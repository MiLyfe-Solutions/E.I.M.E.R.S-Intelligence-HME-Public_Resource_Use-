import V185TrunkScan22Chunk400

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3577119 : List Nat := [1, 1, 2, 4, 5, 1, 2, 1, 5]
def baseStart_3577119 : Nat := 118140960795 + 3577119 * 2 ^ 59
def prefixEnd_3577119 : Nat := 4983230072969 + 3 ^ 40 * 3577119 * 2
def baseEnd_3577119 : Nat := 408173645628998942035919

theorem tailTrace_3577119 : CollatzResearch.WordTrace tailWord_3577119 prefixEnd_3577119 408173645628998942035919 := by
  unfold tailWord_3577119
  simp only [CollatzResearch.WordTrace]
  refine ⟨130468248327716261132222411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86978832218477507421481607 130468248327716261132222411)
  ·
    refine ⟨195702372491574391698333617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130468248327716261132222411 195702372491574391698333617)
    ·
      refine ⟨146776779368680793773750213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195702372491574391698333617 146776779368680793773750213)
      ·
        refine ⟨27520646131627648832578165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146776779368680793773750213 27520646131627648832578165)
        ·
          refine ⟨2580060574840092078054203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27520646131627648832578165 2580060574840092078054203)
          ·
            refine ⟨3870090862260138117081305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580060574840092078054203 3870090862260138117081305)
            ·
              refine ⟨2902568146695103587810979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870090862260138117081305 2902568146695103587810979)
              ·
                refine ⟨4353852220042655381716469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2902568146695103587810979 4353852220042655381716469)
                ·
                  refine ⟨408173645628998942035919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4353852220042655381716469 408173645628998942035919)
                  ·
                    rfl

theorem cell22_3577119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 5].length) (baseStart_3577119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577119 prefixEnd_3577119 := by exact prefixLift 3577119
  have htrace : WordTrace (prefixWord ++ tailWord_3577119) baseStart_3577119 baseEnd_3577119 := by
    simpa [prefixWord, tailWord_3577119, baseEnd_3577119] using wordTrace_append hprefix tailTrace_3577119
  have hstable : (prefixWord ++ tailWord_3577119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577119).length < 2 ^ (prefixWord ++ tailWord_3577119).sum := by decide
  have hdescent : baseEnd_3577119 < baseStart_3577119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577164 : List Nat := [2, 2, 1, 3, 2, 4, 2, 2, 4]
def baseStart_3577164 : Nat := 118140960795 + 3577164 * 2 ^ 59
def prefixEnd_3577164 : Nat := 4983230072969 + 3 ^ 40 * 3577164 * 2
def baseEnd_3577164 : Nat := 408178780435543902910873

theorem tailTrace_3577164 : CollatzResearch.WordTrace tailWord_3577164 prefixEnd_3577164 408178780435543902910873 := by
  unfold tailWord_3577164
  simp only [CollatzResearch.WordTrace]
  refine ⟨65234944806276616908805273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86979926408368822545073697 65234944806276616908805273)
  ·
    refine ⟨48926208604707462681603955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65234944806276616908805273 48926208604707462681603955)
    ·
      refine ⟨73389312907061194022405933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48926208604707462681603955 73389312907061194022405933)
      ·
        refine ⟨27520992340147947758402225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73389312907061194022405933 27520992340147947758402225)
        ·
          refine ⟨20640744255110960818801669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27520992340147947758402225 20640744255110960818801669)
          ·
            refine ⟨3870139547833305153525313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20640744255110960818801669 3870139547833305153525313)
            ·
              refine ⟨2902604660874978865143985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870139547833305153525313 2902604660874978865143985)
              ·
                refine ⟨2176953495656234148857989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902604660874978865143985 2176953495656234148857989)
                ·
                  refine ⟨408178780435543902910873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2176953495656234148857989 408178780435543902910873)
                  ·
                    rfl

theorem cell22_3577164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_3577164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577164 prefixEnd_3577164 := by exact prefixLift 3577164
  have htrace : WordTrace (prefixWord ++ tailWord_3577164) baseStart_3577164 baseEnd_3577164 := by
    simpa [prefixWord, tailWord_3577164, baseEnd_3577164] using wordTrace_append hprefix tailTrace_3577164
  have hstable : (prefixWord ++ tailWord_3577164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577164).length < 2 ^ (prefixWord ++ tailWord_3577164).sum := by decide
  have hdescent : baseEnd_3577164 < baseStart_3577164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577175 : List Nat := [1, 1, 3, 2, 3, 4, 1, 7]
def baseStart_3577175 : Nat := 118140960795 + 3577175 * 2 ^ 59
def prefixEnd_3577175 : Nat := 4983230072969 + 3 ^ 40 * 3577175 * 2
def baseEnd_3577175 : Nat := 136060011870159038523065

theorem tailTrace_3577175 : CollatzResearch.WordTrace tailWord_3577175 prefixEnd_3577175 136060011870159038523065 := by
  unfold tailWord_3577175
  simp only [CollatzResearch.WordTrace]
  refine ⟨130470290815513382696260979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86980193877008921797507319 130470290815513382696260979)
  ·
    refine ⟨195705436223270074044391469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130470290815513382696260979 195705436223270074044391469)
    ·
      refine ⟨73389538583726277766646801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195705436223270074044391469 73389538583726277766646801)
      ·
        refine ⟨55042153937794708324985101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73389538583726277766646801 55042153937794708324985101)
        ·
          refine ⟨20640807726673015621869413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55042153937794708324985101 20640807726673015621869413)
          ·
            refine ⟨3870151448751190429100515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20640807726673015621869413 3870151448751190429100515)
            ·
              refine ⟨5805227173126785643650773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870151448751190429100515 5805227173126785643650773)
              ·
                refine ⟨136060011870159038523065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5805227173126785643650773 136060011870159038523065)
                ·
                  rfl

theorem cell22_3577175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 7].length) (baseStart_3577175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577175 prefixEnd_3577175 := by exact prefixLift 3577175
  have htrace : WordTrace (prefixWord ++ tailWord_3577175) baseStart_3577175 baseEnd_3577175 := by
    simpa [prefixWord, tailWord_3577175, baseEnd_3577175] using wordTrace_append hprefix tailTrace_3577175
  have hstable : (prefixWord ++ tailWord_3577175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577175).length < 2 ^ (prefixWord ++ tailWord_3577175).sum := by decide
  have hdescent : baseEnd_3577175 < baseStart_3577175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577192 : List Nat := [2, 1, 4, 2, 3, 1, 3, 6]
def baseStart_3577192 : Nat := 118140960795 + 3577192 * 2 ^ 59
def prefixEnd_3577192 : Nat := 4983230072969 + 3 ^ 40 * 3577192 * 2
def baseEnd_3577192 : Nat := 136060658475427663225837

theorem tailTrace_3577192 : CollatzResearch.WordTrace tailWord_3577192 prefixEnd_3577192 136060658475427663225837 := by
  unfold tailWord_3577192
  simp only [CollatzResearch.WordTrace]
  refine ⟨65235455428225897299814915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86980607237634529733086553 65235455428225897299814915)
  ·
    refine ⟨97853183142338845949722373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65235455428225897299814915 97853183142338845949722373)
    ·
      refine ⟨18347471839188533615572945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97853183142338845949722373 18347471839188533615572945)
      ·
        refine ⟨13760603879391400211679709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18347471839188533615572945 13760603879391400211679709)
        ·
          refine ⟨5160226454771775079379891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13760603879391400211679709 5160226454771775079379891)
          ·
            refine ⟨7740339682157662619069837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160226454771775079379891 7740339682157662619069837)
            ·
              refine ⟨2902627380809123482151189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7740339682157662619069837 2902627380809123482151189)
              ·
                refine ⟨136060658475427663225837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2902627380809123482151189 136060658475427663225837)
                ·
                  rfl

theorem cell22_3577192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 3, 6].length) (baseStart_3577192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577192 prefixEnd_3577192 := by exact prefixLift 3577192
  have htrace : WordTrace (prefixWord ++ tailWord_3577192) baseStart_3577192 baseEnd_3577192 := by
    simpa [prefixWord, tailWord_3577192, baseEnd_3577192] using wordTrace_append hprefix tailTrace_3577192
  have hstable : (prefixWord ++ tailWord_3577192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577192).length < 2 ^ (prefixWord ++ tailWord_3577192).sum := by decide
  have hdescent : baseEnd_3577192 < baseStart_3577192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577194 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 2, 4]
def baseStart_3577194 : Nat := 118140960795 + 3577194 * 2 ^ 59
def prefixEnd_3577194 : Nat := 4983230072969 + 3 ^ 40 * 3577194 * 2
def baseEnd_3577194 : Nat := 1224546610919721630482527

theorem tailTrace_3577194 : CollatzResearch.WordTrace tailWord_3577194 prefixEnd_3577194 1224546610919721630482527 := by
  unfold tailWord_3577194
  simp only [CollatzResearch.WordTrace]
  refine ⟨32617745950611137235300659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86980655868296365960801757 32617745950611137235300659)
  ·
    refine ⟨48926618925916705852950989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32617745950611137235300659 48926618925916705852950989)
    ·
      refine ⟨18347482097218764694856621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48926618925916705852950989 18347482097218764694856621)
      ·
        refine ⟨6880305786457036760571233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18347482097218764694856621 6880305786457036760571233)
        ·
          refine ⟨5160229339842777570428425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6880305786457036760571233 5160229339842777570428425)
          ·
            refine ⟨3870172004882083177821319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5160229339842777570428425 3870172004882083177821319)
            ·
              refine ⟨5805258007323124766731979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3870172004882083177821319 5805258007323124766731979)
              ·
                refine ⟨8707887010984687150097969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5805258007323124766731979 8707887010984687150097969)
                ·
                  refine ⟨6530915258238515362573477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8707887010984687150097969 6530915258238515362573477)
                  ·
                    refine ⟨1224546610919721630482527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6530915258238515362573477 1224546610919721630482527)
                    ·
                      rfl

theorem cell22_3577194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_3577194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577194 prefixEnd_3577194 := by exact prefixLift 3577194
  have htrace : WordTrace (prefixWord ++ tailWord_3577194) baseStart_3577194 baseEnd_3577194 := by
    simpa [prefixWord, tailWord_3577194, baseEnd_3577194] using wordTrace_append hprefix tailTrace_3577194
  have hstable : (prefixWord ++ tailWord_3577194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577194).length < 2 ^ (prefixWord ++ tailWord_3577194).sum := by decide
  have hdescent : baseEnd_3577194 < baseStart_3577194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577220 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 7]
def baseStart_3577220 : Nat := 118140960795 + 3577220 * 2 ^ 59
def prefixEnd_3577220 : Nat := 4983230072969 + 3 ^ 40 * 3577220 * 2
def baseEnd_3577220 : Nat := 408185170417022076444149

theorem tailTrace_3577220 : CollatzResearch.WordTrace tailWord_3577220 prefixEnd_3577220 408185170417022076444149 := by
  unfold tailWord_3577220
  simp only [CollatzResearch.WordTrace]
  refine ⟨65235966050175177690824557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86981288066900236921099409 65235966050175177690824557)
  ·
    refine ⟨24463487268815691634059209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65235966050175177690824557 24463487268815691634059209)
    ·
      refine ⟨18347615451611768725544407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24463487268815691634059209 18347615451611768725544407)
      ·
        refine ⟨27521423177417653088316611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18347615451611768725544407 27521423177417653088316611)
        ·
          refine ⟨41282134766126479632474917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27521423177417653088316611 41282134766126479632474917)
          ·
            refine ⟨7740400268648714931089047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41282134766126479632474917 7740400268648714931089047)
            ·
              refine ⟨11610600402973072396633571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7740400268648714931089047 11610600402973072396633571)
              ·
                refine ⟨17415900604459608594950357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11610600402973072396633571 17415900604459608594950357)
                ·
                  refine ⟨408185170417022076444149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17415900604459608594950357 408185170417022076444149)
                  ·
                    rfl

theorem cell22_3577220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_3577220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577220 prefixEnd_3577220 := by exact prefixLift 3577220
  have htrace : WordTrace (prefixWord ++ tailWord_3577220) baseStart_3577220 baseEnd_3577220 := by
    simpa [prefixWord, tailWord_3577220, baseEnd_3577220] using wordTrace_append hprefix tailTrace_3577220
  have hstable : (prefixWord ++ tailWord_3577220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577220).length < 2 ^ (prefixWord ++ tailWord_3577220).sum := by decide
  have hdescent : baseEnd_3577220 < baseStart_3577220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577224 : List Nat := [2, 1, 3, 3, 1, 2, 2, 4, 1, 3]
def baseStart_3577224 : Nat := 118140960795 + 3577224 * 2 ^ 59
def prefixEnd_3577224 : Nat := 4983230072969 + 3 ^ 40 * 3577224 * 2
def baseEnd_3577224 : Nat := 1224556880532811552232435

theorem tailTrace_3577224 : CollatzResearch.WordTrace tailWord_3577224 prefixEnd_3577224 1224556880532811552232435 := by
  unfold tailWord_3577224
  simp only [CollatzResearch.WordTrace]
  refine ⟨65236038996167932032397363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86981385328223909376529817 65236038996167932032397363)
  ·
    refine ⟨97854058494251898048596045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65236038996167932032397363 97854058494251898048596045)
    ·
      refine ⟨36695271935344461768223517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97854058494251898048596045 36695271935344461768223517)
      ·
        refine ⟨13760726975754173163083819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36695271935344461768223517 13760726975754173163083819)
        ·
          refine ⟨20641090463631259744625729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13760726975754173163083819 20641090463631259744625729)
          ·
            refine ⟨15480817847723444808469297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20641090463631259744625729 15480817847723444808469297)
            ·
              refine ⟨11610613385792583606351973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15480817847723444808469297 11610613385792583606351973)
              ·
                refine ⟨2176990009836109426190995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11610613385792583606351973 2176990009836109426190995)
                ·
                  refine ⟨3265485014754164139286493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2176990009836109426190995 3265485014754164139286493)
                  ·
                    refine ⟨1224556880532811552232435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3265485014754164139286493 1224556880532811552232435)
                    ·
                      rfl

theorem cell22_3577224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_3577224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577224 prefixEnd_3577224 := by exact prefixLift 3577224
  have htrace : WordTrace (prefixWord ++ tailWord_3577224) baseStart_3577224 baseEnd_3577224 := by
    simpa [prefixWord, tailWord_3577224, baseEnd_3577224] using wordTrace_append hprefix tailTrace_3577224
  have hstable : (prefixWord ++ tailWord_3577224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577224).length < 2 ^ (prefixWord ++ tailWord_3577224).sum := by decide
  have hdescent : baseEnd_3577224 < baseStart_3577224 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577333 : List Nat := [1, 3, 5, 1, 1, 3, 2, 2, 4]
def baseStart_3577333 : Nat := 118140960795 + 3577333 * 2 ^ 59
def prefixEnd_3577333 : Nat := 4983230072969 + 3 ^ 40 * 3577333 * 2
def baseEnd_3577333 : Nat := 408198064486790533752367

theorem tailTrace_3577333 : CollatzResearch.WordTrace tailWord_3577333 prefixEnd_3577333 408198064486790533752367 := by
  unfold tailWord_3577333
  simp only [CollatzResearch.WordTrace]
  refine ⟨130476053548940975680512653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86984035699293983787008435 130476053548940975680512653)
  ·
    refine ⟨48928520080852865880192245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130476053548940975680512653 48928520080852865880192245)
    ·
      refine ⟨4587048757579956176268023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48928520080852865880192245 4587048757579956176268023)
      ·
        refine ⟨6880573136369934264402035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4587048757579956176268023 6880573136369934264402035)
        ·
          refine ⟨10320859704554901396603053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6880573136369934264402035 10320859704554901396603053)
          ·
            refine ⟨3870322389208088023726145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10320859704554901396603053 3870322389208088023726145)
            ·
              refine ⟨2902741791906066017794609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3870322389208088023726145 2902741791906066017794609)
              ·
                refine ⟨2177056343929549513345957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2902741791906066017794609 2177056343929549513345957)
                ·
                  refine ⟨408198064486790533752367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2177056343929549513345957 408198064486790533752367)
                  ·
                    rfl

theorem cell22_3577333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 2, 4].length) (baseStart_3577333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577333 prefixEnd_3577333 := by exact prefixLift 3577333
  have htrace : WordTrace (prefixWord ++ tailWord_3577333) baseStart_3577333 baseEnd_3577333 := by
    simpa [prefixWord, tailWord_3577333, baseEnd_3577333] using wordTrace_append hprefix tailTrace_3577333
  have hstable : (prefixWord ++ tailWord_3577333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577333).length < 2 ^ (prefixWord ++ tailWord_3577333).sum := by decide
  have hdescent : baseEnd_3577333 < baseStart_3577333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577340 : List Nat := [2, 2, 2, 1, 2, 1, 3, 1, 2, 6]
def baseStart_3577340 : Nat := 118140960795 + 3577340 * 2 ^ 59
def prefixEnd_3577340 : Nat := 4983230072969 + 3 ^ 40 * 3577340 * 2
def baseEnd_3577340 : Nat := 1224596589703425916332079

theorem tailTrace_3577340 : CollatzResearch.WordTrace tailWord_3577340 prefixEnd_3577340 1224596589703425916332079 := by
  unfold tailWord_3577340
  simp only [CollatzResearch.WordTrace]
  refine ⟨65238154429957807938008737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86984205906610410584011649 65238154429957807938008737)
  ·
    refine ⟨48928615822468355953506553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65238154429957807938008737 48928615822468355953506553)
    ·
      refine ⟨36696461866851266965129915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48928615822468355953506553 36696461866851266965129915)
      ·
        refine ⟨55044692800276900447694873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36696461866851266965129915 55044692800276900447694873)
        ·
          refine ⟨41283519600207675335771155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55044692800276900447694873 41283519600207675335771155)
          ·
            refine ⟨61925279400311513003656733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41283519600207675335771155 61925279400311513003656733)
            ·
              refine ⟨23221979775116817376371275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61925279400311513003656733 23221979775116817376371275)
              ·
                refine ⟨34832969662675226064556913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23221979775116817376371275 34832969662675226064556913)
                ·
                  refine ⟨26124727247006419548417685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34832969662675226064556913 26124727247006419548417685)
                  ·
                    refine ⟨1224596589703425916332079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26124727247006419548417685 1224596589703425916332079)
                    ·
                      rfl

theorem cell22_3577340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 1, 2, 6].length) (baseStart_3577340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577340 prefixEnd_3577340 := by exact prefixLift 3577340
  have htrace : WordTrace (prefixWord ++ tailWord_3577340) baseStart_3577340 baseEnd_3577340 := by
    simpa [prefixWord, tailWord_3577340, baseEnd_3577340] using wordTrace_append hprefix tailTrace_3577340
  have hstable : (prefixWord ++ tailWord_3577340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577340).length < 2 ^ (prefixWord ++ tailWord_3577340).sum := by decide
  have hdescent : baseEnd_3577340 < baseStart_3577340 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577370 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 3, 7]
def baseStart_3577370 : Nat := 118140960795 + 3577370 * 2 ^ 59
def prefixEnd_3577370 : Nat := 4983230072969 + 3 ^ 40 * 3577370 * 2
def baseEnd_3577370 : Nat := 1224606859316515838081987

theorem tailTrace_3577370 : CollatzResearch.WordTrace tailWord_3577370 prefixEnd_3577370 1224606859316515838081987 := by
  unfold tailWord_3577370
  simp only [CollatzResearch.WordTrace]
  refine ⟨32619350762451732749902391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86984935366537953999739709 32619350762451732749902391)
  ·
    refine ⟨48929026143677599124853587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32619350762451732749902391 48929026143677599124853587)
    ·
      refine ⟨73393539215516398687280381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48929026143677599124853587 73393539215516398687280381)
      ·
        refine ⟨27522577205818649507730143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73393539215516398687280381 27522577205818649507730143)
        ·
          refine ⟨41283865808727974261595215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27522577205818649507730143 41283865808727974261595215)
          ·
            refine ⟨61925798713091961392392823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41283865808727974261595215 61925798713091961392392823)
            ·
              refine ⟨92888698069637942088589235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61925798713091961392392823 92888698069637942088589235)
              ·
                refine ⟨139333047104456913132883853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92888698069637942088589235 139333047104456913132883853)
                ·
                  refine ⟨52249892664171342424831445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139333047104456913132883853 52249892664171342424831445)
                  ·
                    refine ⟨1224606859316515838081987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52249892664171342424831445 1224606859316515838081987)
                    ·
                      rfl

theorem cell22_3577370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_3577370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577370 prefixEnd_3577370 := by exact prefixLift 3577370
  have htrace : WordTrace (prefixWord ++ tailWord_3577370) baseStart_3577370 baseEnd_3577370 := by
    simpa [prefixWord, tailWord_3577370, baseEnd_3577370] using wordTrace_append hprefix tailTrace_3577370
  have hstable : (prefixWord ++ tailWord_3577370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577370).length < 2 ^ (prefixWord ++ tailWord_3577370).sum := by decide
  have hdescent : baseEnd_3577370 < baseStart_3577370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577376 : List Nat := [2, 1, 1, 6, 1, 1, 1, 5, 1, 3]
def baseStart_3577376 : Nat := 118140960795 + 3577376 * 2 ^ 59
def prefixEnd_3577376 : Nat := 4983230072969 + 3 ^ 40 * 3577376 * 2
def baseEnd_3577376 : Nat := 1224608913239133822431969

theorem tailTrace_3577376 : CollatzResearch.WordTrace tailWord_3577376 prefixEnd_3577376 1224608913239133822431969 := by
  unfold tailWord_3577376
  simp only [CollatzResearch.WordTrace]
  refine ⟨65238810943892597012163991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86985081258523462682885321 65238810943892597012163991)
  ·
    refine ⟨97858216415838895518245987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65238810943892597012163991 97858216415838895518245987)
    ·
      refine ⟨146787324623758343277368981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97858216415838895518245987 146787324623758343277368981)
      ·
        refine ⟨6880655841738672341126671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 146787324623758343277368981 6880655841738672341126671)
        ·
          refine ⟨10320983762608008511690007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6880655841738672341126671 10320983762608008511690007)
          ·
            refine ⟨15481475643912012767535011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10320983762608008511690007 15481475643912012767535011)
            ·
              refine ⟨23222213465868019151302517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15481475643912012767535011 23222213465868019151302517)
              ·
                refine ⟨2177082512425126795434611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23222213465868019151302517 2177082512425126795434611)
                ·
                  refine ⟨3265623768637690193151917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2177082512425126795434611 3265623768637690193151917)
                  ·
                    refine ⟨1224608913239133822431969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3265623768637690193151917 1224608913239133822431969)
                    ·
                      rfl

theorem cell22_3577376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 5, 1, 3].length) (baseStart_3577376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577376 prefixEnd_3577376 := by exact prefixLift 3577376
  have htrace : WordTrace (prefixWord ++ tailWord_3577376) baseStart_3577376 baseEnd_3577376 := by
    simpa [prefixWord, tailWord_3577376, baseEnd_3577376] using wordTrace_append hprefix tailTrace_3577376
  have hstable : (prefixWord ++ tailWord_3577376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577376).length < 2 ^ (prefixWord ++ tailWord_3577376).sum := by decide
  have hdescent : baseEnd_3577376 < baseStart_3577376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577447 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 4, 4]
def baseStart_3577447 : Nat := 118140960795 + 3577447 * 2 ^ 59
def prefixEnd_3577447 : Nat := 4983230072969 + 3 ^ 40 * 3577447 * 2
def baseEnd_3577447 : Nat := 1224633217990113303906751

theorem tailTrace_3577447 : CollatzResearch.WordTrace tailWord_3577447 prefixEnd_3577447 1224633217990113303906751 := by
  unfold tailWord_3577447
  simp only [CollatzResearch.WordTrace]
  refine ⟨130480211470527973150162595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86986807647018648766775063 130480211470527973150162595)
  ·
    refine ⟨195720317205791959725243893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130480211470527973150162595 195720317205791959725243893)
    ·
      refine ⟨18348779738042996224241615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195720317205791959725243893 18348779738042996224241615)
      ·
        refine ⟨27523169607064494336362423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18348779738042996224241615 27523169607064494336362423)
        ·
          refine ⟨41284754410596741504543635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27523169607064494336362423 41284754410596741504543635)
          ·
            refine ⟨61927131615895112256815453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41284754410596741504543635 61927131615895112256815453)
            ·
              refine ⟨23222674355960667096305795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61927131615895112256815453 23222674355960667096305795)
              ·
                refine ⟨34834011533941000644458693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23222674355960667096305795 34834011533941000644458693)
                ·
                  refine ⟨6531377162613937620836005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34834011533941000644458693 6531377162613937620836005)
                  ·
                    refine ⟨1224633217990113303906751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6531377162613937620836005 1224633217990113303906751)
                    ·
                      rfl

theorem cell22_3577447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_3577447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577447 prefixEnd_3577447 := by exact prefixLift 3577447
  have htrace : WordTrace (prefixWord ++ tailWord_3577447) baseStart_3577447 baseEnd_3577447 := by
    simpa [prefixWord, tailWord_3577447, baseEnd_3577447] using wordTrace_append hprefix tailTrace_3577447
  have hstable : (prefixWord ++ tailWord_3577447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577447).length < 2 ^ (prefixWord ++ tailWord_3577447).sum := by decide
  have hdescent : baseEnd_3577447 < baseStart_3577447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577522 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 1, 7]
def baseStart_3577522 : Nat := 118140960795 + 3577522 * 2 ^ 59
def prefixEnd_3577522 : Nat := 4983230072969 + 3 ^ 40 * 3577522 * 2
def baseEnd_3577522 : Nat := 1224658892022838108281521

theorem tailTrace_3577522 : CollatzResearch.WordTrace tailWord_3577522 prefixEnd_3577522 1224658892022838108281521 := by
  unfold tailWord_3577522
  simp only [CollatzResearch.WordTrace]
  refine ⟨32620736736314065239785705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86988631296837507306095213 32620736736314065239785705)
  ·
    refine ⟨24465552552235548929839279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32620736736314065239785705 24465552552235548929839279)
    ·
      refine ⟨36698328828353323394758919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24465552552235548929839279 36698328828353323394758919)
      ·
        refine ⟨55047493242529985092138379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36698328828353323394758919 55047493242529985092138379)
        ·
          refine ⟨82571239863794977638207569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55047493242529985092138379 82571239863794977638207569)
          ·
            refine ⟨61928429897846233228655677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82571239863794977638207569 61928429897846233228655677)
            ·
              refine ⟨23223161211692337460745879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61928429897846233228655677 23223161211692337460745879)
              ·
                refine ⟨34834741817538506191118819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23223161211692337460745879 34834741817538506191118819)
                ·
                  refine ⟨52252112726307759286678229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34834741817538506191118819 52252112726307759286678229)
                  ·
                    refine ⟨1224658892022838108281521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52252112726307759286678229 1224658892022838108281521)
                    ·
                      rfl

theorem cell22_3577522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 1, 7].length) (baseStart_3577522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577522 prefixEnd_3577522 := by exact prefixLift 3577522
  have htrace : WordTrace (prefixWord ++ tailWord_3577522) baseStart_3577522 baseEnd_3577522 := by
    simpa [prefixWord, tailWord_3577522, baseEnd_3577522] using wordTrace_append hprefix tailTrace_3577522
  have hstable : (prefixWord ++ tailWord_3577522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577522).length < 2 ^ (prefixWord ++ tailWord_3577522).sum := by decide
  have hdescent : baseEnd_3577522 < baseStart_3577522 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577558 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3577558 : Nat := 118140960795 + 3577558 * 2 ^ 59
def prefixEnd_3577558 : Nat := 4983230072969 + 3 ^ 40 * 3577558 * 2
def baseEnd_3577558 : Nat := 408223738519515338127137

theorem tailTrace_3577558 : CollatzResearch.WordTrace tailWord_3577558 prefixEnd_3577558 408223738519515338127137 := by
  unfold tailWord_3577558
  simp only [CollatzResearch.WordTrace]
  refine ⟨8155266248320364944215833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 86989506648750559404968885 8155266248320364944215833)
  ·
    refine ⟨6116449686240273708161875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8155266248320364944215833 6116449686240273708161875)
    ·
      refine ⟨9174674529360410562242813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6116449686240273708161875 9174674529360410562242813)
      ·
        refine ⟨3440502948510153960841055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9174674529360410562242813 3440502948510153960841055)
        ·
          refine ⟨5160754422765230941261583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3440502948510153960841055 5160754422765230941261583)
          ·
            refine ⟨7741131634147846411892375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5160754422765230941261583 7741131634147846411892375)
            ·
              refine ⟨11611697451221769617838563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7741131634147846411892375 11611697451221769617838563)
              ·
                refine ⟨17417546176832654426757845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11611697451221769617838563 17417546176832654426757845)
                ·
                  refine ⟨408223738519515338127137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17417546176832654426757845 408223738519515338127137)
                  ·
                    rfl

theorem cell22_3577558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3577558 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577558 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577558 prefixEnd_3577558 := by exact prefixLift 3577558
  have htrace : WordTrace (prefixWord ++ tailWord_3577558) baseStart_3577558 baseEnd_3577558 := by
    simpa [prefixWord, tailWord_3577558, baseEnd_3577558] using wordTrace_append hprefix tailTrace_3577558
  have hstable : (prefixWord ++ tailWord_3577558).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577558).length < 2 ^ (prefixWord ++ tailWord_3577558).sum := by decide
  have hdescent : baseEnd_3577558 < baseStart_3577558 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577618 : List Nat := [3, 2, 4, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3577618 : Nat := 118140960795 + 3577618 * 2 ^ 59
def prefixEnd_3577618 : Nat := 4983230072969 + 3 ^ 40 * 3577618 * 2
def baseEnd_3577618 : Nat := 1224691754784725857881227

theorem tailTrace_3577618 : CollatzResearch.WordTrace tailWord_3577618 prefixEnd_3577618 1224691754784725857881227 := by
  unfold tailWord_3577618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32621612088227117338659377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86990965568605646236425005 32621612088227117338659377)
  ·
    refine ⟨24466209066170338003994533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32621612088227117338659377 24466209066170338003994533)
    ·
      refine ⟨4587414199906938375748975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24466209066170338003994533 4587414199906938375748975)
      ·
        refine ⟨6881121299860407563623463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4587414199906938375748975 6881121299860407563623463)
        ·
          refine ⟨10321681949790611345435195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6881121299860407563623463 10321681949790611345435195)
          ·
            refine ⟨15482522924685917018152793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10321681949790611345435195 15482522924685917018152793)
            ·
              refine ⟨11611892193514437763614595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15482522924685917018152793 11611892193514437763614595)
              ·
                refine ⟨17417838290271656645421893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11611892193514437763614595 17417838290271656645421893)
                ·
                  refine ⟨3265844679425935621016605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17417838290271656645421893 3265844679425935621016605)
                  ·
                    refine ⟨1224691754784725857881227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3265844679425935621016605 1224691754784725857881227)
                    ·
                      rfl

theorem cell22_3577618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3577618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577618 prefixEnd_3577618 := by exact prefixLift 3577618
  have htrace : WordTrace (prefixWord ++ tailWord_3577618) baseStart_3577618 baseEnd_3577618 := by
    simpa [prefixWord, tailWord_3577618, baseEnd_3577618] using wordTrace_append hprefix tailTrace_3577618
  have hstable : (prefixWord ++ tailWord_3577618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577618).length < 2 ^ (prefixWord ++ tailWord_3577618).sum := by decide
  have hdescent : baseEnd_3577618 < baseStart_3577618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577627 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 1, 8]
def baseStart_3577627 : Nat := 118140960795 + 3577627 * 2 ^ 59
def prefixEnd_3577627 : Nat := 4983230072969 + 3 ^ 40 * 3577627 * 2
def baseEnd_3577627 : Nat := 1224694835668652834406199

theorem tailTrace_3577627 : CollatzResearch.WordTrace tailWord_3577627 prefixEnd_3577627 1224694835668652834406199 := by
  unfold tailWord_3577627
  simp only [CollatzResearch.WordTrace]
  refine ⟨130486776609875863891715135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86991184406583909261143423 130486776609875863891715135)
  ·
    refine ⟨195730164914813795837572703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130486776609875863891715135 195730164914813795837572703)
    ·
      refine ⟨293595247372220693756359055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195730164914813795837572703 293595247372220693756359055)
      ·
        refine ⟨440392871058331040634538583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293595247372220693756359055 440392871058331040634538583)
        ·
          refine ⟨660589306587496560951807875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440392871058331040634538583 660589306587496560951807875)
          ·
            refine ⟨990883959881244841427711813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 660589306587496560951807875 990883959881244841427711813)
            ·
              refine ⟨185790742477733407767695965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 990883959881244841427711813 185790742477733407767695965)
              ·
                refine ⟨69671528429150027912885987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185790742477733407767695965 69671528429150027912885987)
                ·
                  refine ⟨104507292643725041869328981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69671528429150027912885987 104507292643725041869328981)
                  ·
                    refine ⟨1224694835668652834406199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104507292643725041869328981 1224694835668652834406199)
                    ·
                      rfl

theorem cell22_3577627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 8].length) (baseStart_3577627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577627 prefixEnd_3577627 := by exact prefixLift 3577627
  have htrace : WordTrace (prefixWord ++ tailWord_3577627) baseStart_3577627 baseEnd_3577627 := by
    simpa [prefixWord, tailWord_3577627, baseEnd_3577627] using wordTrace_append hprefix tailTrace_3577627
  have hstable : (prefixWord ++ tailWord_3577627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577627).length < 2 ^ (prefixWord ++ tailWord_3577627).sum := by decide
  have hdescent : baseEnd_3577627 < baseStart_3577627 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577674 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 2, 5]
def baseStart_3577674 : Nat := 118140960795 + 3577674 * 2 ^ 59
def prefixEnd_3577674 : Nat := 4983230072969 + 3 ^ 40 * 3577674 * 2
def baseEnd_3577674 : Nat := 1224710924729160378481055

theorem tailTrace_3577674 : CollatzResearch.WordTrace tailWord_3577674 prefixEnd_3577674 1224710924729160378481055 := by
  unfold tailWord_3577674
  simp only [CollatzResearch.WordTrace]
  refine ⟨32622122710176397729669019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86992327227137060612450717 32622122710176397729669019)
  ·
    refine ⟨48933184065264596594503529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32622122710176397729669019 48933184065264596594503529)
    ·
      refine ⟨36699888048948447445877647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48933184065264596594503529 36699888048948447445877647)
      ·
        refine ⟨55049832073422671168816471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36699888048948447445877647 55049832073422671168816471)
        ·
          refine ⟨82574748110134006753224707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55049832073422671168816471 82574748110134006753224707)
          ·
            refine ⟨123862122165201010129837061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82574748110134006753224707 123862122165201010129837061)
            ·
              refine ⟨23224147905975189399344449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123862122165201010129837061 23224147905975189399344449)
              ·
                refine ⟨17418110929481392049508337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23224147905975189399344449 17418110929481392049508337)
                ·
                  refine ⟨13063583197111044037131253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17418110929481392049508337 13063583197111044037131253)
                  ·
                    refine ⟨1224710924729160378481055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13063583197111044037131253 1224710924729160378481055)
                    ·
                      rfl

theorem cell22_3577674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_3577674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577674 prefixEnd_3577674 := by exact prefixLift 3577674
  have htrace : WordTrace (prefixWord ++ tailWord_3577674) baseStart_3577674 baseEnd_3577674 := by
    simpa [prefixWord, tailWord_3577674, baseEnd_3577674] using wordTrace_append hprefix tailTrace_3577674
  have hstable : (prefixWord ++ tailWord_3577674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577674).length < 2 ^ (prefixWord ++ tailWord_3577674).sum := by decide
  have hdescent : baseEnd_3577674 < baseStart_3577674 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577689 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 5, 4]
def baseStart_3577689 : Nat := 118140960795 + 3577689 * 2 ^ 59
def prefixEnd_3577689 : Nat := 4983230072969 + 3 ^ 40 * 3577689 * 2
def baseEnd_3577689 : Nat := 1224716059535705339356009

theorem tailTrace_3577689 : CollatzResearch.WordTrace tailWord_3577689 prefixEnd_3577689 1224716059535705339356009 := by
  unfold tailWord_3577689
  simp only [CollatzResearch.WordTrace]
  refine ⟨130489037935651248480472121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86992691957100832320314747 130489037935651248480472121)
  ·
    refine ⟨97866778451738436360354091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130489037935651248480472121 97866778451738436360354091)
    ·
      refine ⟨146800167677607654540531137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97866778451738436360354091 146800167677607654540531137)
      ·
        refine ⟨110100125758205740905398353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146800167677607654540531137 110100125758205740905398353)
        ·
          refine ⟨82575094318654305679048765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110100125758205740905398353 82575094318654305679048765)
          ·
            refine ⟨30965660369495364629643287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82575094318654305679048765 30965660369495364629643287)
            ·
              refine ⟨46448490554243046944464931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30965660369495364629643287 46448490554243046944464931)
              ·
                refine ⟨69672735831364570416697397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46448490554243046944464931 69672735831364570416697397)
                ·
                  refine ⟨6531818984190428476565381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69672735831364570416697397 6531818984190428476565381)
                  ·
                    refine ⟨1224716059535705339356009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6531818984190428476565381 1224716059535705339356009)
                    ·
                      rfl

theorem cell22_3577689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 5, 4].length) (baseStart_3577689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577689 prefixEnd_3577689 := by exact prefixLift 3577689
  have htrace : WordTrace (prefixWord ++ tailWord_3577689) baseStart_3577689 baseEnd_3577689 := by
    simpa [prefixWord, tailWord_3577689, baseEnd_3577689] using wordTrace_append hprefix tailTrace_3577689
  have hstable : (prefixWord ++ tailWord_3577689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577689).length < 2 ^ (prefixWord ++ tailWord_3577689).sum := by decide
  have hdescent : baseEnd_3577689 < baseStart_3577689 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577738 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 6]
def baseStart_3577738 : Nat := 118140960795 + 3577738 * 2 ^ 59
def prefixEnd_3577738 : Nat := 4983230072969 + 3 ^ 40 * 3577738 * 2
def baseEnd_3577738 : Nat := 408244277745695181626953

theorem tailTrace_3577738 : CollatzResearch.WordTrace tailWord_3577738 prefixEnd_3577738 408244277745695181626953 := by
  unfold tailWord_3577738
  simp only [CollatzResearch.WordTrace]
  refine ⟨32622706278118432462251467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86993883408315819899337245 32622706278118432462251467)
  ·
    refine ⟨48934059417177648693377201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32622706278118432462251467 48934059417177648693377201)
    ·
      refine ⟨36700544562883236520032901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48934059417177648693377201 36700544562883236520032901)
      ·
        refine ⟨6881352105540606847506169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36700544562883236520032901 6881352105540606847506169)
        ·
          refine ⟨5161014079155455135629627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6881352105540606847506169 5161014079155455135629627)
          ·
            refine ⟨7741521118733182703444441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5161014079155455135629627 7741521118733182703444441)
            ·
              refine ⟨5806140839049887027583331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7741521118733182703444441 5806140839049887027583331)
              ·
                refine ⟨8709211258574830541374997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5806140839049887027583331 8709211258574830541374997)
                ·
                  refine ⟨408244277745695181626953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8709211258574830541374997 408244277745695181626953)
                  ·
                    rfl

theorem cell22_3577738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 6].length) (baseStart_3577738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577738 prefixEnd_3577738 := by exact prefixLift 3577738
  have htrace : WordTrace (prefixWord ++ tailWord_3577738) baseStart_3577738 baseEnd_3577738 := by
    simpa [prefixWord, tailWord_3577738, baseEnd_3577738] using wordTrace_append hprefix tailTrace_3577738
  have hstable : (prefixWord ++ tailWord_3577738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577738).length < 2 ^ (prefixWord ++ tailWord_3577738).sum := by decide
  have hdescent : baseEnd_3577738 < baseStart_3577738 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577749 : List Nat := [1, 3, 2, 1, 1, 3, 2, 9]
def baseStart_3577749 : Nat := 118140960795 + 3577749 * 2 ^ 59
def prefixEnd_3577749 : Nat := 4983230072969 + 3 ^ 40 * 3577749 * 2
def baseEnd_3577749 : Nat := 136081844306876131428425

theorem tailTrace_3577749 : CollatzResearch.WordTrace tailWord_3577749 prefixEnd_3577749 136081844306876131428425 := by
  unfold tailWord_3577749
  simp only [CollatzResearch.WordTrace]
  refine ⟨130491226315433878727656301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86994150876955919151770867 130491226315433878727656301)
  ·
    refine ⟨48934209868287704522871113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130491226315433878727656301 48934209868287704522871113)
    ·
      refine ⟨36700657401215778392153335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48934209868287704522871113 36700657401215778392153335)
      ·
        refine ⟨55050986101823667588230003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36700657401215778392153335 55050986101823667588230003)
        ·
          refine ⟨82576479152735501382345005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55050986101823667588230003 82576479152735501382345005)
          ·
            refine ⟨30966179682275813018379377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82576479152735501382345005 30966179682275813018379377)
            ·
              refine ⟨23224634761706859763784533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30966179682275813018379377 23224634761706859763784533)
              ·
                refine ⟨136081844306876131428425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23224634761706859763784533 136081844306876131428425)
                ·
                  rfl

theorem cell22_3577749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 9].length) (baseStart_3577749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577749 prefixEnd_3577749 := by exact prefixLift 3577749
  have htrace : WordTrace (prefixWord ++ tailWord_3577749) baseStart_3577749 baseEnd_3577749 := by
    simpa [prefixWord, tailWord_3577749, baseEnd_3577749] using wordTrace_append hprefix tailTrace_3577749
  have hstable : (prefixWord ++ tailWord_3577749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577749).length < 2 ^ (prefixWord ++ tailWord_3577749).sum := by decide
  have hdescent : baseEnd_3577749 < baseStart_3577749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577860 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_3577860 : Nat := 118140960795 + 3577860 * 2 ^ 59
def prefixEnd_3577860 : Nat := 4983230072969 + 3 ^ 40 * 3577860 * 2
def baseEnd_3577860 : Nat := 1224774596330317893330485

theorem tailTrace_3577860 : CollatzResearch.WordTrace tailWord_3577860 prefixEnd_3577860 1224774596330317893330485 := by
  unfold tailWord_3577860
  simp only [CollatzResearch.WordTrace]
  refine ⟨65247637409015872342473517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86996849878687829789964689 65247637409015872342473517)
  ·
    refine ⟨24467864028380952128427569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65247637409015872342473517 24467864028380952128427569)
    ·
      refine ⟨18350898021285714096320677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24467864028380952128427569 18350898021285714096320677)
      ·
        refine ⟨3440793378991071393060127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18350898021285714096320677 3440793378991071393060127)
        ·
          refine ⟨5161190068486607089590191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3440793378991071393060127 5161190068486607089590191)
          ·
            refine ⟨7741785102729910634385287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5161190068486607089590191 7741785102729910634385287)
            ·
              refine ⟨11612677654094865951577931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7741785102729910634385287 11612677654094865951577931)
              ·
                refine ⟨17419016481142298927366897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11612677654094865951577931 17419016481142298927366897)
                ·
                  refine ⟨13064262360856724195525173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17419016481142298927366897 13064262360856724195525173)
                  ·
                    refine ⟨1224774596330317893330485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13064262360856724195525173 1224774596330317893330485)
                    ·
                      rfl

theorem cell22_3577860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_3577860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577860 prefixEnd_3577860 := by exact prefixLift 3577860
  have htrace : WordTrace (prefixWord ++ tailWord_3577860) baseStart_3577860 baseEnd_3577860 := by
    simpa [prefixWord, tailWord_3577860, baseEnd_3577860] using wordTrace_append hprefix tailTrace_3577860
  have hstable : (prefixWord ++ tailWord_3577860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577860).length < 2 ^ (prefixWord ++ tailWord_3577860).sum := by decide
  have hdescent : baseEnd_3577860 < baseStart_3577860 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577890 : List Nat := [3, 3, 1, 1, 1, 2, 4, 3, 4]
def baseStart_3577890 : Nat := 118140960795 + 3577890 * 2 ^ 59
def prefixEnd_3577890 : Nat := 4983230072969 + 3 ^ 40 * 3577890 * 2
def baseEnd_3577890 : Nat := 408261621981135938360131

theorem tailTrace_3577890 : CollatzResearch.WordTrace tailWord_3577890 prefixEnd_3577890 408261621981135938360131 := by
  unfold tailWord_3577890
  simp only [CollatzResearch.WordTrace]
  refine ⟨32624092251980764952134781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86997579338615373205692749 32624092251980764952134781)
  ·
    refine ⟨12234034594492786857050543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32624092251980764952134781 12234034594492786857050543)
    ·
      refine ⟨18351051891739180285575815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12234034594492786857050543 18351051891739180285575815)
      ·
        refine ⟨27526577837608770428363723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18351051891739180285575815 27526577837608770428363723)
        ·
          refine ⟨41289866756413155642545585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27526577837608770428363723 41289866756413155642545585)
          ·
            refine ⟨30967400067309866731909189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41289866756413155642545585 30967400067309866731909189)
            ·
              refine ⟨5806387512620600012232973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30967400067309866731909189 5806387512620600012232973)
              ·
                refine ⟨2177395317232725004587365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5806387512620600012232973 2177395317232725004587365)
                ·
                  refine ⟨408261621981135938360131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2177395317232725004587365 408261621981135938360131)
                  ·
                    rfl

theorem cell22_3577890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 3, 4].length) (baseStart_3577890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577890 prefixEnd_3577890 := by exact prefixLift 3577890
  have htrace : WordTrace (prefixWord ++ tailWord_3577890) baseStart_3577890 baseEnd_3577890 := by
    simpa [prefixWord, tailWord_3577890, baseEnd_3577890] using wordTrace_append hprefix tailTrace_3577890
  have hstable : (prefixWord ++ tailWord_3577890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577890).length < 2 ^ (prefixWord ++ tailWord_3577890).sum := by decide
  have hdescent : baseEnd_3577890 < baseStart_3577890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577905 : List Nat := [1, 2, 2, 3, 1, 3, 3, 2, 2, 3]
def baseStart_3577905 : Nat := 118140960795 + 3577905 * 2 ^ 59
def prefixEnd_3577905 : Nat := 4983230072969 + 3 ^ 40 * 3577905 * 2
def baseEnd_3577905 : Nat := 1224790000749952775955347

theorem tailTrace_3577905 : CollatzResearch.WordTrace tailWord_3577905 prefixEnd_3577905 1224790000749952775955347 := by
  unfold tailWord_3577905
  simp only [CollatzResearch.WordTrace]
  refine ⟨130496916102868717370335169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86997944068579144913556779 130496916102868717370335169)
  ·
    refine ⟨97872687077151538027751377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130496916102868717370335169 97872687077151538027751377)
    ·
      refine ⟨73404515307863653520813533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97872687077151538027751377 73404515307863653520813533)
      ·
        refine ⟨27526693240448870070305075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73404515307863653520813533 27526693240448870070305075)
        ·
          refine ⟨41290039860673305105457613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27526693240448870070305075 41290039860673305105457613)
          ·
            refine ⟨15483764947752489414546605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41290039860673305105457613 15483764947752489414546605)
            ·
              refine ⟨5806411855407183530454977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15483764947752489414546605 5806411855407183530454977)
              ·
                refine ⟨4354808891555387647841233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5806411855407183530454977 4354808891555387647841233)
                ·
                  refine ⟨3266106668666540735880925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4354808891555387647841233 3266106668666540735880925)
                  ·
                    refine ⟨1224790000749952775955347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3266106668666540735880925 1224790000749952775955347)
                    ·
                      rfl

theorem cell22_3577905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 2, 2, 3].length) (baseStart_3577905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577905 prefixEnd_3577905 := by exact prefixLift 3577905
  have htrace : WordTrace (prefixWord ++ tailWord_3577905) baseStart_3577905 baseEnd_3577905 := by
    simpa [prefixWord, tailWord_3577905, baseEnd_3577905] using wordTrace_append hprefix tailTrace_3577905
  have hstable : (prefixWord ++ tailWord_3577905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577905).length < 2 ^ (prefixWord ++ tailWord_3577905).sum := by decide
  have hdescent : baseEnd_3577905 < baseStart_3577905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577933 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_3577933 : Nat := 118140960795 + 3577933 * 2 ^ 59
def prefixEnd_3577933 : Nat := 4983230072969 + 3 ^ 40 * 3577933 * 2
def baseEnd_3577933 : Nat := 1224799585722170036255261

theorem tailTrace_3577933 : CollatzResearch.WordTrace tailWord_3577933 prefixEnd_3577933 1224799585722170036255261 := by
  unfold tailWord_3577933
  simp only [CollatzResearch.WordTrace]
  refine ⟨130497937346767278152354453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 86998624897844852101569635 130497937346767278152354453)
  ·
    refine ⟨6117090813129716163391615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 130497937346767278152354453 6117090813129716163391615)
    ·
      refine ⟨9175636219694574245087423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6117090813129716163391615 9175636219694574245087423)
      ·
        refine ⟨13763454329541861367631135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9175636219694574245087423 13763454329541861367631135)
        ·
          refine ⟨20645181494312792051446703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13763454329541861367631135 20645181494312792051446703)
          ·
            refine ⟨30967772241469188077170055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20645181494312792051446703 30967772241469188077170055)
            ·
              refine ⟨46451658362203782115755083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30967772241469188077170055 46451658362203782115755083)
              ·
                refine ⟨69677487543305673173632625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46451658362203782115755083 69677487543305673173632625)
                ·
                  refine ⟨52258115657479254880224469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69677487543305673173632625 52258115657479254880224469)
                  ·
                    refine ⟨1224799585722170036255261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52258115657479254880224469 1224799585722170036255261)
                    ·
                      rfl

theorem cell22_3577933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_3577933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577933 prefixEnd_3577933 := by exact prefixLift 3577933
  have htrace : WordTrace (prefixWord ++ tailWord_3577933) baseStart_3577933 baseEnd_3577933 := by
    simpa [prefixWord, tailWord_3577933, baseEnd_3577933] using wordTrace_append hprefix tailTrace_3577933
  have hstable : (prefixWord ++ tailWord_3577933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577933).length < 2 ^ (prefixWord ++ tailWord_3577933).sum := by decide
  have hdescent : baseEnd_3577933 < baseStart_3577933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577946 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 9]
def baseStart_3577946 : Nat := 118140960795 + 3577946 * 2 ^ 59
def prefixEnd_3577946 : Nat := 4983230072969 + 3 ^ 40 * 3577946 * 2
def baseEnd_3577946 : Nat := 408268011962614111893407

theorem tailTrace_3577946 : CollatzResearch.WordTrace tailWord_3577946 prefixEnd_3577946 408268011962614111893407 := by
  unfold tailWord_3577946
  simp only [CollatzResearch.WordTrace]
  refine ⟨32624602873930045343144423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 86998940997146787581718461 32624602873930045343144423)
  ·
    refine ⟨48936904310895068014716635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32624602873930045343144423 48936904310895068014716635)
    ·
      refine ⟨73405356466342602022074953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48936904310895068014716635 73405356466342602022074953)
      ·
        refine ⟨55054017349756951516556215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73405356466342602022074953 55054017349756951516556215)
        ·
          refine ⟨82581026024635427274834323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55054017349756951516556215 82581026024635427274834323)
          ·
            refine ⟨123871539036953140912251485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82581026024635427274834323 123871539036953140912251485)
            ·
              refine ⟨46451827138857427842094307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123871539036953140912251485 46451827138857427842094307)
              ·
                refine ⟨69677740708286141763141461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46451827138857427842094307 69677740708286141763141461)
                ·
                  refine ⟨408268011962614111893407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69677740708286141763141461 408268011962614111893407)
                  ·
                    rfl

theorem cell22_3577946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_3577946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577946 prefixEnd_3577946 := by exact prefixLift 3577946
  have htrace : WordTrace (prefixWord ++ tailWord_3577946) baseStart_3577946 baseEnd_3577946 := by
    simpa [prefixWord, tailWord_3577946, baseEnd_3577946] using wordTrace_append hprefix tailTrace_3577946
  have hstable : (prefixWord ++ tailWord_3577946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577946).length < 2 ^ (prefixWord ++ tailWord_3577946).sum := by decide
  have hdescent : baseEnd_3577946 < baseStart_3577946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577976 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 2, 8]
def baseStart_3577976 : Nat := 118140960795 + 3577976 * 2 ^ 59
def prefixEnd_3577976 : Nat := 4983230072969 + 3 ^ 40 * 3577976 * 2
def baseEnd_3577976 : Nat := 1224814305500932257430129

theorem tailTrace_3577976 : CollatzResearch.WordTrace tailWord_3577976 prefixEnd_3577976 1224814305500932257430129 := by
  unfold tailWord_3577976
  simp only [CollatzResearch.WordTrace]
  refine ⟨65249752842805748248084891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86999670457074330997446521 65249752842805748248084891)
  ·
    refine ⟨97874629264208622372127337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65249752842805748248084891 97874629264208622372127337)
    ·
      refine ⟨73405971948156466779095503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97874629264208622372127337 73405971948156466779095503)
      ·
        refine ⟨110108957922234700168643255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73405971948156466779095503 110108957922234700168643255)
        ·
          refine ⟨165163436883352050252964883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110108957922234700168643255 165163436883352050252964883)
          ·
            refine ⟨247745155325028075379447325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165163436883352050252964883 247745155325028075379447325)
            ·
              refine ⟨92904433246885528267292747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 247745155325028075379447325 92904433246885528267292747)
              ·
                refine ⟨139356649870328292400939121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92904433246885528267292747 139356649870328292400939121)
                ·
                  refine ⟨104517487402746219300704341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139356649870328292400939121 104517487402746219300704341)
                  ·
                    refine ⟨1224814305500932257430129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104517487402746219300704341 1224814305500932257430129)
                    ·
                      rfl

theorem cell22_3577976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_3577976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577976 prefixEnd_3577976 := by exact prefixLift 3577976
  have htrace : WordTrace (prefixWord ++ tailWord_3577976) baseStart_3577976 baseEnd_3577976 := by
    simpa [prefixWord, tailWord_3577976, baseEnd_3577976] using wordTrace_append hprefix tailTrace_3577976
  have hstable : (prefixWord ++ tailWord_3577976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577976).length < 2 ^ (prefixWord ++ tailWord_3577976).sum := by decide
  have hdescent : baseEnd_3577976 < baseStart_3577976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577980 : List Nat := [2, 2, 2, 1, 1, 4, 4, 1, 5]
def baseStart_3577980 : Nat := 118140960795 + 3577980 * 2 ^ 59
def prefixEnd_3577980 : Nat := 4983230072969 + 3 ^ 40 * 3577980 * 2
def baseEnd_3577980 : Nat := 408271891594225860110039

theorem tailTrace_3577980 : CollatzResearch.WordTrace tailWord_3577980 prefixEnd_3577980 408271891594225860110039 := by
  unfold tailWord_3577980
  simp only [CollatzResearch.WordTrace]
  refine ⟨65249825788798502589657697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 86999767718398003452876929 65249825788798502589657697)
  ·
    refine ⟨48937369341598876942243273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65249825788798502589657697 48937369341598876942243273)
    ·
      refine ⟨36703027006199157706682455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48937369341598876942243273 36703027006199157706682455)
      ·
        refine ⟨55054540509298736560023683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36703027006199157706682455 55054540509298736560023683)
        ·
          refine ⟨82581810763948104840035525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55054540509298736560023683 82581810763948104840035525)
          ·
            refine ⟨15484089518240269657506661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82581810763948104840035525 15484089518240269657506661)
            ·
              refine ⟨2903266784670050560782499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15484089518240269657506661 2903266784670050560782499)
              ·
                refine ⟨4354900177005075841173749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903266784670050560782499 4354900177005075841173749)
                ·
                  refine ⟨408271891594225860110039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4354900177005075841173749 408271891594225860110039)
                  ·
                    rfl

theorem cell22_3577980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 5].length) (baseStart_3577980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577980 prefixEnd_3577980 := by exact prefixLift 3577980
  have htrace : WordTrace (prefixWord ++ tailWord_3577980) baseStart_3577980 baseEnd_3577980 := by
    simpa [prefixWord, tailWord_3577980, baseEnd_3577980] using wordTrace_append hprefix tailTrace_3577980
  have hstable : (prefixWord ++ tailWord_3577980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577980).length < 2 ^ (prefixWord ++ tailWord_3577980).sum := by decide
  have hdescent : baseEnd_3577980 < baseStart_3577980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3577993 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 3, 4]
def baseStart_3577993 : Nat := 118140960795 + 3577993 * 2 ^ 59
def prefixEnd_3577993 : Nat := 4983230072969 + 3 ^ 40 * 3577993 * 2
def baseEnd_3577993 : Nat := 1224820124948349879755077

theorem tailTrace_3577993 : CollatzResearch.WordTrace tailWord_3577993 prefixEnd_3577993 1224820124948349879755077 := by
  unfold tailWord_3577993
  simp only [CollatzResearch.WordTrace]
  refine ⟨130500125726549908399538633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87000083817699938933025755 130500125726549908399538633)
  ·
    refine ⟨97875094294912431299653975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130500125726549908399538633 97875094294912431299653975)
    ·
      refine ⟨146812641442368646949480963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97875094294912431299653975 146812641442368646949480963)
      ·
        refine ⟨220218962163552970424221445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146812641442368646949480963 220218962163552970424221445)
        ·
          refine ⟨41291055405666181954541521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220218962163552970424221445 41291055405666181954541521)
          ·
            refine ⟨30968291554249636465906141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41291055405666181954541521 30968291554249636465906141)
            ·
              refine ⟨11613109332843613674714803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30968291554249636465906141 11613109332843613674714803)
              ·
                refine ⟨17419663999265420512072205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11613109332843613674714803 17419663999265420512072205)
                ·
                  refine ⟨6532373999724532692027077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17419663999265420512072205 6532373999724532692027077)
                  ·
                    refine ⟨1224820124948349879755077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6532373999724532692027077 1224820124948349879755077)
                    ·
                      rfl

theorem cell22_3577993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 3, 4].length) (baseStart_3577993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3577993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3577993 prefixEnd_3577993 := by exact prefixLift 3577993
  have htrace : WordTrace (prefixWord ++ tailWord_3577993) baseStart_3577993 baseEnd_3577993 := by
    simpa [prefixWord, tailWord_3577993, baseEnd_3577993] using wordTrace_append hprefix tailTrace_3577993
  have hstable : (prefixWord ++ tailWord_3577993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3577993).length < 2 ^ (prefixWord ++ tailWord_3577993).sum := by decide
  have hdescent : baseEnd_3577993 < baseStart_3577993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3577993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578040 : List Nat := [2, 1, 2, 1, 2, 1, 3, 5, 2, 3]
def baseStart_3578040 : Nat := 118140960795 + 3578040 * 2 ^ 59
def prefixEnd_3578040 : Nat := 4983230072969 + 3 ^ 40 * 3578040 * 2
def baseEnd_3578040 : Nat := 1224836214008857423829933

theorem tailTrace_3578040 : CollatzResearch.WordTrace tailWord_3578040 prefixEnd_3578040 1224836214008857423829933 := by
  unfold tailWord_3578040
  simp only [CollatzResearch.WordTrace]
  refine ⟨65250919978689817713249787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87001226638253090284333049 65250919978689817713249787)
  ·
    refine ⟨97876379968034726569874681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65250919978689817713249787 97876379968034726569874681)
    ·
      refine ⟨73407284976026044927406011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97876379968034726569874681 73407284976026044927406011)
      ·
        refine ⟨110110927464039067391109017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73407284976026044927406011 110110927464039067391109017)
        ·
          refine ⟨82583195598029300543331763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110110927464039067391109017 82583195598029300543331763)
          ·
            refine ⟨123874793397043950814997645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82583195598029300543331763 123874793397043950814997645)
            ·
              refine ⟨46453047523891481555624117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123874793397043950814997645 46453047523891481555624117)
              ·
                refine ⟨4354973205364826395839761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46453047523891481555624117 4354973205364826395839761)
                ·
                  refine ⟨3266229904023619796879821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4354973205364826395839761 3266229904023619796879821)
                  ·
                    refine ⟨1224836214008857423829933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3266229904023619796879821 1224836214008857423829933)
                    ·
                      rfl

theorem cell22_3578040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_3578040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578040 prefixEnd_3578040 := by exact prefixLift 3578040
  have htrace : WordTrace (prefixWord ++ tailWord_3578040) baseStart_3578040 baseEnd_3578040 := by
    simpa [prefixWord, tailWord_3578040, baseEnd_3578040] using wordTrace_append hprefix tailTrace_3578040
  have hstable : (prefixWord ++ tailWord_3578040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578040).length < 2 ^ (prefixWord ++ tailWord_3578040).sum := by decide
  have hdescent : baseEnd_3578040 < baseStart_3578040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578102 : List Nat := [5, 1, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_3578102 : Nat := 118140960795 + 3578102 * 2 ^ 59
def prefixEnd_3578102 : Nat := 4983230072969 + 3 ^ 40 * 3578102 * 2
def baseEnd_3578102 : Nat := 1224857437875909928779743

theorem tailTrace_3578102 : CollatzResearch.WordTrace tailWord_3578102 prefixEnd_3578102 1224857437875909928779743 := by
  unfold tailWord_3578102
  simp only [CollatzResearch.WordTrace]
  refine ⟨8156506330197188750953535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87002734188770013343504373 8156506330197188750953535)
  ·
    refine ⟨12234759495295783126430303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8156506330197188750953535 12234759495295783126430303)
    ·
      refine ⟨18352139242943674689645455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12234759495295783126430303 18352139242943674689645455)
      ·
        refine ⟨27528208864415512034468183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18352139242943674689645455 27528208864415512034468183)
        ·
          refine ⟨41292313296623268051702275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27528208864415512034468183 41292313296623268051702275)
          ·
            refine ⟨61938469944934902077553413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41292313296623268051702275 61938469944934902077553413)
            ·
              refine ⟨11613463114675294139541265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61938469944934902077553413 11613463114675294139541265)
              ·
                refine ⟨8710097336006470604655949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11613463114675294139541265 8710097336006470604655949)
                ·
                  refine ⟨3266286501002426476745981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8710097336006470604655949 3266286501002426476745981)
                  ·
                    refine ⟨1224857437875909928779743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3266286501002426476745981 1224857437875909928779743)
                    ·
                      rfl

theorem cell22_3578102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_3578102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578102 prefixEnd_3578102 := by exact prefixLift 3578102
  have htrace : WordTrace (prefixWord ++ tailWord_3578102) baseStart_3578102 baseEnd_3578102 := by
    simpa [prefixWord, tailWord_3578102, baseEnd_3578102] using wordTrace_append hprefix tailTrace_3578102
  have hstable : (prefixWord ++ tailWord_3578102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578102).length < 2 ^ (prefixWord ++ tailWord_3578102).sum := by decide
  have hdescent : baseEnd_3578102 < baseStart_3578102 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578149 : List Nat := [1, 3, 1, 2, 5, 2, 2, 1, 5]
def baseStart_3578149 : Nat := 118140960795 + 3578149 * 2 ^ 59
def prefixEnd_3578149 : Nat := 4983230072969 + 3 ^ 40 * 3578149 * 2
def baseEnd_3578149 : Nat := 408291175645472490951533

theorem tailTrace_3578149 : CollatzResearch.WordTrace tailWord_3578149 prefixEnd_3578149 408291175645472490951533 := by
  unfold tailWord_3578149
  simp only [CollatzResearch.WordTrace]
  refine ⟨130505815513984747042217501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87003877009323164694811667 130505815513984747042217501)
  ·
    refine ⟨48939680817744280140831563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130505815513984747042217501 48939680817744280140831563)
    ·
      refine ⟨73409521226616420211247345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48939680817744280140831563 73409521226616420211247345)
      ·
        refine ⟨55057140919962315158435509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73409521226616420211247345 55057140919962315158435509)
        ·
          refine ⟨5161606961246467046103329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55057140919962315158435509 5161606961246467046103329)
          ·
            refine ⟨3871205220934850284577497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5161606961246467046103329 3871205220934850284577497)
            ·
              refine ⟨2903403915701137713433123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3871205220934850284577497 2903403915701137713433123)
              ·
                refine ⟨4355105873551706570149685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903403915701137713433123 4355105873551706570149685)
                ·
                  refine ⟨408291175645472490951533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4355105873551706570149685 408291175645472490951533)
                  ·
                    rfl

theorem cell22_3578149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 2, 1, 5].length) (baseStart_3578149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578149 prefixEnd_3578149 := by exact prefixLift 3578149
  have htrace : WordTrace (prefixWord ++ tailWord_3578149) baseStart_3578149 baseEnd_3578149 := by
    simpa [prefixWord, tailWord_3578149, baseEnd_3578149] using wordTrace_append hprefix tailTrace_3578149
  have hstable : (prefixWord ++ tailWord_3578149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578149).length < 2 ^ (prefixWord ++ tailWord_3578149).sum := by decide
  have hdescent : baseEnd_3578149 < baseStart_3578149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578162 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 3, 4]
def baseStart_3578162 : Nat := 118140960795 + 3578162 * 2 ^ 59
def prefixEnd_3578162 : Nat := 4983230072969 + 3 ^ 40 * 3578162 * 2
def baseEnd_3578162 : Nat := 1224877977102089772279559

theorem tailTrace_3578162 : CollatzResearch.WordTrace tailWord_3578162 prefixEnd_3578162 1224877977102089772279559 := by
  unfold tailWord_3578162
  simp only [CollatzResearch.WordTrace]
  refine ⟨32626572415734412565610185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87004193108625100174960493 32626572415734412565610185)
  ·
    refine ⟨24469929311800809424207639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32626572415734412565610185 24469929311800809424207639)
    ·
      refine ⟨36704893967701214136311459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24469929311800809424207639 36704893967701214136311459)
      ·
        refine ⟨55057340951551821204467189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36704893967701214136311459 55057340951551821204467189)
        ·
          refine ⟨5161625714207983237918799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55057340951551821204467189 5161625714207983237918799)
          ·
            refine ⟨7742438571311974856878199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5161625714207983237918799 7742438571311974856878199)
            ·
              refine ⟨11613657856967962285317299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7742438571311974856878199 11613657856967962285317299)
              ·
                refine ⟨17420486785451943427975949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11613657856967962285317299 17420486785451943427975949)
                ·
                  refine ⟨6532682544544478785490981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17420486785451943427975949 6532682544544478785490981)
                  ·
                    refine ⟨1224877977102089772279559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6532682544544478785490981 1224877977102089772279559)
                    ·
                      rfl

theorem cell22_3578162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 3, 4].length) (baseStart_3578162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578162 prefixEnd_3578162 := by exact prefixLift 3578162
  have htrace : WordTrace (prefixWord ++ tailWord_3578162) baseStart_3578162 baseEnd_3578162 := by
    simpa [prefixWord, tailWord_3578162, baseEnd_3578162] using wordTrace_append hprefix tailTrace_3578162
  have hstable : (prefixWord ++ tailWord_3578162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578162).length < 2 ^ (prefixWord ++ tailWord_3578162).sum := by decide
  have hdescent : baseEnd_3578162 < baseStart_3578162 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578175 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 1, 5]
def baseStart_3578175 : Nat := 118140960795 + 3578175 * 2 ^ 59
def prefixEnd_3578175 : Nat := 4983230072969 + 3 ^ 40 * 3578175 * 2
def baseEnd_3578175 : Nat := 1224882427267762071704519

theorem tailTrace_3578175 : CollatzResearch.WordTrace tailWord_3578175 prefixEnd_3578175 1224882427267762071704519 := by
  unfold tailWord_3578175
  simp only [CollatzResearch.WordTrace]
  refine ⟨130506763811890553482663979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87004509207927035655109319 130506763811890553482663979)
  ·
    refine ⟨195760145717835830223995969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130506763811890553482663979 195760145717835830223995969)
    ·
      refine ⟨146820109288376872667996977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195760145717835830223995969 146820109288376872667996977)
      ·
        refine ⟨110115081966282654500997733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146820109288376872667996977 110115081966282654500997733)
        ·
          refine ⟨20646577868677997718937075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110115081966282654500997733 20646577868677997718937075)
          ·
            refine ⟨30969866803016996578405613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20646577868677997718937075 30969866803016996578405613)
            ·
              refine ⟨11613700051131373716902105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30969866803016996578405613 11613700051131373716902105)
              ·
                refine ⟨8710275038348530287676579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11613700051131373716902105 8710275038348530287676579)
                ·
                  refine ⟨13065412557522795431514869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8710275038348530287676579 13065412557522795431514869)
                  ·
                    refine ⟨1224882427267762071704519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13065412557522795431514869 1224882427267762071704519)
                    ·
                      rfl

theorem cell22_3578175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 5].length) (baseStart_3578175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578175 prefixEnd_3578175 := by exact prefixLift 3578175
  have htrace : WordTrace (prefixWord ++ tailWord_3578175) baseStart_3578175 baseEnd_3578175 := by
    simpa [prefixWord, tailWord_3578175, baseEnd_3578175] using wordTrace_append hprefix tailTrace_3578175
  have hstable : (prefixWord ++ tailWord_3578175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578175).length < 2 ^ (prefixWord ++ tailWord_3578175).sum := by decide
  have hdescent : baseEnd_3578175 < baseStart_3578175 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578190 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_3578190 : Nat := 118140960795 + 3578190 * 2 ^ 59
def prefixEnd_3578190 : Nat := 4983230072969 + 3 ^ 40 * 3578190 * 2
def baseEnd_3578190 : Nat := 1224887562074307032579473

theorem tailTrace_3578190 : CollatzResearch.WordTrace tailWord_3578190 prefixEnd_3578190 1224887562074307032579473 := by
  unfold tailWord_3578190
  simp only [CollatzResearch.WordTrace]
  refine ⟨16313413863354526380557503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87004873937890807362973349 16313413863354526380557503)
  ·
    refine ⟨24470120795031789570836255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16313413863354526380557503 24470120795031789570836255)
    ·
      refine ⟨36705181192547684356254383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24470120795031789570836255 36705181192547684356254383)
      ·
        refine ⟨55057771788821526534381575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36705181192547684356254383 55057771788821526534381575)
        ·
          refine ⟨82586657683232289801572363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55057771788821526534381575 82586657683232289801572363)
          ·
            refine ⟨123879986524848434702358545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82586657683232289801572363 123879986524848434702358545)
            ·
              refine ⟨92909989893636326026768909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123879986524848434702358545 92909989893636326026768909)
              ·
                refine ⟨34841246210113622260038341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92909989893636326026768909 34841246210113622260038341)
                ·
                  refine ⟨6532733664396304173757189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34841246210113622260038341 6532733664396304173757189)
                  ·
                    refine ⟨1224887562074307032579473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6532733664396304173757189 1224887562074307032579473)
                    ·
                      rfl

theorem cell22_3578190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_3578190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578190 prefixEnd_3578190 := by exact prefixLift 3578190
  have htrace : WordTrace (prefixWord ++ tailWord_3578190) baseStart_3578190 baseEnd_3578190 := by
    simpa [prefixWord, tailWord_3578190, baseEnd_3578190] using wordTrace_append hprefix tailTrace_3578190
  have hstable : (prefixWord ++ tailWord_3578190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578190).length < 2 ^ (prefixWord ++ tailWord_3578190).sum := by decide
  have hdescent : baseEnd_3578190 < baseStart_3578190 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578192 : List Nat := [2, 1, 1, 1, 1, 6, 1, 4, 2, 3]
def baseStart_3578192 : Nat := 118140960795 + 3578192 * 2 ^ 59
def prefixEnd_3578192 : Nat := 4983230072969 + 3 ^ 40 * 3578192 * 2
def baseEnd_3578192 : Nat := 1224888246715179694029467

theorem tailTrace_3578192 : CollatzResearch.WordTrace tailWord_3578192 prefixEnd_3578192 1224888246715179694029467 := by
  unfold tailWord_3578192
  simp only [CollatzResearch.WordTrace]
  refine ⟨65253691926414482693016415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87004922568552643590688553 65253691926414482693016415)
  ·
    refine ⟨97880537889621724039524623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65253691926414482693016415 97880537889621724039524623)
    ·
      refine ⟨146820806834432586059286935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97880537889621724039524623 146820806834432586059286935)
      ·
        refine ⟨220231210251648879088930403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146820806834432586059286935 220231210251648879088930403)
        ·
          refine ⟨330346815377473318633395605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220231210251648879088930403 330346815377473318633395605)
          ·
            refine ⟨15485006970819061810940419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 330346815377473318633395605 15485006970819061810940419)
            ·
              refine ⟨23227510456228592716410629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15485006970819061810940419 23227510456228592716410629)
              ·
                refine ⟨4355158210542861134326993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23227510456228592716410629 4355158210542861134326993)
                ·
                  refine ⟨3266368657907145850745245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4355158210542861134326993 3266368657907145850745245)
                  ·
                    refine ⟨1224888246715179694029467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3266368657907145850745245 1224888246715179694029467)
                    ·
                      rfl

theorem cell22_3578192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 4, 2, 3].length) (baseStart_3578192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578192 prefixEnd_3578192 := by exact prefixLift 3578192
  have htrace : WordTrace (prefixWord ++ tailWord_3578192) baseStart_3578192 baseEnd_3578192 := by
    simpa [prefixWord, tailWord_3578192, baseEnd_3578192] using wordTrace_append hprefix tailTrace_3578192
  have hstable : (prefixWord ++ tailWord_3578192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578192).length < 2 ^ (prefixWord ++ tailWord_3578192).sum := by decide
  have hdescent : baseEnd_3578192 < baseStart_3578192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578194 : List Nat := [3, 2, 2, 1, 1, 1, 6, 2, 4]
def baseStart_3578194 : Nat := 118140960795 + 3578194 * 2 ^ 59
def prefixEnd_3578194 : Nat := 4983230072969 + 3 ^ 40 * 3578194 * 2
def baseEnd_3578194 : Nat := 408296310452017451826487

theorem tailTrace_3578194 : CollatzResearch.WordTrace tailWord_3578194 prefixEnd_3578194 408296310452017451826487 := by
  unfold tailWord_3578194
  simp only [CollatzResearch.WordTrace]
  refine ⟨32626864199705429931901409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87004971199214479818403757 32626864199705429931901409)
  ·
    refine ⟨24470148149779072448926057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32626864199705429931901409 24470148149779072448926057)
    ·
      refine ⟨18352611112334304336694543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24470148149779072448926057 18352611112334304336694543)
      ·
        refine ⟨27528916668501456505041815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18352611112334304336694543 27528916668501456505041815)
        ·
          refine ⟨41293375002752184757562723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27528916668501456505041815 41293375002752184757562723)
          ·
            refine ⟨61940062504128277136344085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41293375002752184757562723 61940062504128277136344085)
            ·
              refine ⟨2903440429881012990766129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 61940062504128277136344085 2903440429881012990766129)
              ·
                refine ⟨2177580322410759743074597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2903440429881012990766129 2177580322410759743074597)
                ·
                  refine ⟨408296310452017451826487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2177580322410759743074597 408296310452017451826487)
                  ·
                    rfl

theorem cell22_3578194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 2, 4].length) (baseStart_3578194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578194 prefixEnd_3578194 := by exact prefixLift 3578194
  have htrace : WordTrace (prefixWord ++ tailWord_3578194) baseStart_3578194 baseEnd_3578194 := by
    simpa [prefixWord, tailWord_3578194, baseEnd_3578194] using wordTrace_append hprefix tailTrace_3578194
  have hstable : (prefixWord ++ tailWord_3578194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578194).length < 2 ^ (prefixWord ++ tailWord_3578194).sum := by decide
  have hdescent : baseEnd_3578194 < baseStart_3578194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578230 : List Nat := [5, 1, 1, 4, 2, 1, 2, 1, 1, 4]
def baseStart_3578230 : Nat := 118140960795 + 3578230 * 2 ^ 59
def prefixEnd_3578230 : Nat := 4983230072969 + 3 ^ 40 * 3578230 * 2
def baseEnd_3578230 : Nat := 1224901254891760261579351

theorem tailTrace_3578230 : CollatzResearch.WordTrace tailWord_3578230 prefixEnd_3578230 1224901254891760261579351 := by
  unfold tailWord_3578230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8156798114168206117244759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87005846551127531917277429 8156798114168206117244759)
  ·
    refine ⟨12235197171252309175867139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8156798114168206117244759 12235197171252309175867139)
    ·
      refine ⟨18352795756878463763800709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12235197171252309175867139 18352795756878463763800709)
      ·
        refine ⟨3441149204414711955712633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18352795756878463763800709 3441149204414711955712633)
        ·
          refine ⟨2580861903311033966784475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3441149204414711955712633 2580861903311033966784475)
          ·
            refine ⟨3871292854966550950176713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2580861903311033966784475 3871292854966550950176713)
            ·
              refine ⟨2903469641224913212632535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3871292854966550950176713 2903469641224913212632535)
              ·
                refine ⟨4355204461837369818948803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903469641224913212632535 4355204461837369818948803)
                ·
                  refine ⟨6532806692756054728423205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355204461837369818948803 6532806692756054728423205)
                  ·
                    refine ⟨1224901254891760261579351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6532806692756054728423205 1224901254891760261579351)
                    ·
                      rfl

theorem cell22_3578230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 2, 1, 1, 4].length) (baseStart_3578230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578230 prefixEnd_3578230 := by exact prefixLift 3578230
  have htrace : WordTrace (prefixWord ++ tailWord_3578230) baseStart_3578230 baseEnd_3578230 := by
    simpa [prefixWord, tailWord_3578230, baseEnd_3578230] using wordTrace_append hprefix tailTrace_3578230
  have hstable : (prefixWord ++ tailWord_3578230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578230).length < 2 ^ (prefixWord ++ tailWord_3578230).sum := by decide
  have hdescent : baseEnd_3578230 < baseStart_3578230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578254 : List Nat := [4, 1, 1, 4, 1, 1, 1, 3, 3, 3]
def baseStart_3578254 : Nat := 118140960795 + 3578254 * 2 ^ 59
def prefixEnd_3578254 : Nat := 4983230072969 + 3 ^ 40 * 3578254 * 2
def baseEnd_3578254 : Nat := 1224909470582232198979277

theorem tailTrace_3578254 : CollatzResearch.WordTrace tailWord_3578254 prefixEnd_3578254 1224909470582232198979277 := by
  unfold tailWord_3578254
  simp only [CollatzResearch.WordTrace]
  refine ⟨16313705647325543746848727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87006430119069566649859877 16313705647325543746848727)
  ·
    refine ⟨24470558470988315620273091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16313705647325543746848727 24470558470988315620273091)
    ·
      refine ⟨36705837706482473430409637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24470558470988315620273091 36705837706482473430409637)
      ·
        refine ⟨6882344569965463768201807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36705837706482473430409637 6882344569965463768201807)
        ·
          refine ⟨10323516854948195652302711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6882344569965463768201807 10323516854948195652302711)
          ·
            refine ⟨15485275282422293478454067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10323516854948195652302711 15485275282422293478454067)
            ·
              refine ⟨23227912923633440217681101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15485275282422293478454067 23227912923633440217681101)
              ·
                refine ⟨8710467346362540081630413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23227912923633440217681101 8710467346362540081630413)
                ·
                  refine ⟨3266425254885952530611405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8710467346362540081630413 3266425254885952530611405)
                  ·
                    refine ⟨1224909470582232198979277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3266425254885952530611405 1224909470582232198979277)
                    ·
                      rfl

theorem cell22_3578254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_3578254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578254 prefixEnd_3578254 := by exact prefixLift 3578254
  have htrace : WordTrace (prefixWord ++ tailWord_3578254) baseStart_3578254 baseEnd_3578254 := by
    simpa [prefixWord, tailWord_3578254, baseEnd_3578254] using wordTrace_append hprefix tailTrace_3578254
  have hstable : (prefixWord ++ tailWord_3578254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578254).length < 2 ^ (prefixWord ++ tailWord_3578254).sum := by decide
  have hdescent : baseEnd_3578254 < baseStart_3578254 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578265 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 2, 5]
def baseStart_3578265 : Nat := 118140960795 + 3578265 * 2 ^ 59
def prefixEnd_3578265 : Nat := 4983230072969 + 3 ^ 40 * 3578265 * 2
def baseEnd_3578265 : Nat := 1224913236107031836954243

theorem tailTrace_3578265 : CollatzResearch.WordTrace tailWord_3578265 prefixEnd_3578265 1224913236107031836954243 := by
  unfold tailWord_3578265
  simp only [CollatzResearch.WordTrace]
  refine ⟨130510046381564498853440249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87006697587709665902293499 130510046381564498853440249)
  ·
    refine ⟨97882534786173374140080187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130510046381564498853440249 97882534786173374140080187)
    ·
      refine ⟨146823802179260061210120281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97882534786173374140080187 146823802179260061210120281)
      ·
        refine ⟨110117851634445045907590211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146823802179260061210120281 110117851634445045907590211)
        ·
          refine ⟨165176777451667568861385317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110117851634445045907590211 165176777451667568861385317)
          ·
            refine ⟨30970645772187669161509747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165176777451667568861385317 30970645772187669161509747)
            ·
              refine ⟨46455968658281503742264621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30970645772187669161509747 46455968658281503742264621)
              ·
                refine ⟨17420988246855563903349233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46455968658281503742264621 17420988246855563903349233)
                ·
                  refine ⟨13065741185141672927511925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17420988246855563903349233 13065741185141672927511925)
                  ·
                    refine ⟨1224913236107031836954243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13065741185141672927511925 1224913236107031836954243)
                    ·
                      rfl

theorem cell22_3578265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 2, 5].length) (baseStart_3578265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578265 prefixEnd_3578265 := by exact prefixLift 3578265
  have htrace : WordTrace (prefixWord ++ tailWord_3578265) baseStart_3578265 baseEnd_3578265 := by
    simpa [prefixWord, tailWord_3578265, baseEnd_3578265] using wordTrace_append hprefix tailTrace_3578265
  have hstable : (prefixWord ++ tailWord_3578265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578265).length < 2 ^ (prefixWord ++ tailWord_3578265).sum := by decide
  have hdescent : baseEnd_3578265 < baseStart_3578265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578305 : List Nat := [1, 2, 7, 1, 1, 2, 1, 1, 3, 3]
def baseStart_3578305 : Nat := 118140960795 + 3578305 * 2 ^ 59
def prefixEnd_3578305 : Nat := 4983230072969 + 3 ^ 40 * 3578305 * 2
def baseEnd_3578305 : Nat := 1224926928924485065954121

theorem tailTrace_3578305 : CollatzResearch.WordTrace tailWord_3578305 prefixEnd_3578305 1224926928924485065954121 := by
  unfold tailWord_3578305
  simp only [CollatzResearch.WordTrace]
  refine ⟨130511505301419585684896369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87007670200946390456597579 130511505301419585684896369)
  ·
    refine ⟨97883628976064689263672277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130511505301419585684896369 97883628976064689263672277)
    ·
      refine ⟨2294147554126516154617319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 97883628976064689263672277 2294147554126516154617319)
      ·
        refine ⟨3441221331189774231925979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294147554126516154617319 3441221331189774231925979)
        ·
          refine ⟨5161831996784661347888969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441221331189774231925979 5161831996784661347888969)
          ·
            refine ⟨3871373997588496010916727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5161831996784661347888969 3871373997588496010916727)
            ·
              refine ⟨5807060996382744016375091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871373997588496010916727 5807060996382744016375091)
              ·
                refine ⟨8710591494574116024562637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807060996382744016375091 8710591494574116024562637)
                ·
                  refine ⟨3266471810465293509210989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8710591494574116024562637 3266471810465293509210989)
                  ·
                    refine ⟨1224926928924485065954121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3266471810465293509210989 1224926928924485065954121)
                    ·
                      rfl

theorem cell22_3578305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_3578305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578305 prefixEnd_3578305 := by exact prefixLift 3578305
  have htrace : WordTrace (prefixWord ++ tailWord_3578305) baseStart_3578305 baseEnd_3578305 := by
    simpa [prefixWord, tailWord_3578305, baseEnd_3578305] using wordTrace_append hprefix tailTrace_3578305
  have hstable : (prefixWord ++ tailWord_3578305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578305).length < 2 ^ (prefixWord ++ tailWord_3578305).sum := by decide
  have hdescent : baseEnd_3578305 < baseStart_3578305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578312 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 6]
def baseStart_3578312 : Nat := 118140960795 + 3578312 * 2 ^ 59
def prefixEnd_3578312 : Nat := 4983230072969 + 3 ^ 40 * 3578312 * 2
def baseEnd_3578312 : Nat := 408309775055846460343033

theorem tailTrace_3578312 : CollatzResearch.WordTrace tailWord_3578312 prefixEnd_3578312 408309775055846460343033 := by
  unfold tailWord_3578312
  simp only [CollatzResearch.WordTrace]
  refine ⟨65255880306197112940200595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87007840408262817253600793 65255880306197112940200595)
  ·
    refine ⟨97883820459295669410300893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65255880306197112940200595 97883820459295669410300893)
    ·
      refine ⟨36706432672235876028862835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97883820459295669410300893 36706432672235876028862835)
      ·
        refine ⟨55059649008353814043294253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36706432672235876028862835 55059649008353814043294253)
        ·
          refine ⟨20647368378132680266235345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55059649008353814043294253 20647368378132680266235345)
          ·
            refine ⟨15485526283599510199676509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20647368378132680266235345 15485526283599510199676509)
            ·
              refine ⟨5807072356349816324878691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15485526283599510199676509 5807072356349816324878691)
              ·
                refine ⟨8710608534524724487318037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807072356349816324878691 8710608534524724487318037)
                ·
                  refine ⟨408309775055846460343033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8710608534524724487318037 408309775055846460343033)
                  ·
                    rfl

theorem cell22_3578312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 6].length) (baseStart_3578312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578312 prefixEnd_3578312 := by exact prefixLift 3578312
  have htrace : WordTrace (prefixWord ++ tailWord_3578312) baseStart_3578312 baseEnd_3578312 := by
    simpa [prefixWord, tailWord_3578312, baseEnd_3578312] using wordTrace_append hprefix tailTrace_3578312
  have hstable : (prefixWord ++ tailWord_3578312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578312).length < 2 ^ (prefixWord ++ tailWord_3578312).sum := by decide
  have hdescent : baseEnd_3578312 < baseStart_3578312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578357 : List Nat := [1, 3, 5, 1, 12]
def baseStart_3578357 : Nat := 118140960795 + 3578357 * 2 ^ 59
def prefixEnd_3578357 : Nat := 4983230072969 + 3 ^ 40 * 3578357 * 2
def baseEnd_3578357 : Nat := 5040924813115943471827

theorem tailTrace_3578357 : CollatzResearch.WordTrace tailWord_3578357 prefixEnd_3578357 5040924813115943471827 := by
  unfold tailWord_3578357
  simp only [CollatzResearch.WordTrace]
  refine ⟨130513401897231198565789325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87008934598154132377192883 130513401897231198565789325)
  ·
    refine ⟨48942525711461699462170997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130513401897231198565789325 48942525711461699462170997)
    ·
      refine ⟨4588361785449534324578531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48942525711461699462170997 4588361785449534324578531)
      ·
        refine ⟨6882542678174301486867797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4588361785449534324578531 6882542678174301486867797)
        ·
          refine ⟨5040924813115943471827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 6882542678174301486867797 5040924813115943471827)
          ·
            rfl

theorem cell22_3578357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 12].length) (baseStart_3578357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578357 prefixEnd_3578357 := by exact prefixLift 3578357
  have htrace : WordTrace (prefixWord ++ tailWord_3578357) baseStart_3578357 baseEnd_3578357 := by
    simpa [prefixWord, tailWord_3578357, baseEnd_3578357] using wordTrace_append hprefix tailTrace_3578357
  have hstable : (prefixWord ++ tailWord_3578357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578357).length < 2 ^ (prefixWord ++ tailWord_3578357).sum := by decide
  have hdescent : baseEnd_3578357 < baseStart_3578357 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578389 : List Nat := [1, 3, 2, 1, 3, 1, 3, 2, 3, 3]
def baseStart_3578389 : Nat := 118140960795 + 3578389 * 2 ^ 59
def prefixEnd_3578389 : Nat := 4983230072969 + 3 ^ 40 * 3578389 * 2
def baseEnd_3578389 : Nat := 1224955683841136846853863

theorem tailTrace_3578389 : CollatzResearch.WordTrace tailWord_3578389 prefixEnd_3578389 1224955683841136846853863 := by
  unfold tailWord_3578389
  simp only [CollatzResearch.WordTrace]
  refine ⟨130514569033115268030954221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87009712688743512020636147 130514569033115268030954221)
  ·
    refine ⟨48942963387418225511607833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130514569033115268030954221 48942963387418225511607833)
    ·
      refine ⟨36707222540563669133705875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48942963387418225511607833 36707222540563669133705875)
      ·
        refine ⟨55060833810845503700558813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36707222540563669133705875 55060833810845503700558813)
        ·
          refine ⟨20647812679067063887709555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55060833810845503700558813 20647812679067063887709555)
          ·
            refine ⟨30971719018600595831564333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20647812679067063887709555 30971719018600595831564333)
            ·
              refine ⟨11614394631975223436836625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30971719018600595831564333 11614394631975223436836625)
              ·
                refine ⟨8710795973981417577627469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11614394631975223436836625 8710795973981417577627469)
                ·
                  refine ⟨3266548490243031591610301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8710795973981417577627469 3266548490243031591610301)
                  ·
                    refine ⟨1224955683841136846853863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3266548490243031591610301 1224955683841136846853863)
                    ·
                      rfl

theorem cell22_3578389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_3578389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578389 prefixEnd_3578389 := by exact prefixLift 3578389
  have htrace : WordTrace (prefixWord ++ tailWord_3578389) baseStart_3578389 baseEnd_3578389 := by
    simpa [prefixWord, tailWord_3578389, baseEnd_3578389] using wordTrace_append hprefix tailTrace_3578389
  have hstable : (prefixWord ++ tailWord_3578389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578389).length < 2 ^ (prefixWord ++ tailWord_3578389).sum := by decide
  have hdescent : baseEnd_3578389 < baseStart_3578389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578391 : List Nat := [1, 1, 3, 6, 1, 1, 3, 6]
def baseStart_3578391 : Nat := 118140960795 + 3578391 * 2 ^ 59
def prefixEnd_3578391 : Nat := 4983230072969 + 3 ^ 40 * 3578391 * 2
def baseEnd_3578391 : Nat := 136106263164667723144873

theorem tailTrace_3578391 : CollatzResearch.WordTrace tailWord_3578391 prefixEnd_3578391 136106263164667723144873 := by
  unfold tailWord_3578391
  simp only [CollatzResearch.WordTrace]
  refine ⟨130514641979108022372527027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87009761319405348248351351 130514641979108022372527027)
  ·
    refine ⟨195771962968662033558790541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130514641979108022372527027 195771962968662033558790541)
    ·
      refine ⟨73414486113248262584546453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195771962968662033558790541 73414486113248262584546453)
      ·
        refine ⟨3441304036558512308650615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 73414486113248262584546453 3441304036558512308650615)
        ·
          refine ⟨5161956054837768462975923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441304036558512308650615 5161956054837768462975923)
          ·
            refine ⟨7742934082256652694463885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5161956054837768462975923 7742934082256652694463885)
            ·
              refine ⟨2903600280846244760423957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7742934082256652694463885 2903600280846244760423957)
              ·
                refine ⟨136106263164667723144873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2903600280846244760423957 136106263164667723144873)
                ·
                  rfl

theorem cell22_3578391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 3, 6].length) (baseStart_3578391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578391 prefixEnd_3578391 := by exact prefixLift 3578391
  have htrace : WordTrace (prefixWord ++ tailWord_3578391) baseStart_3578391 baseEnd_3578391 := by
    simpa [prefixWord, tailWord_3578391, baseEnd_3578391] using wordTrace_append hprefix tailTrace_3578391
  have hstable : (prefixWord ++ tailWord_3578391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578391).length < 2 ^ (prefixWord ++ tailWord_3578391).sum := by decide
  have hdescent : baseEnd_3578391 < baseStart_3578391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578402 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 7]
def baseStart_3578402 : Nat := 118140960795 + 3578402 * 2 ^ 59
def prefixEnd_3578402 : Nat := 4983230072969 + 3 ^ 40 * 3578402 * 2
def baseEnd_3578402 : Nat := 408320044668936382092941

theorem tailTrace_3578402 : CollatzResearch.WordTrace tailWord_3578402 prefixEnd_3578402 408320044668936382092941 := by
  unfold tailWord_3578402
  simp only [CollatzResearch.WordTrace]
  refine ⟨32628760795517042812794365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87010028788045447500784973 32628760795517042812794365)
  ·
    refine ⟨12235785298318891054797887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32628760795517042812794365 12235785298318891054797887)
    ·
      refine ⟨18353677947478336582196831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12235785298318891054797887 18353677947478336582196831)
      ·
        refine ⟨27530516921217504873295247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18353677947478336582196831 27530516921217504873295247)
        ·
          refine ⟨41295775381826257309942871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27530516921217504873295247 41295775381826257309942871)
          ·
            refine ⟨61943663072739385964914307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41295775381826257309942871 61943663072739385964914307)
            ·
              refine ⟨92915494609109078947371461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61943663072739385964914307 92915494609109078947371461)
              ·
                refine ⟨17421655239207952302632149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 92915494609109078947371461 17421655239207952302632149)
                ·
                  refine ⟨408320044668936382092941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17421655239207952302632149 408320044668936382092941)
                  ·
                    rfl

theorem cell22_3578402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 7].length) (baseStart_3578402 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578402 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578402 prefixEnd_3578402 := by exact prefixLift 3578402
  have htrace : WordTrace (prefixWord ++ tailWord_3578402) baseStart_3578402 baseEnd_3578402 := by
    simpa [prefixWord, tailWord_3578402, baseEnd_3578402] using wordTrace_append hprefix tailTrace_3578402
  have hstable : (prefixWord ++ tailWord_3578402).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578402).length < 2 ^ (prefixWord ++ tailWord_3578402).sum := by decide
  have hdescent : baseEnd_3578402 < baseStart_3578402 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578417 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 2, 5]
def baseStart_3578417 : Nat := 118140960795 + 3578417 * 2 ^ 59
def prefixEnd_3578417 : Nat := 4983230072969 + 3 ^ 40 * 3578417 * 2
def baseEnd_3578417 : Nat := 1224965268813354107153777

theorem tailTrace_3578417 : CollatzResearch.WordTrace tailWord_3578417 prefixEnd_3578417 1224965268813354107153777 := by
  unfold tailWord_3578417
  simp only [CollatzResearch.WordTrace]
  refine ⟨130515590277013828812973505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87010393518009219208649003 130515590277013828812973505)
  ·
    refine ⟨97886692707760371609730129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130515590277013828812973505 97886692707760371609730129)
    ·
      refine ⟨73415019530820278707297597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97886692707760371609730129 73415019530820278707297597)
      ·
        refine ⟨27530632324057604515236599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73415019530820278707297597 27530632324057604515236599)
        ·
          refine ⟨41295948486086406772854899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27530632324057604515236599 41295948486086406772854899)
          ·
            refine ⟨61943922729129610159282349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41295948486086406772854899 61943922729129610159282349)
            ·
              refine ⟨23228971023423603809730881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61943922729129610159282349 23228971023423603809730881)
              ·
                refine ⟨17421728267567702857298161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23228971023423603809730881 17421728267567702857298161)
                ·
                  refine ⟨13066296200675777142973621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17421728267567702857298161 13066296200675777142973621)
                  ·
                    refine ⟨1224965268813354107153777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13066296200675777142973621 1224965268813354107153777)
                    ·
                      rfl

theorem cell22_3578417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 2, 5].length) (baseStart_3578417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578417 prefixEnd_3578417 := by exact prefixLift 3578417
  have htrace : WordTrace (prefixWord ++ tailWord_3578417) baseStart_3578417 baseEnd_3578417 := by
    simpa [prefixWord, tailWord_3578417, baseEnd_3578417] using wordTrace_append hprefix tailTrace_3578417
  have hstable : (prefixWord ++ tailWord_3578417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578417).length < 2 ^ (prefixWord ++ tailWord_3578417).sum := by decide
  have hdescent : baseEnd_3578417 < baseStart_3578417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578432 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 5, 4]
def baseStart_3578432 : Nat := 118140960795 + 3578432 * 2 ^ 59
def prefixEnd_3578432 : Nat := 4983230072969 + 3 ^ 40 * 3578432 * 2
def baseEnd_3578432 : Nat := 1224970403619899068028731

theorem tailTrace_3578432 : CollatzResearch.WordTrace tailWord_3578432 prefixEnd_3578432 1224970403619899068028731 := by
  unfold tailWord_3578432
  simp only [CollatzResearch.WordTrace]
  refine ⟨65258068685979743187384775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87010758247972990916513033 65258068685979743187384775)
  ·
    refine ⟨97887103028969614781077163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65258068685979743187384775 97887103028969614781077163)
    ·
      refine ⟨146830654543454422171615745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97887103028969614781077163 146830654543454422171615745)
      ·
        refine ⟨110122990907590816628711809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146830654543454422171615745 110122990907590816628711809)
        ·
          refine ⟨82592243180693112471533857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110122990907590816628711809 82592243180693112471533857)
          ·
            refine ⟨61944182385519834353650393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82592243180693112471533857 61944182385519834353650393)
            ·
              refine ⟨46458136789139875765237795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61944182385519834353650393 46458136789139875765237795)
              ·
                refine ⟨69687205183709813647856693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46458136789139875765237795 69687205183709813647856693)
                ·
                  refine ⟨6533175485972795029486565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69687205183709813647856693 6533175485972795029486565)
                  ·
                    refine ⟨1224970403619899068028731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6533175485972795029486565 1224970403619899068028731)
                    ·
                      rfl

theorem cell22_3578432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 5, 4].length) (baseStart_3578432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578432 prefixEnd_3578432 := by exact prefixLift 3578432
  have htrace : WordTrace (prefixWord ++ tailWord_3578432) baseStart_3578432 baseEnd_3578432 := by
    simpa [prefixWord, tailWord_3578432, baseEnd_3578432] using wordTrace_append hprefix tailTrace_3578432
  have hstable : (prefixWord ++ tailWord_3578432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578432).length < 2 ^ (prefixWord ++ tailWord_3578432).sum := by decide
  have hdescent : baseEnd_3578432 < baseStart_3578432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578447 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 6]
def baseStart_3578447 : Nat := 118140960795 + 3578447 * 2 ^ 59
def prefixEnd_3578447 : Nat := 4983230072969 + 3 ^ 40 * 3578447 * 2
def baseEnd_3578447 : Nat := 408325179475481342967895

theorem tailTrace_3578447 : CollatzResearch.WordTrace tailWord_3578447 prefixEnd_3578447 408325179475481342967895 := by
  unfold tailWord_3578447
  simp only [CollatzResearch.WordTrace]
  refine ⟨130516684466905143936565595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87011122977936762624377063 130516684466905143936565595)
  ·
    refine ⟨195775026700357715904848393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130516684466905143936565595 195775026700357715904848393)
    ·
      refine ⟨146831270025268286928636295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195775026700357715904848393 146831270025268286928636295)
      ·
        refine ⟨220246905037902430392954443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146831270025268286928636295 220246905037902430392954443)
        ·
          refine ⟨330370357556853645589431665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220246905037902430392954443 330370357556853645589431665)
          ·
            refine ⟨247777768167640234192073749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330370357556853645589431665 247777768167640234192073749)
            ·
              refine ⟨11614582882858135977753457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 247777768167640234192073749 11614582882858135977753457)
              ·
                refine ⟨8710937162143601983315093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11614582882858135977753457 8710937162143601983315093)
                ·
                  refine ⟨408325179475481342967895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8710937162143601983315093 408325179475481342967895)
                  ·
                    rfl

theorem cell22_3578447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 6].length) (baseStart_3578447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578447 prefixEnd_3578447 := by exact prefixLift 3578447
  have htrace : WordTrace (prefixWord ++ tailWord_3578447) baseStart_3578447 baseEnd_3578447 := by
    simpa [prefixWord, tailWord_3578447, baseEnd_3578447] using wordTrace_append hprefix tailTrace_3578447
  have hstable : (prefixWord ++ tailWord_3578447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578447).length < 2 ^ (prefixWord ++ tailWord_3578447).sum := by decide
  have hdescent : baseEnd_3578447 < baseStart_3578447 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578449 : List Nat := [1, 2, 2, 1, 3, 3, 1, 4, 1, 4]
def baseStart_3578449 : Nat := 118140960795 + 3578449 * 2 ^ 59
def prefixEnd_3578449 : Nat := 4983230072969 + 3 ^ 40 * 3578449 * 2
def baseEnd_3578449 : Nat := 1224976223067316690353679

theorem tailTrace_3578449 : CollatzResearch.WordTrace tailWord_3578449 prefixEnd_3578449 1224976223067316690353679 := by
  unfold tailWord_3578449
  simp only [CollatzResearch.WordTrace]
  refine ⟨130516757412897898278138401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87011171608598598852092267 130516757412897898278138401)
  ·
    refine ⟨97887568059673423708603801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130516757412897898278138401 97887568059673423708603801)
    ·
      refine ⟨73415676044755067781452851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97887568059673423708603801 73415676044755067781452851)
      ·
        refine ⟨110123514067132601672179277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73415676044755067781452851 110123514067132601672179277)
        ·
          refine ⟨41296317775174725627067229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110123514067132601672179277 41296317775174725627067229)
          ·
            refine ⟨15486119165690522110150211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41296317775174725627067229 15486119165690522110150211)
            ·
              refine ⟨23229178748535783165225317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15486119165690522110150211 23229178748535783165225317)
              ·
                refine ⟨4355471015350459343479747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23229178748535783165225317 4355471015350459343479747)
                ·
                  refine ⟨6533206523025689015219621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355471015350459343479747 6533206523025689015219621)
                  ·
                    refine ⟨1224976223067316690353679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6533206523025689015219621 1224976223067316690353679)
                    ·
                      rfl

theorem cell22_3578449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 4, 1, 4].length) (baseStart_3578449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578449 prefixEnd_3578449 := by exact prefixLift 3578449
  have htrace : WordTrace (prefixWord ++ tailWord_3578449) baseStart_3578449 baseEnd_3578449 := by
    simpa [prefixWord, tailWord_3578449, baseEnd_3578449] using wordTrace_append hprefix tailTrace_3578449
  have hstable : (prefixWord ++ tailWord_3578449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578449).length < 2 ^ (prefixWord ++ tailWord_3578449).sum := by decide
  have hdescent : baseEnd_3578449 < baseStart_3578449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578479 : List Nat := [1, 1, 2, 1, 3, 2, 4, 1, 4, 3]
def baseStart_3578479 : Nat := 118140960795 + 3578479 * 2 ^ 59
def prefixEnd_3578479 : Nat := 4983230072969 + 3 ^ 40 * 3578479 * 2
def baseEnd_3578479 : Nat := 1224986492680406612103587

theorem tailTrace_3578479 : CollatzResearch.WordTrace tailWord_3578479 prefixEnd_3578479 1224986492680406612103587 := by
  unfold tailWord_3578479
  simp only [CollatzResearch.WordTrace]
  refine ⟨130517851602789213401730491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87011901068526142267820327 130517851602789213401730491)
  ·
    refine ⟨195776777404183820102595737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130517851602789213401730491 195776777404183820102595737)
    ·
      refine ⟨146832583053137865076946803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195776777404183820102595737 146832583053137865076946803)
      ·
        refine ⟨220248874579706797615420205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146832583053137865076946803 220248874579706797615420205)
        ·
          refine ⟨82593327967390049105782577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220248874579706797615420205 82593327967390049105782577)
          ·
            refine ⟨61944995975542536829336933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82593327967390049105782577 61944995975542536829336933)
            ·
              refine ⟨11614686745414225655500675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61944995975542536829336933 11614686745414225655500675)
              ·
                refine ⟨17422030118121338483251013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11614686745414225655500675 17422030118121338483251013)
                ·
                  refine ⟨3266630647147750965609565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17422030118121338483251013 3266630647147750965609565)
                  ·
                    refine ⟨1224986492680406612103587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3266630647147750965609565 1224986492680406612103587)
                    ·
                      rfl

theorem cell22_3578479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 1, 4, 3].length) (baseStart_3578479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578479 prefixEnd_3578479 := by exact prefixLift 3578479
  have htrace : WordTrace (prefixWord ++ tailWord_3578479) baseStart_3578479 baseEnd_3578479 := by
    simpa [prefixWord, tailWord_3578479, baseEnd_3578479] using wordTrace_append hprefix tailTrace_3578479
  have hstable : (prefixWord ++ tailWord_3578479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578479).length < 2 ^ (prefixWord ++ tailWord_3578479).sum := by decide
  have hdescent : baseEnd_3578479 < baseStart_3578479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578492 : List Nat := [2, 2, 2, 1, 1, 2, 3, 9]
def baseStart_3578492 : Nat := 118140960795 + 3578492 * 2 ^ 59
def prefixEnd_3578492 : Nat := 4983230072969 + 3 ^ 40 * 3578492 * 2
def baseEnd_3578492 : Nat := 136110104760675434614283

theorem tailTrace_3578492 : CollatzResearch.WordTrace tailWord_3578492 prefixEnd_3578492 136110104760675434614283 := by
  unfold tailWord_3578492
  simp only [CollatzResearch.WordTrace]
  refine ⟨65259162875871058310976865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87012217167828077747969153 65259162875871058310976865)
  ·
    refine ⟨48944372156903293733232649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65259162875871058310976865 48944372156903293733232649)
    ·
      refine ⟨36708279117677470299924487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48944372156903293733232649 36708279117677470299924487)
      ·
        refine ⟨55062418676516205449886731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36708279117677470299924487 55062418676516205449886731)
        ·
          refine ⟨82593628014774308174830097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55062418676516205449886731 82593628014774308174830097)
          ·
            refine ⟨61945221011080731131122573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82593628014774308174830097 61945221011080731131122573)
            ·
              refine ⟨23229457879155274174170965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61945221011080731131122573 23229457879155274174170965)
              ·
                refine ⟨136110104760675434614283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23229457879155274174170965 136110104760675434614283)
                ·
                  rfl

theorem cell22_3578492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 9].length) (baseStart_3578492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578492 prefixEnd_3578492 := by exact prefixLift 3578492
  have htrace : WordTrace (prefixWord ++ tailWord_3578492) baseStart_3578492 baseEnd_3578492 := by
    simpa [prefixWord, tailWord_3578492, baseEnd_3578492] using wordTrace_append hprefix tailTrace_3578492
  have hstable : (prefixWord ++ tailWord_3578492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578492).length < 2 ^ (prefixWord ++ tailWord_3578492).sum := by decide
  have hdescent : baseEnd_3578492 < baseStart_3578492 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578496 : List Nat := [2, 1, 1, 2, 1, 6, 1, 3, 2, 3]
def baseStart_3578496 : Nat := 118140960795 + 3578496 * 2 ^ 59
def prefixEnd_3578496 : Nat := 4983230072969 + 3 ^ 40 * 3578496 * 2
def baseEnd_3578496 : Nat := 1224992312127824234428535

theorem tailTrace_3578496 : CollatzResearch.WordTrace tailWord_3578496 prefixEnd_3578496 1224992312127824234428535 := by
  unfold tailWord_3578496
  simp only [CollatzResearch.WordTrace]
  refine ⟨65259235821863812652549671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87012314429151750203399561 65259235821863812652549671)
  ·
    refine ⟨97888853732795718978824507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65259235821863812652549671 97888853732795718978824507)
    ·
      refine ⟨146833280599193578468236761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97888853732795718978824507 146833280599193578468236761)
      ·
        refine ⟨110124960449395183851177571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146833280599193578468236761 110124960449395183851177571)
        ·
          refine ⟨165187440674092775776766357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110124960449395183851177571 165187440674092775776766357)
          ·
            refine ⟨7743161281598098864535923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165187440674092775776766357 7743161281598098864535923)
            ·
              refine ⟨11614741922397148296803885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7743161281598098864535923 11614741922397148296803885)
              ·
                refine ⟨4355528220898930611301457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11614741922397148296803885 4355528220898930611301457)
                ·
                  refine ⟨3266646165674197958476093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4355528220898930611301457 3266646165674197958476093)
                  ·
                    refine ⟨1224992312127824234428535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3266646165674197958476093 1224992312127824234428535)
                    ·
                      rfl

theorem cell22_3578496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 3, 2, 3].length) (baseStart_3578496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578496 prefixEnd_3578496 := by exact prefixLift 3578496
  have htrace : WordTrace (prefixWord ++ tailWord_3578496) baseStart_3578496 baseEnd_3578496 := by
    simpa [prefixWord, tailWord_3578496, baseEnd_3578496] using wordTrace_append hprefix tailTrace_3578496
  have hstable : (prefixWord ++ tailWord_3578496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578496).length < 2 ^ (prefixWord ++ tailWord_3578496).sum := by decide
  have hdescent : baseEnd_3578496 < baseStart_3578496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578554 : List Nat := [3, 1, 1, 1, 2, 3, 1, 5, 5]
def baseStart_3578554 : Nat := 118140960795 + 3578554 * 2 ^ 59
def prefixEnd_3578554 : Nat := 4983230072969 + 3 ^ 40 * 3578554 * 2
def baseEnd_3578554 : Nat := 408337388904377138826119

theorem tailTrace_3578554 : CollatzResearch.WordTrace tailWord_3578554 prefixEnd_3578554 408337388904377138826119 := by
  unfold tailWord_3578554
  simp only [CollatzResearch.WordTrace]
  refine ⟨32630146769379375302677679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87013724718345000807140477 32630146769379375302677679)
  ·
    refine ⟨48945220154069062954016519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32630146769379375302677679 48945220154069062954016519)
    ·
      refine ⟨73417830231103594431024779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48945220154069062954016519 73417830231103594431024779)
      ·
        refine ⟨110126745346655391646537169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73417830231103594431024779 110126745346655391646537169)
        ·
          refine ⟨82595059009991543734902877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110126745346655391646537169 82595059009991543734902877)
          ·
            refine ⟨30973147128746828900588579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82595059009991543734902877 30973147128746828900588579)
            ·
              refine ⟨46459720693120243350882869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30973147128746828900588579 46459720693120243350882869)
              ·
                refine ⟨4355598814980022814145269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46459720693120243350882869 4355598814980022814145269)
                ·
                  refine ⟨408337388904377138826119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4355598814980022814145269 408337388904377138826119)
                  ·
                    rfl

theorem cell22_3578554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 5].length) (baseStart_3578554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578554 prefixEnd_3578554 := by exact prefixLift 3578554
  have htrace : WordTrace (prefixWord ++ tailWord_3578554) baseStart_3578554 baseEnd_3578554 := by
    simpa [prefixWord, tailWord_3578554, baseEnd_3578554] using wordTrace_append hprefix tailTrace_3578554
  have hstable : (prefixWord ++ tailWord_3578554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578554).length < 2 ^ (prefixWord ++ tailWord_3578554).sum := by decide
  have hdescent : baseEnd_3578554 < baseStart_3578554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578588 : List Nat := [2, 2, 5, 1, 1, 1, 3, 2, 5]
def baseStart_3578588 : Nat := 118140960795 + 3578588 * 2 ^ 59
def prefixEnd_3578588 : Nat := 4983230072969 + 3 ^ 40 * 3578588 * 2
def baseEnd_3578588 : Nat := 408341268535988887042751

theorem tailTrace_3578588 : CollatzResearch.WordTrace tailWord_3578588 prefixEnd_3578588 408341268535988887042751 := by
  unfold tailWord_3578588
  simp only [CollatzResearch.WordTrace]
  refine ⟨65260913579697162508724209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87014551439596216678298945 65260913579697162508724209)
  ·
    refine ⟨48945685184772871881543157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65260913579697162508724209 48945685184772871881543157)
    ·
      refine ⟨4588657986072456738894671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48945685184772871881543157 4588657986072456738894671)
      ·
        refine ⟨6882986979108685108342007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4588657986072456738894671 6882986979108685108342007)
        ·
          refine ⟨10324480468663027662513011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6882986979108685108342007 10324480468663027662513011)
          ·
            refine ⟨15486720702994541493769517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10324480468663027662513011 15486720702994541493769517)
            ·
              refine ⟨5807520263622953060163569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15486720702994541493769517 5807520263622953060163569)
              ·
                refine ⟨4355640197717214795122677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5807520263622953060163569 4355640197717214795122677)
                ·
                  refine ⟨408341268535988887042751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4355640197717214795122677 408341268535988887042751)
                  ·
                    rfl

theorem cell22_3578588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 5].length) (baseStart_3578588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578588 prefixEnd_3578588 := by exact prefixLift 3578588
  have htrace : WordTrace (prefixWord ++ tailWord_3578588) baseStart_3578588 baseEnd_3578588 := by
    simpa [prefixWord, tailWord_3578588, baseEnd_3578588] using wordTrace_append hprefix tailTrace_3578588
  have hstable : (prefixWord ++ tailWord_3578588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578588).length < 2 ^ (prefixWord ++ tailWord_3578588).sum := by decide
  have hdescent : baseEnd_3578588 < baseStart_3578588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578629 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 6, 4]
def baseStart_3578629 : Nat := 118140960795 + 3578629 * 2 ^ 59
def prefixEnd_3578629 : Nat := 4983230072969 + 3 ^ 40 * 3578629 * 2
def baseEnd_3578629 : Nat := 1225037840745856220853127

theorem tailTrace_3578629 : CollatzResearch.WordTrace tailWord_3578629 prefixEnd_3578629 1225037840745856220853127 := by
  unfold tailWord_3578629
  simp only [CollatzResearch.WordTrace]
  refine ⟨130523322552245789019690941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87015548368163859346460627 130523322552245789019690941)
  ·
    refine ⟨48946245957092170882384103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130523322552245789019690941 48946245957092170882384103)
    ·
      refine ⟨73419368935638256323576155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48946245957092170882384103 73419368935638256323576155)
      ·
        refine ⟨110129053403457384485364233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73419368935638256323576155 110129053403457384485364233)
        ·
          refine ⟨82596790052593038364023175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110129053403457384485364233 82596790052593038364023175)
          ·
            refine ⟨123895185078889557546034763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82596790052593038364023175 123895185078889557546034763)
            ·
              refine ⟨185842777618334336319052145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123895185078889557546034763 185842777618334336319052145)
              ·
                refine ⟨139382083213750752239289109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 185842777618334336319052145 139382083213750752239289109)
                ·
                  refine ⟨6533535150644566511216677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139382083213750752239289109 6533535150644566511216677)
                  ·
                    refine ⟨1225037840745856220853127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6533535150644566511216677 1225037840745856220853127)
                    ·
                      rfl

theorem cell22_3578629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 6, 4].length) (baseStart_3578629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578629 prefixEnd_3578629 := by exact prefixLift 3578629
  have htrace : WordTrace (prefixWord ++ tailWord_3578629) baseStart_3578629 baseEnd_3578629 := by
    simpa [prefixWord, tailWord_3578629, baseEnd_3578629] using wordTrace_append hprefix tailTrace_3578629
  have hstable : (prefixWord ++ tailWord_3578629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578629).length < 2 ^ (prefixWord ++ tailWord_3578629).sum := by decide
  have hdescent : baseEnd_3578629 < baseStart_3578629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578669 : List Nat := [1, 5, 3, 2, 2, 1, 1, 2, 1, 4]
def baseStart_3578669 : Nat := 118140960795 + 3578669 * 2 ^ 59
def prefixEnd_3578669 : Nat := 4983230072969 + 3 ^ 40 * 3578669 * 2
def baseEnd_3578669 : Nat := 1225051533563309449853005

theorem tailTrace_3578669 : CollatzResearch.WordTrace tailWord_3578669 prefixEnd_3578669 1225051533563309449853005 := by
  unfold tailWord_3578669
  simp only [CollatzResearch.WordTrace]
  refine ⟨130524781472100875851147061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87016520981400583900764707 130524781472100875851147061)
  ·
    refine ⟨12236698263009457111045037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130524781472100875851147061 12236698263009457111045037)
    ·
      refine ⟨4588761848628546416641889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12236698263009457111045037 4588761848628546416641889)
      ·
        refine ⟨3441571386471409812481417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4588761848628546416641889 3441571386471409812481417)
        ·
          refine ⟨2581178539853557359361063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3441571386471409812481417 2581178539853557359361063)
          ·
            refine ⟨3871767809780336039041595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581178539853557359361063 3871767809780336039041595)
            ·
              refine ⟨5807651714670504058562393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3871767809780336039041595 5807651714670504058562393)
              ·
                refine ⟨4355738786002878043921795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5807651714670504058562393 4355738786002878043921795)
                ·
                  refine ⟨6533608179004317065882693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4355738786002878043921795 6533608179004317065882693)
                  ·
                    refine ⟨1225051533563309449853005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6533608179004317065882693 1225051533563309449853005)
                    ·
                      rfl

theorem cell22_3578669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_3578669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578669 prefixEnd_3578669 := by exact prefixLift 3578669
  have htrace : WordTrace (prefixWord ++ tailWord_3578669) baseStart_3578669 baseEnd_3578669 := by
    simpa [prefixWord, tailWord_3578669, baseEnd_3578669] using wordTrace_append hprefix tailTrace_3578669
  have hstable : (prefixWord ++ tailWord_3578669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578669).length < 2 ^ (prefixWord ++ tailWord_3578669).sum := by decide
  have hdescent : baseEnd_3578669 < baseStart_3578669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578736 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 3, 4]
def baseStart_3578736 : Nat := 118140960795 + 3578736 * 2 ^ 59
def prefixEnd_3578736 : Nat := 4983230072969 + 3 ^ 40 * 3578736 * 2
def baseEnd_3578736 : Nat := 1225074469032543608427799

theorem tailTrace_3578736 : CollatzResearch.WordTrace tailWord_3578736 prefixEnd_3578736 1225074469032543608427799 := by
  unfold tailWord_3578736
  simp only [CollatzResearch.WordTrace]
  refine ⟨65263612581429073146918031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87018150108572097529224041 65263612581429073146918031)
  ·
    refine ⟨97895418872143609720377047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65263612581429073146918031 97895418872143609720377047)
    ·
      refine ⟨146843128308215414580565571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97895418872143609720377047 146843128308215414580565571)
      ·
        refine ⟨220264692462323121870848357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146843128308215414580565571 220264692462323121870848357)
        ·
          refine ⟨41299629836685585350784067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 220264692462323121870848357 41299629836685585350784067)
          ·
            refine ⟨61949444755028378026176101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41299629836685585350784067 61949444755028378026176101)
            ·
              refine ⟨11615520891567820879908019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61949444755028378026176101 11615520891567820879908019)
              ·
                refine ⟨17423281337351731319862029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11615520891567820879908019 17423281337351731319862029)
                ·
                  refine ⟨6533730501506899244948261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17423281337351731319862029 6533730501506899244948261)
                  ·
                    refine ⟨1225074469032543608427799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6533730501506899244948261 1225074469032543608427799)
                    ·
                      rfl

theorem cell22_3578736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 3, 4].length) (baseStart_3578736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578736 prefixEnd_3578736 := by exact prefixLift 3578736
  have htrace : WordTrace (prefixWord ++ tailWord_3578736) baseStart_3578736 baseEnd_3578736 := by
    simpa [prefixWord, tailWord_3578736, baseEnd_3578736] using wordTrace_append hprefix tailTrace_3578736
  have hstable : (prefixWord ++ tailWord_3578736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578736).length < 2 ^ (prefixWord ++ tailWord_3578736).sum := by decide
  have hdescent : baseEnd_3578736 < baseStart_3578736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578774 : List Nat := [5, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_3578774 : Nat := 118140960795 + 3578774 * 2 ^ 59
def prefixEnd_3578774 : Nat := 4983230072969 + 3 ^ 40 * 3578774 * 2
def baseEnd_3578774 : Nat := 408362492403041391992561

theorem tailTrace_3578774 : CollatzResearch.WordTrace tailWord_3578774 prefixEnd_3578774 408362492403041391992561 := by
  unfold tailWord_3578774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8158038196045029923982461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87019074091146985855812917 8158038196045029923982461)
  ·
    refine ⟨3059264323516886221493423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8158038196045029923982461 3059264323516886221493423)
    ·
      refine ⟨4588896485275329332240135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3059264323516886221493423 4588896485275329332240135)
      ·
        refine ⟨6883344727912993998360203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4588896485275329332240135 6883344727912993998360203)
        ·
          refine ⟨10325017091869490997540305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883344727912993998360203 10325017091869490997540305)
          ·
            refine ⟨7743762818902118248155229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10325017091869490997540305 7743762818902118248155229)
            ·
              refine ⟨2903911057088294343058211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7743762818902118248155229 2903911057088294343058211)
              ·
                refine ⟨4355866585632441514587317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903911057088294343058211 4355866585632441514587317)
                ·
                  refine ⟨408362492403041391992561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4355866585632441514587317 408362492403041391992561)
                  ·
                    rfl

theorem cell22_3578774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_3578774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578774 prefixEnd_3578774 := by exact prefixLift 3578774
  have htrace : WordTrace (prefixWord ++ tailWord_3578774) baseStart_3578774 baseEnd_3578774 := by
    simpa [prefixWord, tailWord_3578774, baseEnd_3578774] using wordTrace_append hprefix tailTrace_3578774
  have hstable : (prefixWord ++ tailWord_3578774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578774).length < 2 ^ (prefixWord ++ tailWord_3578774).sum := by decide
  have hdescent : baseEnd_3578774 < baseStart_3578774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578781 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 3, 6]
def baseStart_3578781 : Nat := 118140960795 + 3578781 * 2 ^ 59
def prefixEnd_3578781 : Nat := 4983230072969 + 3 ^ 40 * 3578781 * 2
def baseEnd_3578781 : Nat := 1225089873452178491052661

theorem tailTrace_3578781 : CollatzResearch.WordTrace tailWord_3578781 prefixEnd_3578781 1225089873452178491052661 := by
  unfold tailWord_3578781
  simp only [CollatzResearch.WordTrace]
  refine ⟨130528866447695118979224197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87019244298463412652816131 130528866447695118979224197)
  ·
    refine ⟨24474162458942834808604537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130528866447695118979224197 24474162458942834808604537)
    ·
      refine ⟨18355621844207126106453403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24474162458942834808604537 18355621844207126106453403)
      ·
        refine ⟨27533432766310689159680105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18355621844207126106453403 27533432766310689159680105)
        ·
          refine ⟨20650074574733016869760079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27533432766310689159680105 20650074574733016869760079)
          ·
            refine ⟨30975111862099525304640119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20650074574733016869760079 30975111862099525304640119)
            ·
              refine ⟨46462667793149287956960179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30975111862099525304640119 46462667793149287956960179)
              ·
                refine ⟨69694001689723931935440269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46462667793149287956960179 69694001689723931935440269)
                ·
                  refine ⟨26135250633646474475790101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69694001689723931935440269 26135250633646474475790101)
                  ·
                    refine ⟨1225089873452178491052661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26135250633646474475790101 1225089873452178491052661)
                    ·
                      rfl

theorem cell22_3578781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_3578781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578781 prefixEnd_3578781 := by exact prefixLift 3578781
  have htrace : WordTrace (prefixWord ++ tailWord_3578781) baseStart_3578781 baseEnd_3578781 := by
    simpa [prefixWord, tailWord_3578781, baseEnd_3578781] using wordTrace_append hprefix tailTrace_3578781
  have hstable : (prefixWord ++ tailWord_3578781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578781).length < 2 ^ (prefixWord ++ tailWord_3578781).sum := by decide
  have hdescent : baseEnd_3578781 < baseStart_3578781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578783 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 1, 5]
def baseStart_3578783 : Nat := 118140960795 + 3578783 * 2 ^ 59
def prefixEnd_3578783 : Nat := 4983230072969 + 3 ^ 40 * 3578783 * 2
def baseEnd_3578783 : Nat := 1225090558093051152502655

theorem tailTrace_3578783 : CollatzResearch.WordTrace tailWord_3578783 prefixEnd_3578783 1225090558093051152502655 := by
  unfold tailWord_3578783
  simp only [CollatzResearch.WordTrace]
  refine ⟨130528939393687873320797003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87019292929125248880531335 130528939393687873320797003)
  ·
    refine ⟨195793409090531809981195505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130528939393687873320797003 195793409090531809981195505)
    ·
      refine ⟨146845056817898857485896629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195793409090531809981195505 146845056817898857485896629)
      ·
        refine ⟨13766724076678017889302809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146845056817898857485896629 13766724076678017889302809)
        ·
          refine ⟨10325043057508513416977107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13766724076678017889302809 10325043057508513416977107)
          ·
            refine ⟨15487564586262770125465661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10325043057508513416977107 15487564586262770125465661)
            ·
              refine ⟨5807836719848538797049623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15487564586262770125465661 5807836719848538797049623)
              ·
                refine ⟨8711755079772808195574435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5807836719848538797049623 8711755079772808195574435)
                ·
                  refine ⟨13067632619659212293361653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8711755079772808195574435 13067632619659212293361653)
                  ·
                    refine ⟨1225090558093051152502655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13067632619659212293361653 1225090558093051152502655)
                    ·
                      rfl

theorem cell22_3578783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 1, 5].length) (baseStart_3578783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578783 prefixEnd_3578783 := by exact prefixLift 3578783
  have htrace : WordTrace (prefixWord ++ tailWord_3578783) baseStart_3578783 baseEnd_3578783 := by
    simpa [prefixWord, tailWord_3578783, baseEnd_3578783] using wordTrace_append hprefix tailTrace_3578783
  have hstable : (prefixWord ++ tailWord_3578783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578783).length < 2 ^ (prefixWord ++ tailWord_3578783).sum := by decide
  have hdescent : baseEnd_3578783 < baseStart_3578783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578813 : List Nat := [1, 4, 1, 2, 4, 2, 8]
def baseStart_3578813 : Nat := 118140960795 + 3578813 * 2 ^ 59
def prefixEnd_3578813 : Nat := 4983230072969 + 3 ^ 40 * 3578813 * 2
def baseEnd_3578813 : Nat := 45374104729857076824169

theorem tailTrace_3578813 : CollatzResearch.WordTrace tailWord_3578813 prefixEnd_3578813 45374104729857076824169 := by
  unfold tailWord_3578813
  simp only [CollatzResearch.WordTrace]
  refine ⟨130530033583579188444389093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87020022389052792296259395 130530033583579188444389093)
  ·
    refine ⟨24474381296921097833322955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130530033583579188444389093 24474381296921097833322955)
    ·
      refine ⟨36711571945381646749984433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24474381296921097833322955 36711571945381646749984433)
      ·
        refine ⟨27533678959036235062488325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36711571945381646749984433 27533678959036235062488325)
        ·
          refine ⟨5162564804819294074216561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27533678959036235062488325 5162564804819294074216561)
          ·
            refine ⟨3871923603614470555662421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5162564804819294074216561 3871923603614470555662421)
            ·
              refine ⟨45374104729857076824169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3871923603614470555662421 45374104729857076824169)
              ·
                rfl

theorem cell22_3578813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 2, 8].length) (baseStart_3578813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578813 prefixEnd_3578813 := by exact prefixLift 3578813
  have htrace : WordTrace (prefixWord ++ tailWord_3578813) baseStart_3578813 baseEnd_3578813 := by
    simpa [prefixWord, tailWord_3578813, baseEnd_3578813] using wordTrace_append hprefix tailTrace_3578813
  have hstable : (prefixWord ++ tailWord_3578813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578813).length < 2 ^ (prefixWord ++ tailWord_3578813).sum := by decide
  have hdescent : baseEnd_3578813 < baseStart_3578813 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578826 : List Nat := [3, 1, 2, 1, 2, 1, 1, 3, 2, 6]
def baseStart_3578826 : Nat := 118140960795 + 3578826 * 2 ^ 59
def prefixEnd_3578826 : Nat := 4983230072969 + 3 ^ 40 * 3578826 * 2
def baseEnd_3578826 : Nat := 1225105277871813373677523

theorem tailTrace_3578826 : CollatzResearch.WordTrace tailWord_3578826 prefixEnd_3578826 1225105277871813373677523 := by
  unfold tailWord_3578826
  simp only [CollatzResearch.WordTrace]
  refine ⟨32632626933133022916153083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87020338488354727776408221 32632626933133022916153083)
  ·
    refine ⟨48948940399699534374229625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32632626933133022916153083 48948940399699534374229625)
    ·
      refine ⟨36711705299774650780672219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48948940399699534374229625 36711705299774650780672219)
      ·
        refine ⟨55067557949661976171008329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36711705299774650780672219 55067557949661976171008329)
        ·
          refine ⟨41300668462246482128256247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55067557949661976171008329 41300668462246482128256247)
          ·
            refine ⟨61951002693369723192384371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41300668462246482128256247 61951002693369723192384371)
            ·
              refine ⟨92926504040054584788576557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61951002693369723192384371 92926504040054584788576557)
              ·
                refine ⟨34847439015020469295716209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92926504040054584788576557 34847439015020469295716209)
                ·
                  refine ⟨26135579261265351971787157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34847439015020469295716209 26135579261265351971787157)
                  ·
                    refine ⟨1225105277871813373677523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26135579261265351971787157 1225105277871813373677523)
                    ·
                      rfl

theorem cell22_3578826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_3578826 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578826 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578826 prefixEnd_3578826 := by exact prefixLift 3578826
  have htrace : WordTrace (prefixWord ++ tailWord_3578826) baseStart_3578826 baseEnd_3578826 := by
    simpa [prefixWord, tailWord_3578826, baseEnd_3578826] using wordTrace_append hprefix tailTrace_3578826
  have hstable : (prefixWord ++ tailWord_3578826).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578826).length < 2 ^ (prefixWord ++ tailWord_3578826).sum := by decide
  have hdescent : baseEnd_3578826 < baseStart_3578826 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578834 : List Nat := [3, 2, 2, 3, 1, 3, 2, 1, 2, 3]
def baseStart_3578834 : Nat := 118140960795 + 3578834 * 2 ^ 59
def prefixEnd_3578834 : Nat := 4983230072969 + 3 ^ 40 * 3578834 * 2
def baseEnd_3578834 : Nat := 1225108016435304019477499

theorem tailTrace_3578834 : CollatzResearch.WordTrace tailWord_3578834 prefixEnd_3578834 1225108016435304019477499 := by
  unfold tailWord_3578834
  simp only [CollatzResearch.WordTrace]
  refine ⟨32632699879125777257725889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87020533011002072687269037 32632699879125777257725889)
  ·
    refine ⟨24474524909344332943294417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32632699879125777257725889 24474524909344332943294417)
    ·
      refine ⟨18355893682008249707470813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24474524909344332943294417 18355893682008249707470813)
      ·
        refine ⟨6883460130753093640301555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18355893682008249707470813 6883460130753093640301555)
        ·
          refine ⟨10325190196129640460452333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883460130753093640301555 10325190196129640460452333)
          ·
            refine ⟨3871946323548615172669625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10325190196129640460452333 3871946323548615172669625)
            ·
              refine ⟨2903959742661461379502219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3871946323548615172669625 2903959742661461379502219)
              ·
                refine ⟨4355939613992192069253329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2903959742661461379502219 4355939613992192069253329)
                ·
                  refine ⟨3266954710494144051939997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4355939613992192069253329 3266954710494144051939997)
                  ·
                    refine ⟨1225108016435304019477499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3266954710494144051939997 1225108016435304019477499)
                    ·
                      rfl

theorem cell22_3578834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_3578834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578834 prefixEnd_3578834 := by exact prefixLift 3578834
  have htrace : WordTrace (prefixWord ++ tailWord_3578834) baseStart_3578834 baseEnd_3578834 := by
    simpa [prefixWord, tailWord_3578834, baseEnd_3578834] using wordTrace_append hprefix tailTrace_3578834
  have hstable : (prefixWord ++ tailWord_3578834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578834).length < 2 ^ (prefixWord ++ tailWord_3578834).sum := by decide
  have hdescent : baseEnd_3578834 < baseStart_3578834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578868 : List Nat := [2, 6, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_3578868 : Nat := 118140960795 + 3578868 * 2 ^ 59
def prefixEnd_3578868 : Nat := 4983230072969 + 3 ^ 40 * 3578868 * 2
def baseEnd_3578868 : Nat := 1225119655330139264127395

theorem tailTrace_3578868 : CollatzResearch.WordTrace tailWord_3578868 prefixEnd_3578868 1225119655330139264127395 := by
  unfold tailWord_3578868
  simp only [CollatzResearch.WordTrace]
  refine ⟨65266019799189966418820629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87021359732253288558427505 65266019799189966418820629)
  ·
    refine ⟨3059344678087029675882217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65266019799189966418820629 3059344678087029675882217)
    ·
      refine ⟨2294508508565272256911663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3059344678087029675882217 2294508508565272256911663)
      ·
        refine ⟨3441762762847908385367495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2294508508565272256911663 3441762762847908385367495)
        ·
          refine ⟨5162644144271862578051243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3441762762847908385367495 5162644144271862578051243)
          ·
            refine ⟨7743966216407793867076865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162644144271862578051243 7743966216407793867076865)
            ·
              refine ⟨5807974662305845400307649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7743966216407793867076865 5807974662305845400307649)
              ·
                refine ⟨4355980996729384050230737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5807974662305845400307649 4355980996729384050230737)
                ·
                  refine ⟨3266985747547038037673053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4355980996729384050230737 3266985747547038037673053)
                  ·
                    refine ⟨1225119655330139264127395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3266985747547038037673053 1225119655330139264127395)
                    ·
                      rfl

theorem cell22_3578868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_3578868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578868 prefixEnd_3578868 := by exact prefixLift 3578868
  have htrace : WordTrace (prefixWord ++ tailWord_3578868) baseStart_3578868 baseEnd_3578868 := by
    simpa [prefixWord, tailWord_3578868, baseEnd_3578868] using wordTrace_append hprefix tailTrace_3578868
  have hstable : (prefixWord ++ tailWord_3578868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578868).length < 2 ^ (prefixWord ++ tailWord_3578868).sum := by decide
  have hdescent : baseEnd_3578868 < baseStart_3578868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578888 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 3, 4]
def baseStart_3578888 : Nat := 118140960795 + 3578888 * 2 ^ 59
def prefixEnd_3578888 : Nat := 4983230072969 + 3 ^ 40 * 3578888 * 2
def baseEnd_3578888 : Nat := 1225126501738865878627333

theorem tailTrace_3578888 : CollatzResearch.WordTrace tailWord_3578888 prefixEnd_3578888 1225126501738865878627333 := by
  unfold tailWord_3578888
  simp only [CollatzResearch.WordTrace]
  refine ⟨65266384529153738126684659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87021846038871650835579545 65266384529153738126684659)
  ·
    refine ⟨97899576793730607190026989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65266384529153738126684659 97899576793730607190026989)
    ·
      refine ⟨36712341297648977696260121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97899576793730607190026989 36712341297648977696260121)
      ·
        refine ⟨27534255973236733272195091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36712341297648977696260121 27534255973236733272195091)
        ·
          refine ⟨41301383959855099908292637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27534255973236733272195091 41301383959855099908292637)
          ·
            refine ⟨15488018984945662465609739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41301383959855099908292637 15488018984945662465609739)
            ·
              refine ⟨23232028477418493698414609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15488018984945662465609739 23232028477418493698414609)
              ·
                refine ⟨17424021358063870273810957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23232028477418493698414609 17424021358063870273810957)
                ·
                  refine ⟨6534008009273951352679109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17424021358063870273810957 6534008009273951352679109)
                  ·
                    refine ⟨1225126501738865878627333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6534008009273951352679109 1225126501738865878627333)
                    ·
                      rfl

theorem cell22_3578888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_3578888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578888 prefixEnd_3578888 := by exact prefixLift 3578888
  have htrace : WordTrace (prefixWord ++ tailWord_3578888) baseStart_3578888 baseEnd_3578888 := by
    simpa [prefixWord, tailWord_3578888, baseEnd_3578888] using wordTrace_append hprefix tailTrace_3578888
  have hstable : (prefixWord ++ tailWord_3578888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578888).length < 2 ^ (prefixWord ++ tailWord_3578888).sum := by decide
  have hdescent : baseEnd_3578888 < baseStart_3578888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578903 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 8]
def baseStart_3578903 : Nat := 118140960795 + 3578903 * 2 ^ 59
def prefixEnd_3578903 : Nat := 4983230072969 + 3 ^ 40 * 3578903 * 2
def baseEnd_3578903 : Nat := 408377212181803613167429

theorem tailTrace_3578903 : CollatzResearch.WordTrace tailWord_3578903 prefixEnd_3578903 408377212181803613167429 := by
  unfold tailWord_3578903
  simp only [CollatzResearch.WordTrace]
  refine ⟨130533316153253133815165363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87022210768835422543443575 130533316153253133815165363)
  ·
    refine ⟨195799974229879700722748045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130533316153253133815165363 195799974229879700722748045)
    ·
      refine ⟨73424990336204887771030517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195799974229879700722748045 73424990336204887771030517)
      ·
        refine ⟨6883592844019208228534111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73424990336204887771030517 6883592844019208228534111)
        ·
          refine ⟨10325389266028812342801167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6883592844019208228534111 10325389266028812342801167)
          ·
            refine ⟨15488083899043218514201751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10325389266028812342801167 15488083899043218514201751)
            ·
              refine ⟨23232125848564827771302627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15488083899043218514201751 23232125848564827771302627)
              ·
                refine ⟨34848188772847241656953941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23232125848564827771302627 34848188772847241656953941)
                ·
                  refine ⟨408377212181803613167429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34848188772847241656953941 408377212181803613167429)
                  ·
                    rfl

theorem cell22_3578903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 8].length) (baseStart_3578903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578903 prefixEnd_3578903 := by exact prefixLift 3578903
  have htrace : WordTrace (prefixWord ++ tailWord_3578903) baseStart_3578903 baseEnd_3578903 := by
    simpa [prefixWord, tailWord_3578903, baseEnd_3578903] using wordTrace_append hprefix tailTrace_3578903
  have hstable : (prefixWord ++ tailWord_3578903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578903).length < 2 ^ (prefixWord ++ tailWord_3578903).sum := by decide
  have hdescent : baseEnd_3578903 < baseStart_3578903 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578922 : List Nat := [3, 1, 4, 1, 3, 1, 1, 3, 1, 4]
def baseStart_3578922 : Nat := 118140960795 + 3578922 * 2 ^ 59
def prefixEnd_3578922 : Nat := 4983230072969 + 3 ^ 40 * 3578922 * 2
def baseEnd_3578922 : Nat := 1225138140633701123277229

theorem tailTrace_3578922 : CollatzResearch.WordTrace tailWord_3578922 prefixEnd_3578922 1225138140633701123277229 := by
  unfold tailWord_3578922
  simp only [CollatzResearch.WordTrace]
  refine ⟨32633502285046075015026755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87022672760122866706738013 32633502285046075015026755)
  ·
    refine ⟨48950253427569112522540133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32633502285046075015026755 48950253427569112522540133)
    ·
      refine ⟨9178172517669208597976275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48950253427569112522540133 9178172517669208597976275)
      ·
        refine ⟨13767258776503812896964413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9178172517669208597976275 13767258776503812896964413)
        ·
          refine ⟨5162722041188929836361655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13767258776503812896964413 5162722041188929836361655)
          ·
            refine ⟨7744083061783394754542483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5162722041188929836361655 7744083061783394754542483)
            ·
              refine ⟨11616124592675092131813725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7744083061783394754542483 11616124592675092131813725)
              ·
                refine ⟨4356046722253159549430147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11616124592675092131813725 4356046722253159549430147)
                ·
                  refine ⟨6534070083379739324145221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4356046722253159549430147 6534070083379739324145221)
                  ·
                    refine ⟨1225138140633701123277229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6534070083379739324145221 1225138140633701123277229)
                    ·
                      rfl

theorem cell22_3578922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_3578922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578922 prefixEnd_3578922 := by exact prefixLift 3578922
  have htrace : WordTrace (prefixWord ++ tailWord_3578922) baseStart_3578922 baseEnd_3578922 := by
    simpa [prefixWord, tailWord_3578922, baseEnd_3578922] using wordTrace_append hprefix tailTrace_3578922
  have hstable : (prefixWord ++ tailWord_3578922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578922).length < 2 ^ (prefixWord ++ tailWord_3578922).sum := by decide
  have hdescent : baseEnd_3578922 < baseStart_3578922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578933 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 4, 4]
def baseStart_3578933 : Nat := 118140960795 + 3578933 * 2 ^ 59
def prefixEnd_3578933 : Nat := 4983230072969 + 3 ^ 40 * 3578933 * 2
def baseEnd_3578933 : Nat := 1225141906158500761252195

theorem tailTrace_3578933 : CollatzResearch.WordTrace tailWord_3578933 prefixEnd_3578933 1225141906158500761252195 := by
  unfold tailWord_3578933
  simp only [CollatzResearch.WordTrace]
  refine ⟨130534410343144448938757453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87022940228762965959171635 130534410343144448938757453)
  ·
    refine ⟨48950403878679168352034045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130534410343144448938757453 48950403878679168352034045)
    ·
      refine ⟨18356401454504688132012767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48950403878679168352034045 18356401454504688132012767)
      ·
        refine ⟨27534602181757032198019151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18356401454504688132012767 27534602181757032198019151)
        ·
          refine ⟨41301903272635548297028727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27534602181757032198019151 41301903272635548297028727)
          ·
            refine ⟨61952854908953322445543091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41301903272635548297028727 61952854908953322445543091)
            ·
              refine ⟨92929282363429983668314637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61952854908953322445543091 92929282363429983668314637)
              ·
                refine ⟨34848480886286243875617989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92929282363429983668314637 34848480886286243875617989)
                ·
                  refine ⟨6534090166178670726678373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34848480886286243875617989 6534090166178670726678373)
                  ·
                    refine ⟨1225141906158500761252195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6534090166178670726678373 1225141906158500761252195)
                    ·
                      rfl

theorem cell22_3578933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_3578933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578933 prefixEnd_3578933 := by exact prefixLift 3578933
  have htrace : WordTrace (prefixWord ++ tailWord_3578933) baseStart_3578933 baseEnd_3578933 := by
    simpa [prefixWord, tailWord_3578933, baseEnd_3578933] using wordTrace_append hprefix tailTrace_3578933
  have hstable : (prefixWord ++ tailWord_3578933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578933).length < 2 ^ (prefixWord ++ tailWord_3578933).sum := by decide
  have hdescent : baseEnd_3578933 < baseStart_3578933 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3578952 : List Nat := [2, 1, 3, 1, 1, 1, 7, 1, 2, 3]
def baseStart_3578952 : Nat := 118140960795 + 3578952 * 2 ^ 59
def prefixEnd_3578952 : Nat := 4983230072969 + 3 ^ 40 * 3578952 * 2
def baseEnd_3578952 : Nat := 1225148410246791045027137

theorem tailTrace_3578952 : CollatzResearch.WordTrace tailWord_3578952 prefixEnd_3578952 1225148410246791045027137 := by
  unfold tailWord_3578952
  simp only [CollatzResearch.WordTrace]
  refine ⟨65267551665037807591849555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87023402220050410122466073 65267551665037807591849555)
  ·
    refine ⟨97901327497556711387774333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65267551665037807591849555 97901327497556711387774333)
    ·
      refine ⟨36712997811583766770415375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97901327497556711387774333 36712997811583766770415375)
      ·
        refine ⟨55069496717375650155623063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36712997811583766770415375 55069496717375650155623063)
        ·
          refine ⟨82604245076063475233434595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55069496717375650155623063 82604245076063475233434595)
          ·
            refine ⟨123906367614095212850151893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82604245076063475233434595 123906367614095212850151893)
            ·
              refine ⟨2904055490955356551175435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 123906367614095212850151893 2904055490955356551175435)
              ·
                refine ⟨4356083236433034826763153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904055490955356551175435 4356083236433034826763153)
                ·
                  refine ⟨3267062427324776120072365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4356083236433034826763153 3267062427324776120072365)
                  ·
                    refine ⟨1225148410246791045027137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3267062427324776120072365 1225148410246791045027137)
                    ·
                      rfl

theorem cell22_3578952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_3578952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3578952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3578952 prefixEnd_3578952 := by exact prefixLift 3578952
  have htrace : WordTrace (prefixWord ++ tailWord_3578952) baseStart_3578952 baseEnd_3578952 := by
    simpa [prefixWord, tailWord_3578952, baseEnd_3578952] using wordTrace_append hprefix tailTrace_3578952
  have hstable : (prefixWord ++ tailWord_3578952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3578952).length < 2 ^ (prefixWord ++ tailWord_3578952).sum := by decide
  have hdescent : baseEnd_3578952 < baseStart_3578952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3578952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579008 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 2, 5]
def baseStart_3579008 : Nat := 118140960795 + 3579008 * 2 ^ 59
def prefixEnd_3579008 : Nat := 4983230072969 + 3 ^ 40 * 3579008 * 2
def baseEnd_3579008 : Nat := 1225167580191225565626965

theorem tailTrace_3579008 : CollatzResearch.WordTrace tailWord_3579008 prefixEnd_3579008 1225167580191225565626965 := by
  unfold tailWord_3579008
  simp only [CollatzResearch.WordTrace]
  refine ⟨65268572908936368373868839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87024763878581824498491785 65268572908936368373868839)
  ·
    refine ⟨97902859363404552560803259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65268572908936368373868839 97902859363404552560803259)
    ·
      refine ⟨146854289045106828841204889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97902859363404552560803259 146854289045106828841204889)
      ·
        refine ⟨110140716783830121630903667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146854289045106828841204889 110140716783830121630903667)
        ·
          refine ⟨165211075175745182446355501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110140716783830121630903667 165211075175745182446355501)
          ·
            refine ⟨61954153190904443417383313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165211075175745182446355501 61954153190904443417383313)
            ·
              refine ⟨46465614893178332563037485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61954153190904443417383313 46465614893178332563037485)
              ·
                refine ⟨17424605584941874711139057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46465614893178332563037485 17424605584941874711139057)
                ·
                  refine ⟨13068454188706406033354293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17424605584941874711139057 13068454188706406033354293)
                  ·
                    refine ⟨1225167580191225565626965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13068454188706406033354293 1225167580191225565626965)
                    ·
                      rfl

theorem cell22_3579008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 2, 5].length) (baseStart_3579008 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579008 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579008 prefixEnd_3579008 := by exact prefixLift 3579008
  have htrace : WordTrace (prefixWord ++ tailWord_3579008) baseStart_3579008 baseEnd_3579008 := by
    simpa [prefixWord, tailWord_3579008, baseEnd_3579008] using wordTrace_append hprefix tailTrace_3579008
  have hstable : (prefixWord ++ tailWord_3579008).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579008).length < 2 ^ (prefixWord ++ tailWord_3579008).sum := by decide
  have hdescent : baseEnd_3579008 < baseStart_3579008 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579104 : List Nat := [2, 1, 1, 3, 1, 6, 1, 2, 2, 3]
def baseStart_3579104 : Nat := 118140960795 + 3579104 * 2 ^ 59
def prefixEnd_3579104 : Nat := 4983230072969 + 3 ^ 40 * 3579104 * 2
def baseEnd_3579104 : Nat := 1225200442953113315226671

theorem tailTrace_3579104 : CollatzResearch.WordTrace tailWord_3579104 prefixEnd_3579104 1225200442953113315226671 := by
  unfold tailWord_3579104
  simp only [CollatzResearch.WordTrace]
  refine ⟨65270323612762472571616183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87027098150349963428821577 65270323612762472571616183)
  ·
    refine ⟨97905485419143708857424275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65270323612762472571616183 97905485419143708857424275)
    ·
      refine ⟨146858228128715563286136413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97905485419143708857424275 146858228128715563286136413)
      ·
        refine ⟨55071835548268336232301155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 146858228128715563286136413 55071835548268336232301155)
        ·
          refine ⟨82607753322402504348451733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55071835548268336232301155 82607753322402504348451733)
          ·
            refine ⟨3872238436987617391333675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82607753322402504348451733 3872238436987617391333675)
            ·
              refine ⟨5808357655481426087000513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872238436987617391333675 5808357655481426087000513)
              ·
                refine ⟨4356268241611069565250385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5808357655481426087000513 4356268241611069565250385)
                ·
                  refine ⟨3267201181208302173937789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4356268241611069565250385 3267201181208302173937789)
                  ·
                    refine ⟨1225200442953113315226671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3267201181208302173937789 1225200442953113315226671)
                    ·
                      rfl

theorem cell22_3579104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 2, 2, 3].length) (baseStart_3579104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579104 prefixEnd_3579104 := by exact prefixLift 3579104
  have htrace : WordTrace (prefixWord ++ tailWord_3579104) baseStart_3579104 baseEnd_3579104 := by
    simpa [prefixWord, tailWord_3579104, baseEnd_3579104] using wordTrace_append hprefix tailTrace_3579104
  have hstable : (prefixWord ++ tailWord_3579104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579104).length < 2 ^ (prefixWord ++ tailWord_3579104).sum := by decide
  have hdescent : baseEnd_3579104 < baseStart_3579104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579134 : List Nat := [4, 2, 2, 1, 1, 4, 2, 6]
def baseStart_3579134 : Nat := 118140960795 + 3579134 * 2 ^ 59
def prefixEnd_3579134 : Nat := 4983230072969 + 3 ^ 40 * 3579134 * 2
def baseEnd_3579134 : Nat := 136134523618467026330731

theorem tailTrace_3579134 : CollatzResearch.WordTrace tailWord_3579134 prefixEnd_3579134 136134523618467026330731 := by
  unfold tailWord_3579134
  simp only [CollatzResearch.WordTrace]
  refine ⟨16317717676927032533353057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87027827610277506844549637 16317717676927032533353057)
  ·
    refine ⟨12238288257695274400014793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16317717676927032533353057 12238288257695274400014793)
    ·
      refine ⟨9178716193271455800011095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12238288257695274400014793 9178716193271455800011095)
      ·
        refine ⟨13768074289907183700016643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9178716193271455800011095 13768074289907183700016643)
        ·
          refine ⟨20652111434860775550024965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13768074289907183700016643 20652111434860775550024965)
          ·
            refine ⟨3872270894036395415629681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20652111434860775550024965 3872270894036395415629681)
            ·
              refine ⟨2904203170527296561722261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3872270894036395415629681 2904203170527296561722261)
              ·
                refine ⟨136134523618467026330731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2904203170527296561722261 136134523618467026330731)
                ·
                  rfl

theorem cell22_3579134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_3579134 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579134 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579134 prefixEnd_3579134 := by exact prefixLift 3579134
  have htrace : WordTrace (prefixWord ++ tailWord_3579134) baseStart_3579134 baseEnd_3579134 := by
    simpa [prefixWord, tailWord_3579134, baseEnd_3579134] using wordTrace_append hprefix tailTrace_3579134
  have hstable : (prefixWord ++ tailWord_3579134).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579134).length < 2 ^ (prefixWord ++ tailWord_3579134).sum := by decide
  have hdescent : baseEnd_3579134 < baseStart_3579134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579239 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 1, 5]
def baseStart_3579239 : Nat := 118140960795 + 3579239 * 2 ^ 59
def prefixEnd_3579239 : Nat := 4983230072969 + 3 ^ 40 * 3579239 * 2
def baseEnd_3579239 : Nat := 1225246656212017963101257

theorem tailTrace_3579239 : CollatzResearch.WordTrace tailWord_3579239 prefixEnd_3579239 1225246656212017963101257 := by
  unfold tailWord_3579239
  simp only [CollatzResearch.WordTrace]
  refine ⟨130545571080035863199396771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87030380720023908799597847 130545571080035863199396771)
  ·
    refine ⟨195818356620053794799095157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130545571080035863199396771 195818356620053794799095157)
    ·
      refine ⟨18357970933130043262415171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195818356620053794799095157 18357970933130043262415171)
      ·
        refine ⟨27536956399695064893622757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18357970933130043262415171 27536956399695064893622757)
        ·
          refine ⟨5163179324942824667554267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27536956399695064893622757 5163179324942824667554267)
          ·
            refine ⟨7744768987414237001331401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5163179324942824667554267 7744768987414237001331401)
            ·
              refine ⟨5808576740560677750998551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7744768987414237001331401 5808576740560677750998551)
              ·
                refine ⟨8712865110841016626497827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5808576740560677750998551 8712865110841016626497827)
                ·
                  refine ⟨13069297666261524939746741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8712865110841016626497827 13069297666261524939746741)
                  ·
                    refine ⟨1225246656212017963101257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13069297666261524939746741 1225246656212017963101257)
                    ·
                      rfl

theorem cell22_3579239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_3579239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579239 prefixEnd_3579239 := by exact prefixLift 3579239
  have htrace : WordTrace (prefixWord ++ tailWord_3579239) baseStart_3579239 baseEnd_3579239 := by
    simpa [prefixWord, tailWord_3579239, baseEnd_3579239] using wordTrace_append hprefix tailTrace_3579239
  have hstable : (prefixWord ++ tailWord_3579239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579239).length < 2 ^ (prefixWord ++ tailWord_3579239).sum := by decide
  have hdescent : baseEnd_3579239 < baseStart_3579239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579273 : List Nat := [1, 2, 1, 1, 8, 1, 1, 2, 2, 3]
def baseStart_3579273 : Nat := 118140960795 + 3579273 * 2 ^ 59
def prefixEnd_3579273 : Nat := 4983230072969 + 3 ^ 40 * 3579273 * 2
def baseEnd_3579273 : Nat := 1225258295106853207751153

theorem tailTrace_3579273 : CollatzResearch.WordTrace tailWord_3579273 prefixEnd_3579273 1225258295106853207751153 := by
  unfold tailWord_3579273
  simp only [CollatzResearch.WordTrace]
  refine ⟨130546811161912687006134473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87031207441275124670756315 130546811161912687006134473)
  ·
    refine ⟨97910108371434515254600855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130546811161912687006134473 97910108371434515254600855)
    ·
      refine ⟨146865162557151772881901283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97910108371434515254600855 146865162557151772881901283)
      ·
        refine ⟨220297743835727659322851925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146865162557151772881901283 220297743835727659322851925)
        ·
          refine ⟨2581614185574933507689671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 220297743835727659322851925 2581614185574933507689671)
          ·
            refine ⟨3872421278362400261534507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2581614185574933507689671 3872421278362400261534507)
            ·
              refine ⟨5808631917543600392301761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872421278362400261534507 5808631917543600392301761)
              ·
                refine ⟨4356473938157700294226321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5808631917543600392301761 4356473938157700294226321)
                ·
                  refine ⟨3267355453618275220669741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4356473938157700294226321 3267355453618275220669741)
                  ·
                    refine ⟨1225258295106853207751153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3267355453618275220669741 1225258295106853207751153)
                    ·
                      rfl

theorem cell22_3579273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 2, 2, 3].length) (baseStart_3579273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579273 prefixEnd_3579273 := by exact prefixLift 3579273
  have htrace : WordTrace (prefixWord ++ tailWord_3579273) baseStart_3579273 baseEnd_3579273 := by
    simpa [prefixWord, tailWord_3579273, baseEnd_3579273] using wordTrace_append hprefix tailTrace_3579273
  have hstable : (prefixWord ++ tailWord_3579273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579273).length < 2 ^ (prefixWord ++ tailWord_3579273).sum := by decide
  have hdescent : baseEnd_3579273 < baseStart_3579273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579348 : List Nat := [2, 4, 1, 2, 3, 2, 2, 1, 5]
def baseStart_3579348 : Nat := 118140960795 + 3579348 * 2 ^ 59
def prefixEnd_3579348 : Nat := 4983230072969 + 3 ^ 40 * 3579348 * 2
def baseEnd_3579348 : Nat := 408427989713192670708641

theorem tailTrace_3579348 : CollatzResearch.WordTrace tailWord_3579348 prefixEnd_3579348 408427989713192670708641 := by
  unfold tailWord_3579348
  simp only [CollatzResearch.WordTrace]
  refine ⟨65274773318320487407557349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87033031091093983210076465 65274773318320487407557349)
  ·
    refine ⟨12239019997185091388917003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65274773318320487407557349 12239019997185091388917003)
    ·
      refine ⟨18358529995777637083375505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12239019997185091388917003 18358529995777637083375505)
      ·
        refine ⟨13768897496833227812531629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18358529995777637083375505 13768897496833227812531629)
        ·
          refine ⟨5163336561312460429699361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13768897496833227812531629 5163336561312460429699361)
          ·
            refine ⟨3872502420984345322274521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5163336561312460429699361 3872502420984345322274521)
            ·
              refine ⟨2904376815738258991705891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3872502420984345322274521 2904376815738258991705891)
              ·
                refine ⟨4356565223607388487558837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904376815738258991705891 4356565223607388487558837)
                ·
                  refine ⟨408427989713192670708641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4356565223607388487558837 408427989713192670708641)
                  ·
                    rfl

theorem cell22_3579348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_3579348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579348 prefixEnd_3579348 := by exact prefixLift 3579348
  have htrace : WordTrace (prefixWord ++ tailWord_3579348) baseStart_3579348 baseEnd_3579348 := by
    simpa [prefixWord, tailWord_3579348, baseEnd_3579348] using wordTrace_append hprefix tailTrace_3579348
  have hstable : (prefixWord ++ tailWord_3579348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579348).length < 2 ^ (prefixWord ++ tailWord_3579348).sum := by decide
  have hdescent : baseEnd_3579348 < baseStart_3579348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579361 : List Nat := [1, 2, 3, 1, 2, 5, 1, 2, 1, 4]
def baseStart_3579361 : Nat := 118140960795 + 3579361 * 2 ^ 59
def prefixEnd_3579361 : Nat := 4983230072969 + 3 ^ 40 * 3579361 * 2
def baseEnd_3579361 : Nat := 1225288419305250311550883

theorem tailTrace_3579361 : CollatzResearch.WordTrace tailWord_3579361 prefixEnd_3579361 1225288419305250311550883 := by
  unfold tailWord_3579361
  simp only [CollatzResearch.WordTrace]
  refine ⟨130550020785593878035337937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87033347190395918690225291 130550020785593878035337937)
  ·
    refine ⟨97912515589195408526503453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130550020785593878035337937 97912515589195408526503453)
    ·
      refine ⟨36717193345948278197438795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97912515589195408526503453 36717193345948278197438795)
      ·
        refine ⟨55075790018922417296158193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36717193345948278197438795 55075790018922417296158193)
        ·
          refine ⟨41306842514191812972118645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55075790018922417296158193 41306842514191812972118645)
          ·
            refine ⟨3872516485705482466136123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41306842514191812972118645 3872516485705482466136123)
            ·
              refine ⟨5808774728558223699204185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872516485705482466136123 5808774728558223699204185)
              ·
                refine ⟨4356581046418667774403139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5808774728558223699204185 4356581046418667774403139)
                ·
                  refine ⟨6534871569628001661604709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4356581046418667774403139 6534871569628001661604709)
                  ·
                    refine ⟨1225288419305250311550883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6534871569628001661604709 1225288419305250311550883)
                    ·
                      rfl

theorem cell22_3579361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 2, 1, 4].length) (baseStart_3579361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579361 prefixEnd_3579361 := by exact prefixLift 3579361
  have htrace : WordTrace (prefixWord ++ tailWord_3579361) baseStart_3579361 baseEnd_3579361 := by
    simpa [prefixWord, tailWord_3579361, baseEnd_3579361] using wordTrace_append hprefix tailTrace_3579361
  have hstable : (prefixWord ++ tailWord_3579361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579361).length < 2 ^ (prefixWord ++ tailWord_3579361).sum := by decide
  have hdescent : baseEnd_3579361 < baseStart_3579361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579374 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_3579374 : Nat := 118140960795 + 3579374 * 2 ^ 59
def prefixEnd_3579374 : Nat := 4983230072969 + 3 ^ 40 * 3579374 * 2
def baseEnd_3579374 : Nat := 1225292869470922610975843

theorem tailTrace_3579374 : CollatzResearch.WordTrace tailWord_3579374 prefixEnd_3579374 1225292869470922610975843 := by
  unfold tailWord_3579374
  simp only [CollatzResearch.WordTrace]
  refine ⟨16318811866818347656945147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87033663289697854170374117 16318811866818347656945147)
  ·
    refine ⟨24478217800227521485417721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16318811866818347656945147 24478217800227521485417721)
    ·
      refine ⟨18358663350170641114063291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24478217800227521485417721 18358663350170641114063291)
      ·
        refine ⟨27537995025255961671094937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18358663350170641114063291 27537995025255961671094937)
        ·
          refine ⟨20653496268941971253321203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27537995025255961671094937 20653496268941971253321203)
          ·
            refine ⟨30980244403412956879981805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20653496268941971253321203 30980244403412956879981805)
            ·
              refine ⟨11617591651279858829993177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30980244403412956879981805 11617591651279858829993177)
              ·
                refine ⟨8713193738459894122494883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11617591651279858829993177 8713193738459894122494883)
                ·
                  refine ⟨13069790607689841183742325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8713193738459894122494883 13069790607689841183742325)
                  ·
                    refine ⟨1225292869470922610975843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13069790607689841183742325 1225292869470922610975843)
                    ·
                      rfl

theorem cell22_3579374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_3579374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579374 prefixEnd_3579374 := by exact prefixLift 3579374
  have htrace : WordTrace (prefixWord ++ tailWord_3579374) baseStart_3579374 baseEnd_3579374 := by
    simpa [prefixWord, tailWord_3579374, baseEnd_3579374] using wordTrace_append hprefix tailTrace_3579374
  have hstable : (prefixWord ++ tailWord_3579374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579374).length < 2 ^ (prefixWord ++ tailWord_3579374).sum := by decide
  have hdescent : baseEnd_3579374 < baseStart_3579374 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579378 : List Nat := [3, 2, 1, 4, 1, 2, 3, 1, 1, 4]
def baseStart_3579378 : Nat := 118140960795 + 3579378 * 2 ^ 59
def prefixEnd_3579378 : Nat := 4983230072969 + 3 ^ 40 * 3579378 * 2
def baseEnd_3579378 : Nat := 1225294238752667933875831

theorem tailTrace_3579378 : CollatzResearch.WordTrace tailWord_3579378 prefixEnd_3579378 1225294238752667933875831 := by
  unfold tailWord_3579378
  simp only [CollatzResearch.WordTrace]
  refine ⟨32637660206633072484676697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87033760551021526625804525 32637660206633072484676697)
  ·
    refine ⟨24478245154974804363507523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32637660206633072484676697 24478245154974804363507523)
    ·
      refine ⟨36717367732462206545261285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24478245154974804363507523 36717367732462206545261285)
      ·
        refine ⟨6884506449836663727236491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36717367732462206545261285 6884506449836663727236491)
        ·
          refine ⟨10326759674754995590854737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6884506449836663727236491 10326759674754995590854737)
          ·
            refine ⟨7745069756066246693141053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10326759674754995590854737 7745069756066246693141053)
            ·
              refine ⟨2904401158524842509927895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7745069756066246693141053 2904401158524842509927895)
              ·
                refine ⟨4356601737787263764891843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904401158524842509927895 4356601737787263764891843)
                ·
                  refine ⟨6534902606680895647337765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4356601737787263764891843 6534902606680895647337765)
                  ·
                    refine ⟨1225294238752667933875831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6534902606680895647337765 1225294238752667933875831)
                    ·
                      rfl

theorem cell22_3579378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 3, 1, 1, 4].length) (baseStart_3579378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579378 prefixEnd_3579378 := by exact prefixLift 3579378
  have htrace : WordTrace (prefixWord ++ tailWord_3579378) baseStart_3579378 baseEnd_3579378 := by
    simpa [prefixWord, tailWord_3579378, baseEnd_3579378] using wordTrace_append hprefix tailTrace_3579378
  have hstable : (prefixWord ++ tailWord_3579378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579378).length < 2 ^ (prefixWord ++ tailWord_3579378).sum := by decide
  have hdescent : baseEnd_3579378 < baseStart_3579378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579389 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 2, 4]
def baseStart_3579389 : Nat := 118140960795 + 3579389 * 2 ^ 59
def prefixEnd_3579389 : Nat := 4983230072969 + 3 ^ 40 * 3579389 * 2
def baseEnd_3579389 : Nat := 1225298004277467571850797

theorem tailTrace_3579389 : CollatzResearch.WordTrace tailWord_3579389 prefixEnd_3579389 1225298004277467571850797 := by
  unfold tailWord_3579389
  simp only [CollatzResearch.WordTrace]
  refine ⟨130551042029492438817357221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87034028019661625878238147 130551042029492438817357221)
  ·
    refine ⟨24478320380529832278254479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130551042029492438817357221 24478320380529832278254479)
    ·
      refine ⟨36717480570794748417381719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24478320380529832278254479 36717480570794748417381719)
      ·
        refine ⟨55076220856192122626072579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36717480570794748417381719 55076220856192122626072579)
        ·
          refine ⟨82614331284288183939108869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55076220856192122626072579 82614331284288183939108869)
          ·
            refine ⟨15490187115804034488582913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82614331284288183939108869 15490187115804034488582913)
            ·
              refine ⟨11617640336853025866437185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15490187115804034488582913 11617640336853025866437185)
              ·
                refine ⟨8713230252639769399827889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11617640336853025866437185 8713230252639769399827889)
                ·
                  refine ⟨6534922689479827049870917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8713230252639769399827889 6534922689479827049870917)
                  ·
                    refine ⟨1225298004277467571850797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6534922689479827049870917 1225298004277467571850797)
                    ·
                      rfl

theorem cell22_3579389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_3579389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579389 prefixEnd_3579389 := by exact prefixLift 3579389
  have htrace : WordTrace (prefixWord ++ tailWord_3579389) baseStart_3579389 baseEnd_3579389 := by
    simpa [prefixWord, tailWord_3579389, baseEnd_3579389] using wordTrace_append hprefix tailTrace_3579389
  have hstable : (prefixWord ++ tailWord_3579389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579389).length < 2 ^ (prefixWord ++ tailWord_3579389).sum := by decide
  have hdescent : baseEnd_3579389 < baseStart_3579389 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579449 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 7]
def baseStart_3579449 : Nat := 118140960795 + 3579449 * 2 ^ 59
def prefixEnd_3579449 : Nat := 4983230072969 + 3 ^ 40 * 3579449 * 2
def baseEnd_3579449 : Nat := 408439514501215805116871

theorem tailTrace_3579449 : CollatzResearch.WordTrace tailWord_3579449 prefixEnd_3579449 408439514501215805116871 := by
  unfold tailWord_3579449
  simp only [CollatzResearch.WordTrace]
  refine ⟨130553230409275069064541401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87035486939516712709694267 130553230409275069064541401)
  ·
    refine ⟨97914922806956301798406051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130553230409275069064541401 97914922806956301798406051)
    ·
      refine ⟨146872384210434452697609077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97914922806956301798406051 146872384210434452697609077)
      ·
        refine ⟨13769286019728229940400851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146872384210434452697609077 13769286019728229940400851)
        ·
          refine ⟨20653929029592344910601277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13769286019728229940400851 20653929029592344910601277)
          ·
            refine ⟨7745223386097129341475479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20653929029592344910601277 7745223386097129341475479)
            ·
              refine ⟨11617835079145694012213219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7745223386097129341475479 11617835079145694012213219)
              ·
                refine ⟨17426752618718541018319829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11617835079145694012213219 17426752618718541018319829)
                ·
                  refine ⟨408439514501215805116871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17426752618718541018319829 408439514501215805116871)
                  ·
                    rfl

theorem cell22_3579449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 7].length) (baseStart_3579449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579449 prefixEnd_3579449 := by exact prefixLift 3579449
  have htrace : WordTrace (prefixWord ++ tailWord_3579449) baseStart_3579449 baseEnd_3579449 := by
    simpa [prefixWord, tailWord_3579449, baseEnd_3579449] using wordTrace_append hprefix tailTrace_3579449
  have hstable : (prefixWord ++ tailWord_3579449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579449).length < 2 ^ (prefixWord ++ tailWord_3579449).sum := by decide
  have hdescent : baseEnd_3579449 < baseStart_3579449 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579453 : List Nat := [1, 4, 1, 3, 3, 1, 2, 1, 3, 3]
def baseStart_3579453 : Nat := 118140960795 + 3579453 * 2 ^ 59
def prefixEnd_3579453 : Nat := 4983230072969 + 3 ^ 40 * 3579453 * 2
def baseEnd_3579453 : Nat := 1225319912785392738250601

theorem tailTrace_3579453 : CollatzResearch.WordTrace tailWord_3579453 prefixEnd_3579453 1225319912785392738250601 := by
  unfold tailWord_3579453
  simp only [CollatzResearch.WordTrace]
  refine ⟨130553376301260577747687013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87035584200840385165124675 130553376301260577747687013)
  ·
    refine ⟨24478758056486358327691315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130553376301260577747687013 24478758056486358327691315)
    ·
      refine ⟨36718137084729537491536973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24478758056486358327691315 36718137084729537491536973)
      ·
        refine ⟨13769301406773576559326365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36718137084729537491536973 13769301406773576559326365)
        ·
          refine ⟨5163488027540091209747387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13769301406773576559326365 5163488027540091209747387)
          ·
            refine ⟨7745232041310136814621081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5163488027540091209747387 7745232041310136814621081)
            ·
              refine ⟨5808924030982602610965811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7745232041310136814621081 5808924030982602610965811)
              ·
                refine ⟨8713386046473903916448717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5808924030982602610965811 8713386046473903916448717)
                ·
                  refine ⟨3267519767427713968668269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8713386046473903916448717 3267519767427713968668269)
                  ·
                    refine ⟨1225319912785392738250601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3267519767427713968668269 1225319912785392738250601)
                    ·
                      rfl

theorem cell22_3579453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 1, 3, 3].length) (baseStart_3579453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579453 prefixEnd_3579453 := by exact prefixLift 3579453
  have htrace : WordTrace (prefixWord ++ tailWord_3579453) baseStart_3579453 baseEnd_3579453 := by
    simpa [prefixWord, tailWord_3579453, baseEnd_3579453] using wordTrace_append hprefix tailTrace_3579453
  have hstable : (prefixWord ++ tailWord_3579453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579453).length < 2 ^ (prefixWord ++ tailWord_3579453).sum := by decide
  have hdescent : baseEnd_3579453 < baseStart_3579453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579466 : List Nat := [3, 1, 2, 1, 1, 3, 5, 1, 5]
def baseStart_3579466 : Nat := 118140960795 + 3579466 * 2 ^ 59
def prefixEnd_3579466 : Nat := 4983230072969 + 3 ^ 40 * 3579466 * 2
def baseEnd_3579466 : Nat := 408441454317021679225187

theorem tailTrace_3579466 : CollatzResearch.WordTrace tailWord_3579466 prefixEnd_3579466 408441454317021679225187 := by
  unfold tailWord_3579466
  simp only [CollatzResearch.WordTrace]
  refine ⟨32638462612553370241977563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87035900300142320645273501 32638462612553370241977563)
  ·
    refine ⟨48957693918830055362966345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32638462612553370241977563 48957693918830055362966345)
    ·
      refine ⟨36718270439122541522224759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48957693918830055362966345 36718270439122541522224759)
      ·
        refine ⟨55077405658683812283337139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36718270439122541522224759 55077405658683812283337139)
        ·
          refine ⟨82616108488025718425005709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55077405658683812283337139 82616108488025718425005709)
          ·
            refine ⟨30981040683009644409377141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82616108488025718425005709 30981040683009644409377141)
            ·
              refine ⟨2904472564032154163379107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30981040683009644409377141 2904472564032154163379107)
              ·
                refine ⟨4356708846048231245068661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904472564032154163379107 4356708846048231245068661)
                ·
                  refine ⟨408441454317021679225187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4356708846048231245068661 408441454317021679225187)
                  ·
                    rfl

theorem cell22_3579466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 5].length) (baseStart_3579466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579466 prefixEnd_3579466 := by exact prefixLift 3579466
  have htrace : WordTrace (prefixWord ++ tailWord_3579466) baseStart_3579466 baseEnd_3579466 := by
    simpa [prefixWord, tailWord_3579466, baseEnd_3579466] using wordTrace_append hprefix tailTrace_3579466
  have hstable : (prefixWord ++ tailWord_3579466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579466).length < 2 ^ (prefixWord ++ tailWord_3579466).sum := by decide
  have hdescent : baseEnd_3579466 < baseStart_3579466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579571 : List Nat := [1, 1, 1, 2, 3, 3, 2, 3, 3, 3]
def baseStart_3579571 : Nat := 118140960795 + 3579571 * 2 ^ 59
def prefixEnd_3579571 : Nat := 4983230072969 + 3 ^ 40 * 3579571 * 2
def baseEnd_3579571 : Nat := 1225360306596879763800239

theorem tailTrace_3579571 : CollatzResearch.WordTrace tailWord_3579571 prefixEnd_3579571 1225360306596879763800239 := by
  unfold tailWord_3579571
  simp only [CollatzResearch.WordTrace]
  refine ⟨130557680114833083900482567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87038453409888722600321711 130557680114833083900482567)
  ·
    refine ⟨195836520172249625850723851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130557680114833083900482567 195836520172249625850723851)
    ·
      refine ⟨293754780258374438776085777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195836520172249625850723851 293754780258374438776085777)
      ·
        refine ⟨220316085193780829082064333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293754780258374438776085777 220316085193780829082064333)
        ·
          refine ⟨82618531947667810905774125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220316085193780829082064333 82618531947667810905774125)
          ·
            refine ⟨30981949480375429089665297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82618531947667810905774125 30981949480375429089665297)
            ·
              refine ⟨23236462110281571817248973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30981949480375429089665297 23236462110281571817248973)
              ·
                refine ⟨8713673291355589431468365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23236462110281571817248973 8713673291355589431468365)
                ·
                  refine ⟨3267627484258346036800637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8713673291355589431468365 3267627484258346036800637)
                  ·
                    refine ⟨1225360306596879763800239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3267627484258346036800637 1225360306596879763800239)
                    ·
                      rfl

theorem cell22_3579571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 3, 3, 3].length) (baseStart_3579571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579571 prefixEnd_3579571 := by exact prefixLift 3579571
  have htrace : WordTrace (prefixWord ++ tailWord_3579571) baseStart_3579571 baseEnd_3579571 := by
    simpa [prefixWord, tailWord_3579571, baseEnd_3579571] using wordTrace_append hprefix tailTrace_3579571
  have hstable : (prefixWord ++ tailWord_3579571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579571).length < 2 ^ (prefixWord ++ tailWord_3579571).sum := by decide
  have hdescent : baseEnd_3579571 < baseStart_3579571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579573 : List Nat := [1, 3, 3, 3, 2, 2, 1, 7]
def baseStart_3579573 : Nat := 118140960795 + 3579573 * 2 ^ 59
def prefixEnd_3579573 : Nat := 4983230072969 + 3 ^ 40 * 3579573 * 2
def baseEnd_3579573 : Nat := 136151221248639158361137

theorem tailTrace_3579573 : CollatzResearch.WordTrace tailWord_3579573 prefixEnd_3579573 136151221248639158361137 := by
  unfold tailWord_3579573
  simp only [CollatzResearch.WordTrace]
  refine ⟨130557753060825838242055373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87038502040550558828036915 130557753060825838242055373)
  ·
    refine ⟨48959157397809689340770765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130557753060825838242055373 48959157397809689340770765)
    ·
      refine ⟨18359684024178633502789037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48959157397809689340770765 18359684024178633502789037)
      ·
        refine ⟨6884881509066987563545889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18359684024178633502789037 6884881509066987563545889)
        ·
          refine ⟨5163661131800240672659417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6884881509066987563545889 5163661131800240672659417)
          ·
            refine ⟨3872745848850180504494563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5163661131800240672659417 3872745848850180504494563)
            ·
              refine ⟨5809118773275270756741845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3872745848850180504494563 5809118773275270756741845)
              ·
                refine ⟨136151221248639158361137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5809118773275270756741845 136151221248639158361137)
                ·
                  rfl

theorem cell22_3579573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 7].length) (baseStart_3579573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579573 prefixEnd_3579573 := by exact prefixLift 3579573
  have htrace : WordTrace (prefixWord ++ tailWord_3579573) baseStart_3579573 baseEnd_3579573 := by
    simpa [prefixWord, tailWord_3579573, baseEnd_3579573] using wordTrace_append hprefix tailTrace_3579573
  have hstable : (prefixWord ++ tailWord_3579573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579573).length < 2 ^ (prefixWord ++ tailWord_3579573).sum := by decide
  have hdescent : baseEnd_3579573 < baseStart_3579573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579588 : List Nat := [2, 3, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_3579588 : Nat := 118140960795 + 3579588 * 2 ^ 59
def prefixEnd_3579588 : Nat := 4983230072969 + 3 ^ 40 * 3579588 * 2
def baseEnd_3579588 : Nat := 1225366126044297386125187

theorem tailTrace_3579588 : CollatzResearch.WordTrace tailWord_3579588 prefixEnd_3579588 1225366126044297386125187 := by
  unfold tailWord_3579588
  simp only [CollatzResearch.WordTrace]
  refine ⟨65279150077885747901925709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87038866770514330535900945 65279150077885747901925709)
  ·
    refine ⟨24479681279207155463222141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65279150077885747901925709 24479681279207155463222141)
    ·
      refine ⟨9179880479702683298708303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24479681279207155463222141 9179880479702683298708303)
      ·
        refine ⟨13769820719554024948062455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9179880479702683298708303 13769820719554024948062455)
        ·
          refine ⟨20654731079331037422093683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13769820719554024948062455 20654731079331037422093683)
          ·
            refine ⟨30982096618996556133140525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20654731079331037422093683 30982096618996556133140525)
            ·
              refine ⟨11618286232123708549927697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30982096618996556133140525 11618286232123708549927697)
              ·
                refine ⟨8713714674092781412445773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11618286232123708549927697 8713714674092781412445773)
                ·
                  refine ⟨3267643002784793029667165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8713714674092781412445773 3267643002784793029667165)
                  ·
                    refine ⟨1225366126044297386125187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3267643002784793029667165 1225366126044297386125187)
                    ·
                      rfl

theorem cell22_3579588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_3579588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579588 prefixEnd_3579588 := by exact prefixLift 3579588
  have htrace : WordTrace (prefixWord ++ tailWord_3579588) baseStart_3579588 baseEnd_3579588 := by
    simpa [prefixWord, tailWord_3579588, baseEnd_3579588] using wordTrace_append hprefix tailTrace_3579588
  have hstable : (prefixWord ++ tailWord_3579588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579588).length < 2 ^ (prefixWord ++ tailWord_3579588).sum := by decide
  have hdescent : baseEnd_3579588 < baseStart_3579588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579680 : List Nat := [2, 1, 1, 5, 1, 1, 5, 2, 4]
def baseStart_3579680 : Nat := 118140960795 + 3579680 * 2 ^ 59
def prefixEnd_3579680 : Nat := 4983230072969 + 3 ^ 40 * 3579680 * 2
def baseEnd_3579680 : Nat := 408465873174813270941635

theorem tailTrace_3579680 : CollatzResearch.WordTrace tailWord_3579680 prefixEnd_3579680 408465873174813270941635 := by
  unfold tailWord_3579680
  simp only [CollatzResearch.WordTrace]
  refine ⟨65280827835719097758100247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87041103780958797010800329 65280827835719097758100247)
  ·
    refine ⟨97921241753578646637150371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65280827835719097758100247 97921241753578646637150371)
    ·
      refine ⟨146881862630367969955725557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97921241753578646637150371 146881862630367969955725557)
      ·
        refine ⟨13770174621596997183349271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146881862630367969955725557 13770174621596997183349271)
        ·
          refine ⟨20655261932395495775023907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13770174621596997183349271 20655261932395495775023907)
          ·
            refine ⟨30982892898593243662535861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20655261932395495775023907 30982892898593243662535861)
            ·
              refine ⟨2904646209243116593362737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 30982892898593243662535861 2904646209243116593362737)
              ·
                refine ⟨2178484656932337445022053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2904646209243116593362737 2178484656932337445022053)
                ·
                  refine ⟨408465873174813270941635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2178484656932337445022053 408465873174813270941635)
                  ·
                    rfl

theorem cell22_3579680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 2, 4].length) (baseStart_3579680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579680 prefixEnd_3579680 := by exact prefixLift 3579680
  have htrace : WordTrace (prefixWord ++ tailWord_3579680) baseStart_3579680 baseEnd_3579680 := by
    simpa [prefixWord, tailWord_3579680, baseEnd_3579680] using wordTrace_append hprefix tailTrace_3579680
  have hstable : (prefixWord ++ tailWord_3579680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579680).length < 2 ^ (prefixWord ++ tailWord_3579680).sum := by decide
  have hdescent : baseEnd_3579680 < baseStart_3579680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579710 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_3579710 : Nat := 118140960795 + 3579710 * 2 ^ 59
def prefixEnd_3579710 : Nat := 4983230072969 + 3 ^ 40 * 3579710 * 2
def baseEnd_3579710 : Nat := 1225407889137529734574813

theorem tailTrace_3579710 : CollatzResearch.WordTrace tailWord_3579710 prefixEnd_3579710 1225407889137529734574813 := by
  unfold tailWord_3579710
  simp only [CollatzResearch.WordTrace]
  refine ⟨16320343732666188829974073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87041833240886340426528389 16320343732666188829974073)
  ·
    refine ⟨12240257799499641622480555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16320343732666188829974073 12240257799499641622480555)
    ·
      refine ⟨18360386699249462433720833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12240257799499641622480555 18360386699249462433720833)
      ·
        refine ⟨13770290024437096825290625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18360386699249462433720833 13770290024437096825290625)
        ·
          refine ⟨10327717518327822618967969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13770290024437096825290625 10327717518327822618967969)
          ·
            refine ⟨7745788138745866964225977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10327717518327822618967969 7745788138745866964225977)
            ·
              refine ⟨5809341104059400223169483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7745788138745866964225977 5809341104059400223169483)
              ·
                refine ⟨8714011656089100334754225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5809341104059400223169483 8714011656089100334754225)
                ·
                  refine ⟨6535508742066825251065669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8714011656089100334754225 6535508742066825251065669)
                  ·
                    refine ⟨1225407889137529734574813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6535508742066825251065669 1225407889137529734574813)
                    ·
                      rfl

theorem cell22_3579710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_3579710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579710 prefixEnd_3579710 := by exact prefixLift 3579710
  have htrace : WordTrace (prefixWord ++ tailWord_3579710) baseStart_3579710 baseEnd_3579710 := by
    simpa [prefixWord, tailWord_3579710, baseEnd_3579710] using wordTrace_append hprefix tailTrace_3579710
  have hstable : (prefixWord ++ tailWord_3579710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579710).length < 2 ^ (prefixWord ++ tailWord_3579710).sum := by decide
  have hdescent : baseEnd_3579710 < baseStart_3579710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579774 : List Nat := [4, 2, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_3579774 : Nat := 118140960795 + 3579774 * 2 ^ 59
def prefixEnd_3579774 : Nat := 4983230072969 + 3 ^ 40 * 3579774 * 2
def baseEnd_3579774 : Nat := 1225429797645454900974617

theorem tailTrace_3579774 : CollatzResearch.WordTrace tailWord_3579774 prefixEnd_3579774 1225429797645454900974617 := by
  unfold tailWord_3579774
  simp only [CollatzResearch.WordTrace]
  refine ⟨16320635516637206196265297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87043389422065099713414917 16320635516637206196265297)
  ·
    refine ⟨12240476637477904647198973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16320635516637206196265297 12240476637477904647198973)
    ·
      refine ⟨4590178739054214242699615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12240476637477904647198973 4590178739054214242699615)
      ·
        refine ⟨6885268108581321364049423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4590178739054214242699615 6885268108581321364049423)
        ·
          refine ⟨10327902162871982046074135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6885268108581321364049423 10327902162871982046074135)
          ·
            refine ⟨15491853244307973069111203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10327902162871982046074135 15491853244307973069111203)
            ·
              refine ⟨23237779866461959603666805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15491853244307973069111203 23237779866461959603666805)
              ·
                refine ⟨2178541862480808712843763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23237779866461959603666805 2178541862480808712843763)
                ·
                  refine ⟨3267812793721213069265645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178541862480808712843763 3267812793721213069265645)
                  ·
                    refine ⟨1225429797645454900974617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3267812793721213069265645 1225429797645454900974617)
                    ·
                      rfl

theorem cell22_3579774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_3579774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579774 prefixEnd_3579774 := by exact prefixLift 3579774
  have htrace : WordTrace (prefixWord ++ tailWord_3579774) baseStart_3579774 baseEnd_3579774 := by
    simpa [prefixWord, tailWord_3579774, baseEnd_3579774] using wordTrace_append hprefix tailTrace_3579774
  have hstable : (prefixWord ++ tailWord_3579774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579774).length < 2 ^ (prefixWord ++ tailWord_3579774).sum := by decide
  have hdescent : baseEnd_3579774 < baseStart_3579774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579781 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 8]
def baseStart_3579781 : Nat := 118140960795 + 3579781 * 2 ^ 59
def prefixEnd_3579781 : Nat := 4983230072969 + 3 ^ 40 * 3579781 * 2
def baseEnd_3579781 : Nat := 408477397962836405349865

theorem tailTrace_3579781 : CollatzResearch.WordTrace tailWord_3579781 prefixEnd_3579781 408477397962836405349865 := by
  unfold tailWord_3579781
  simp only [CollatzResearch.WordTrace]
  refine ⟨130565339444072289765627197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87043559629381526510418131 130565339444072289765627197)
  ·
    refine ⟨48962002291527108662110199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130565339444072289765627197 48962002291527108662110199)
    ·
      refine ⟨73443003437290662993165299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48962002291527108662110199 73443003437290662993165299)
      ·
        refine ⟨110164505155935994489747949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73443003437290662993165299 110164505155935994489747949)
        ·
          refine ⟨41311689433475997933655481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110164505155935994489747949 41311689433475997933655481)
          ·
            refine ⟨30983767075106998450241611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41311689433475997933655481 30983767075106998450241611)
            ·
              refine ⟨46475650612660497675362417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30983767075106998450241611 46475650612660497675362417)
              ·
                refine ⟨34856737959495373256521813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46475650612660497675362417 34856737959495373256521813)
                ·
                  refine ⟨408477397962836405349865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34856737959495373256521813 408477397962836405349865)
                  ·
                    rfl

theorem cell22_3579781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 8].length) (baseStart_3579781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579781 prefixEnd_3579781 := by exact prefixLift 3579781
  have htrace : WordTrace (prefixWord ++ tailWord_3579781) baseStart_3579781 baseEnd_3579781 := by
    simpa [prefixWord, tailWord_3579781, baseEnd_3579781] using wordTrace_append hprefix tailTrace_3579781
  have hstable : (prefixWord ++ tailWord_3579781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579781).length < 2 ^ (prefixWord ++ tailWord_3579781).sum := by decide
  have hdescent : baseEnd_3579781 < baseStart_3579781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579868 : List Nat := [2, 2, 6, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3579868 : Nat := 118140960795 + 3579868 * 2 ^ 59
def prefixEnd_3579868 : Nat := 4983230072969 + 3 ^ 40 * 3579868 * 2
def baseEnd_3579868 : Nat := 1225461975766469989124329

theorem tailTrace_3579868 : CollatzResearch.WordTrace tailWord_3579868 prefixEnd_3579868 1225461975766469989124329 := by
  unfold tailWord_3579868
  simp only [CollatzResearch.WordTrace]
  refine ⟨65284256297378551812022129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87045675063171402416029505 65284256297378551812022129)
  ·
    refine ⟨48963192223033913859016597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65284256297378551812022129 48963192223033913859016597)
    ·
      refine ⟨2295149635454714712141403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 48963192223033913859016597 2295149635454714712141403)
      ·
        refine ⟨3442724453182072068212105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2295149635454714712141403 3442724453182072068212105)
        ·
          refine ⟨2582043339886554051159079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3442724453182072068212105 2582043339886554051159079)
          ·
            refine ⟨3873065009829831076738619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582043339886554051159079 3873065009829831076738619)
            ·
              refine ⟨5809597514744746615107929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3873065009829831076738619 5809597514744746615107929)
              ·
                refine ⟨4357198136058559961330947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5809597514744746615107929 4357198136058559961330947)
                ·
                  refine ⟨6535797204087839941996421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4357198136058559961330947 6535797204087839941996421)
                  ·
                    refine ⟨1225461975766469989124329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6535797204087839941996421 1225461975766469989124329)
                    ·
                      rfl

theorem cell22_3579868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3579868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579868 prefixEnd_3579868 := by exact prefixLift 3579868
  have htrace : WordTrace (prefixWord ++ tailWord_3579868) baseStart_3579868 baseEnd_3579868 := by
    simpa [prefixWord, tailWord_3579868, baseEnd_3579868] using wordTrace_append hprefix tailTrace_3579868
  have hstable : (prefixWord ++ tailWord_3579868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579868).length < 2 ^ (prefixWord ++ tailWord_3579868).sum := by decide
  have hdescent : baseEnd_3579868 < baseStart_3579868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579905 : List Nat := [1, 2, 4, 1, 2, 1, 4, 2, 5]
def baseStart_3579905 : Nat := 118140960795 + 3579905 * 2 ^ 59
def prefixEnd_3579905 : Nat := 4983230072969 + 3 ^ 40 * 3579905 * 2
def baseEnd_3579905 : Nat := 408491547207538075316405

theorem tailTrace_3579905 : CollatzResearch.WordTrace tailWord_3579905 prefixEnd_3579905 408491547207538075316405 := by
  unfold tailWord_3579905
  simp only [CollatzResearch.WordTrace]
  refine ⟨130569862095623058943141169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87046574730415372628760779 130569862095623058943141169)
  ·
    refine ⟨97927396571717294207355877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130569862095623058943141169 97927396571717294207355877)
    ·
      refine ⟨18361386857196992663879227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97927396571717294207355877 18361386857196992663879227)
      ·
        refine ⟨27542080285795488995818841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18361386857196992663879227 27542080285795488995818841)
        ·
          refine ⟨20656560214346616746864131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27542080285795488995818841 20656560214346616746864131)
          ·
            refine ⟨30984840321519925120296197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20656560214346616746864131 30984840321519925120296197)
            ·
              refine ⟨5809657560284985960055537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30984840321519925120296197 5809657560284985960055537)
              ·
                refine ⟨4357243170213739470041653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5809657560284985960055537 4357243170213739470041653)
                ·
                  refine ⟨408491547207538075316405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4357243170213739470041653 408491547207538075316405)
                  ·
                    rfl

theorem cell22_3579905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 4, 2, 5].length) (baseStart_3579905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579905 prefixEnd_3579905 := by exact prefixLift 3579905
  have htrace : WordTrace (prefixWord ++ tailWord_3579905) baseStart_3579905 baseEnd_3579905 := by
    simpa [prefixWord, tailWord_3579905, baseEnd_3579905] using wordTrace_append hprefix tailTrace_3579905
  have hstable : (prefixWord ++ tailWord_3579905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579905).length < 2 ^ (prefixWord ++ tailWord_3579905).sum := by decide
  have hdescent : baseEnd_3579905 < baseStart_3579905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579909 : List Nat := [1, 3, 1, 1, 2, 4, 4, 2, 1, 3]
def baseStart_3579909 : Nat := 118140960795 + 3579909 * 2 ^ 59
def prefixEnd_3579909 : Nat := 4983230072969 + 3 ^ 40 * 3579909 * 2
def baseEnd_3579909 : Nat := 1225476010904359548849203

theorem tailTrace_3579909 : CollatzResearch.WordTrace tailWord_3579909 prefixEnd_3579909 1225476010904359548849203 := by
  unfold tailWord_3579909
  simp only [CollatzResearch.WordTrace]
  refine ⟨130570007987608567626286781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87046671991739045084191187 130570007987608567626286781)
  ·
    refine ⟨48963752995353212859857543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130570007987608567626286781 48963752995353212859857543)
    ·
      refine ⟨73445629493029819289786315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48963752995353212859857543 73445629493029819289786315)
      ·
        refine ⟨110168444239544728934679473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73445629493029819289786315 110168444239544728934679473)
        ·
          refine ⟨82626333179658546701009605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110168444239544728934679473 82626333179658546701009605)
          ·
            refine ⟨15492437471185977506439301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82626333179658546701009605 15492437471185977506439301)
            ·
              refine ⟨2904832025847370782457369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15492437471185977506439301 2904832025847370782457369)
              ·
                refine ⟨2178624019385528086843027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2904832025847370782457369 2178624019385528086843027)
                ·
                  refine ⟨3267936029078292130264541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178624019385528086843027 3267936029078292130264541)
                  ·
                    refine ⟨1225476010904359548849203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3267936029078292130264541 1225476010904359548849203)
                    ·
                      rfl

theorem cell22_3579909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 4, 2, 1, 3].length) (baseStart_3579909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579909 prefixEnd_3579909 := by exact prefixLift 3579909
  have htrace : WordTrace (prefixWord ++ tailWord_3579909) baseStart_3579909 baseEnd_3579909 := by
    simpa [prefixWord, tailWord_3579909, baseEnd_3579909] using wordTrace_append hprefix tailTrace_3579909
  have hstable : (prefixWord ++ tailWord_3579909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579909).length < 2 ^ (prefixWord ++ tailWord_3579909).sum := by decide
  have hdescent : baseEnd_3579909 < baseStart_3579909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579935 : List Nat := [1, 1, 2, 4, 1, 2, 2, 4, 1, 4]
def baseStart_3579935 : Nat := 118140960795 + 3579935 * 2 ^ 59
def prefixEnd_3579935 : Nat := 4983230072969 + 3 ^ 40 * 3579935 * 2
def baseEnd_3579935 : Nat := 1225484911235704147699123

theorem tailTrace_3579935 : CollatzResearch.WordTrace tailWord_3579935 prefixEnd_3579935 1225484911235704147699123 := by
  unfold tailWord_3579935
  simp only [CollatzResearch.WordTrace]
  refine ⟨130570956285514374066733259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87047304190342916044488839 130570956285514374066733259)
  ·
    refine ⟨195856434428271561100099889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130570956285514374066733259 195856434428271561100099889)
    ·
      refine ⟨146892325821203670825074917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195856434428271561100099889 146892325821203670825074917)
      ·
        refine ⟨27542311091475688279701547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146892325821203670825074917 27542311091475688279701547)
        ·
          refine ⟨41313466637213532419552321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27542311091475688279701547 41313466637213532419552321)
          ·
            refine ⟨30985099977910149314664241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41313466637213532419552321 30985099977910149314664241)
            ·
              refine ⟨23238824983432611985998181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30985099977910149314664241 23238824983432611985998181)
              ·
                refine ⟨4357279684393614747374659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23238824983432611985998181 4357279684393614747374659)
                ·
                  refine ⟨6535919526590422121061989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4357279684393614747374659 6535919526590422121061989)
                  ·
                    refine ⟨1225484911235704147699123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6535919526590422121061989 1225484911235704147699123)
                    ·
                      rfl

theorem cell22_3579935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 4, 1, 4].length) (baseStart_3579935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579935 prefixEnd_3579935 := by exact prefixLift 3579935
  have htrace : WordTrace (prefixWord ++ tailWord_3579935) baseStart_3579935 baseEnd_3579935 := by
    simpa [prefixWord, tailWord_3579935, baseEnd_3579935] using wordTrace_append hprefix tailTrace_3579935
  have hstable : (prefixWord ++ tailWord_3579935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579935).length < 2 ^ (prefixWord ++ tailWord_3579935).sum := by decide
  have hdescent : baseEnd_3579935 < baseStart_3579935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579948 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 3, 5]
def baseStart_3579948 : Nat := 118140960795 + 3579948 * 2 ^ 59
def prefixEnd_3579948 : Nat := 4983230072969 + 3 ^ 40 * 3579948 * 2
def baseEnd_3579948 : Nat := 1225489361401376447124083

theorem tailTrace_3579948 : CollatzResearch.WordTrace tailWord_3579948 prefixEnd_3579948 1225489361401376447124083 := by
  unfold tailWord_3579948
  simp only [CollatzResearch.WordTrace]
  refine ⟨65285715217233638643478249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87047620289644851524637665 65285715217233638643478249)
  ·
    refine ⟨48964286412925228982608687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65285715217233638643478249 48964286412925228982608687)
    ·
      refine ⟨73446429619387843473913031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48964286412925228982608687 73446429619387843473913031)
      ·
        refine ⟨110169644429081765210869547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73446429619387843473913031 110169644429081765210869547)
        ·
          refine ⟨165254466643622647816304321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110169644429081765210869547 165254466643622647816304321)
          ·
            refine ⟨123940849982716985862228241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165254466643622647816304321 123940849982716985862228241)
            ·
              refine ⟨92955637487037739396671181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123940849982716985862228241 92955637487037739396671181)
              ·
                refine ⟨34858364057639152273751693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 92955637487037739396671181 34858364057639152273751693)
                ·
                  refine ⟨13071886521614682102656885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34858364057639152273751693 13071886521614682102656885)
                  ·
                    refine ⟨1225489361401376447124083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13071886521614682102656885 1225489361401376447124083)
                    ·
                      rfl

theorem cell22_3579948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 5].length) (baseStart_3579948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579948 prefixEnd_3579948 := by exact prefixLift 3579948
  have htrace : WordTrace (prefixWord ++ tailWord_3579948) baseStart_3579948 baseEnd_3579948 := by
    simpa [prefixWord, tailWord_3579948, baseEnd_3579948] using wordTrace_append hprefix tailTrace_3579948
  have hstable : (prefixWord ++ tailWord_3579948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579948).length < 2 ^ (prefixWord ++ tailWord_3579948).sum := by decide
  have hdescent : baseEnd_3579948 < baseStart_3579948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579952 : List Nat := [2, 1, 1, 1, 2, 5, 4, 1, 1, 4]
def baseStart_3579952 : Nat := 118140960795 + 3579952 * 2 ^ 59
def prefixEnd_3579952 : Nat := 4983230072969 + 3 ^ 40 * 3579952 * 2
def baseEnd_3579952 : Nat := 1225490730683121770024071

theorem tailTrace_3579952 : CollatzResearch.WordTrace tailWord_3579952 prefixEnd_3579952 1225490730683121770024071 := by
  unfold tailWord_3579952
  simp only [CollatzResearch.WordTrace]
  refine ⟨65285788163226392985051055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87047717550968523980068073 65285788163226392985051055)
  ·
    refine ⟨97928682244839589477576583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65285788163226392985051055 97928682244839589477576583)
    ·
      refine ⟨146893023367259384216364875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97928682244839589477576583 146893023367259384216364875)
      ·
        refine ⟨220339535050889076324547313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146893023367259384216364875 220339535050889076324547313)
        ·
          refine ⟨165254651288166807243410485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220339535050889076324547313 165254651288166807243410485)
          ·
            refine ⟨15492623558265638179069733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165254651288166807243410485 15492623558265638179069733)
            ·
              refine ⟨2904866917174807158575575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15492623558265638179069733 2904866917174807158575575)
              ·
                refine ⟨4357300375762210737863363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904866917174807158575575 4357300375762210737863363)
                ·
                  refine ⟨6535950563643316106795045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4357300375762210737863363 6535950563643316106795045)
                  ·
                    refine ⟨1225490730683121770024071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6535950563643316106795045 1225490730683121770024071)
                    ·
                      rfl

theorem cell22_3579952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 4, 1, 1, 4].length) (baseStart_3579952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579952 prefixEnd_3579952 := by exact prefixLift 3579952
  have htrace : WordTrace (prefixWord ++ tailWord_3579952) baseStart_3579952 baseEnd_3579952 := by
    simpa [prefixWord, tailWord_3579952, baseEnd_3579952] using wordTrace_append hprefix tailTrace_3579952
  have hstable : (prefixWord ++ tailWord_3579952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579952).length < 2 ^ (prefixWord ++ tailWord_3579952).sum := by decide
  have hdescent : baseEnd_3579952 < baseStart_3579952 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579956 : List Nat := [2, 5, 1, 2, 3, 1, 1, 2, 5]
def baseStart_3579956 : Nat := 118140960795 + 3579956 * 2 ^ 59
def prefixEnd_3579956 : Nat := 4983230072969 + 3 ^ 40 * 3579956 * 2
def baseEnd_3579956 : Nat := 408497366654955697641353

theorem tailTrace_3579956 : CollatzResearch.WordTrace tailWord_3579956 prefixEnd_3579956 408497366654955697641353 := by
  unfold tailWord_3579956
  simp only [CollatzResearch.WordTrace]
  refine ⟨65285861109219147326623861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87047814812292196435498481 65285861109219147326623861)
  ·
    refine ⟨6120549478989295061870987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65285861109219147326623861 6120549478989295061870987)
    ·
      refine ⟨9180824218483942592806481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6120549478989295061870987 9180824218483942592806481)
      ·
        refine ⟨6885618163862956944604861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9180824218483942592806481 6885618163862956944604861)
        ·
          refine ⟨2582106811448608854226823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6885618163862956944604861 2582106811448608854226823)
          ·
            refine ⟨3873160217172913281340235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582106811448608854226823 3873160217172913281340235)
            ·
              refine ⟨5809740325759369922010353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3873160217172913281340235 5809740325759369922010353)
              ·
                refine ⟨4357305244319527441507765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5809740325759369922010353 4357305244319527441507765)
                ·
                  refine ⟨408497366654955697641353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4357305244319527441507765 408497366654955697641353)
                  ·
                    rfl

theorem cell22_3579956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_3579956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579956 prefixEnd_3579956 := by exact prefixLift 3579956
  have htrace : WordTrace (prefixWord ++ tailWord_3579956) baseStart_3579956 baseEnd_3579956 := by
    simpa [prefixWord, tailWord_3579956, baseEnd_3579956] using wordTrace_append hprefix tailTrace_3579956
  have hstable : (prefixWord ++ tailWord_3579956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579956).length < 2 ^ (prefixWord ++ tailWord_3579956).sum := by decide
  have hdescent : baseEnd_3579956 < baseStart_3579956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579978 : List Nat := [3, 1, 2, 1, 1, 2, 1, 11]
def baseStart_3579978 : Nat := 118140960795 + 3579978 * 2 ^ 59
def prefixEnd_3579978 : Nat := 4983230072969 + 3 ^ 40 * 3579978 * 2
def baseEnd_3579978 : Nat := 136166625668274040985999

theorem tailTrace_3579978 : CollatzResearch.WordTrace tailWord_3579978 prefixEnd_3579978 136166625668274040985999 := by
  unfold tailWord_3579978
  simp only [CollatzResearch.WordTrace]
  refine ⟨32643131156089648102637147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87048349749572394940365725 32643131156089648102637147)
  ·
    refine ⟨48964696734134472153955721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32643131156089648102637147 48964696734134472153955721)
    ·
      refine ⟨36723522550600854115466791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48964696734134472153955721 36723522550600854115466791)
      ·
        refine ⟨55085283825901281173200187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36723522550600854115466791 55085283825901281173200187)
        ·
          refine ⟨82627925738851921759800281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55085283825901281173200187 82627925738851921759800281)
          ·
            refine ⟨61970944304138941319850211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82627925738851921759800281 61970944304138941319850211)
            ·
              refine ⟨92956416456208411979775317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 61970944304138941319850211 92956416456208411979775317)
              ·
                refine ⟨136166625668274040985999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 92956416456208411979775317 136166625668274040985999)
                ·
                  rfl

theorem cell22_3579978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 11].length) (baseStart_3579978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579978 prefixEnd_3579978 := by exact prefixLift 3579978
  have htrace : WordTrace (prefixWord ++ tailWord_3579978) baseStart_3579978 baseEnd_3579978 := by
    simpa [prefixWord, tailWord_3579978, baseEnd_3579978] using wordTrace_append hprefix tailTrace_3579978
  have hstable : (prefixWord ++ tailWord_3579978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579978).length < 2 ^ (prefixWord ++ tailWord_3579978).sum := by decide
  have hdescent : baseEnd_3579978 < baseStart_3579978 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579982 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 1, 5]
def baseStart_3579982 : Nat := 118140960795 + 3579982 * 2 ^ 59
def prefixEnd_3579982 : Nat := 4983230072969 + 3 ^ 40 * 3579982 * 2
def baseEnd_3579982 : Nat := 1225501000296211691773979

theorem tailTrace_3579982 : CollatzResearch.WordTrace tailWord_3579982 prefixEnd_3579982 1225501000296211691773979 := by
  unfold tailWord_3579982
  simp only [CollatzResearch.WordTrace]
  refine ⟨16321583814543012636711775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87048447010896067395796133 16321583814543012636711775)
  ·
    refine ⟨24482375721814518955067663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16321583814543012636711775 24482375721814518955067663)
    ·
      refine ⟨36723563582721778432601495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24482375721814518955067663 36723563582721778432601495)
      ·
        refine ⟨55085345374082667648902243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36723563582721778432601495 55085345374082667648902243)
        ·
          refine ⟨82628018061124001473353365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55085345374082667648902243 82628018061124001473353365)
          ·
            refine ⟨3873188346615187569063439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 82628018061124001473353365 3873188346615187569063439)
            ·
              refine ⟨5809782519922781353595159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3873188346615187569063439 5809782519922781353595159)
              ·
                refine ⟨8714673779884172030392739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5809782519922781353595159 8714673779884172030392739)
                ·
                  refine ⟨13072010669826258045589109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8714673779884172030392739 13072010669826258045589109)
                  ·
                    refine ⟨1225501000296211691773979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13072010669826258045589109 1225501000296211691773979)
                    ·
                      rfl

theorem cell22_3579982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_3579982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579982 prefixEnd_3579982 := by exact prefixLift 3579982
  have htrace : WordTrace (prefixWord ++ tailWord_3579982) baseStart_3579982 baseEnd_3579982 := by
    simpa [prefixWord, tailWord_3579982, baseEnd_3579982] using wordTrace_append hprefix tailTrace_3579982
  have hstable : (prefixWord ++ tailWord_3579982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579982).length < 2 ^ (prefixWord ++ tailWord_3579982).sum := by decide
  have hdescent : baseEnd_3579982 < baseStart_3579982 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579993 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 2, 7]
def baseStart_3579993 : Nat := 118140960795 + 3579993 * 2 ^ 59
def prefixEnd_3579993 : Nat := 4983230072969 + 3 ^ 40 * 3579993 * 2
def baseEnd_3579993 : Nat := 1225504765821011329748945

theorem tailTrace_3579993 : CollatzResearch.WordTrace tailWord_3579993 prefixEnd_3579993 1225504765821011329748945 := by
  unfold tailWord_3579993
  simp only [CollatzResearch.WordTrace]
  refine ⟨130573071719304249972344633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87048714479536166648229755 130573071719304249972344633)
  ·
    refine ⟨97929803789478187479258475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130573071719304249972344633 97929803789478187479258475)
    ·
      refine ⟨146894705684217281218887713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97929803789478187479258475 146894705684217281218887713)
      ·
        refine ⟨110171029263162960914165785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146894705684217281218887713 110171029263162960914165785)
        ·
          refine ⟨82628271947372220685624339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110171029263162960914165785 82628271947372220685624339)
          ·
            refine ⟨123942407921058331028436509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82628271947372220685624339 123942407921058331028436509)
            ·
              refine ⟨46478402970396874135663691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123942407921058331028436509 46478402970396874135663691)
              ·
                refine ⟨69717604455595311203495537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46478402970396874135663691 69717604455595311203495537)
                ·
                  refine ⟨52288203341696483402621653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69717604455595311203495537 52288203341696483402621653)
                  ·
                    refine ⟨1225504765821011329748945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52288203341696483402621653 1225504765821011329748945)
                    ·
                      rfl

theorem cell22_3579993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 2, 7].length) (baseStart_3579993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579993 prefixEnd_3579993 := by exact prefixLift 3579993
  have htrace : WordTrace (prefixWord ++ tailWord_3579993) baseStart_3579993 baseEnd_3579993 := by
    simpa [prefixWord, tailWord_3579993, baseEnd_3579993] using wordTrace_append hprefix tailTrace_3579993
  have hstable : (prefixWord ++ tailWord_3579993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579993).length < 2 ^ (prefixWord ++ tailWord_3579993).sum := by decide
  have hdescent : baseEnd_3579993 < baseStart_3579993 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3579997 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 1, 6]
def baseStart_3579997 : Nat := 118140960795 + 3579997 * 2 ^ 59
def prefixEnd_3579997 : Nat := 4983230072969 + 3 ^ 40 * 3579997 * 2
def baseEnd_3579997 : Nat := 1225506135102756652648933

theorem tailTrace_3579997 : CollatzResearch.WordTrace tailWord_3579997 prefixEnd_3579997 1225506135102756652648933 := by
  unfold tailWord_3579997
  simp only [CollatzResearch.WordTrace]
  refine ⟨130573217611289758655490245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87048811740859839103660163 130573217611289758655490245)
  ·
    refine ⟨24482478302116829747904421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130573217611289758655490245 24482478302116829747904421)
    ·
      refine ⟨4590464681646905577732079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24482478302116829747904421 4590464681646905577732079)
      ·
        refine ⟨6885697022470358366598119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4590464681646905577732079 6885697022470358366598119)
        ·
          refine ⟨10328545533705537549897179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6885697022470358366598119 10328545533705537549897179)
          ·
            refine ⟨15492818300558306324845769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10328545533705537549897179 15492818300558306324845769)
            ·
              refine ⟨11619613725418729743634327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15492818300558306324845769 11619613725418729743634327)
              ·
                refine ⟨17429420588128094615451491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11619613725418729743634327 17429420588128094615451491)
                ·
                  refine ⟨26144130882192141923177237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17429420588128094615451491 26144130882192141923177237)
                  ·
                    refine ⟨1225506135102756652648933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26144130882192141923177237 1225506135102756652648933)
                    ·
                      rfl

theorem cell22_3579997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_3579997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3579997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3579997 prefixEnd_3579997 := by exact prefixLift 3579997
  have htrace : WordTrace (prefixWord ++ tailWord_3579997) baseStart_3579997 baseEnd_3579997 := by
    simpa [prefixWord, tailWord_3579997, baseEnd_3579997] using wordTrace_append hprefix tailTrace_3579997
  have hstable : (prefixWord ++ tailWord_3579997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3579997).length < 2 ^ (prefixWord ++ tailWord_3579997).sum := by decide
  have hdescent : baseEnd_3579997 < baseStart_3579997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3579997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580033 : List Nat := [1, 2, 4, 2, 4, 1, 2, 1, 2, 3]
def baseStart_3580033 : Nat := 118140960795 + 3580033 * 2 ^ 59
def prefixEnd_3580033 : Nat := 4983230072969 + 3 ^ 40 * 3580033 * 2
def baseEnd_3580033 : Nat := 1225518458638464558748823

theorem tailTrace_3580033 : CollatzResearch.WordTrace tailWord_3580033 prefixEnd_3580033 1225518458638464558748823 := by
  unfold tailWord_3580033
  simp only [CollatzResearch.WordTrace]
  refine ⟨130574530639159336803800753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87049687092772891202533835 130574530639159336803800753)
  ·
    refine ⟨97930897979369502602850565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130574530639159336803800753 97930897979369502602850565)
    ·
      refine ⟨18362043371131781738034481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97930897979369502602850565 18362043371131781738034481)
      ·
        refine ⟨13771532528348836303525861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18362043371131781738034481 13771532528348836303525861)
        ·
          refine ⟨2582162349065406806911099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13771532528348836303525861 2582162349065406806911099)
          ·
            refine ⟨3873243523598110210366649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582162349065406806911099 3873243523598110210366649)
            ·
              refine ⟨2904932642698582657774987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3873243523598110210366649 2904932642698582657774987)
              ·
                refine ⟨4357398964047873986662481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2904932642698582657774987 4357398964047873986662481)
                ·
                  refine ⟨3268049223035905489996861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4357398964047873986662481 3268049223035905489996861)
                  ·
                    refine ⟨1225518458638464558748823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3268049223035905489996861 1225518458638464558748823)
                    ·
                      rfl

theorem cell22_3580033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 2, 1, 2, 3].length) (baseStart_3580033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580033 prefixEnd_3580033 := by exact prefixLift 3580033
  have htrace : WordTrace (prefixWord ++ tailWord_3580033) baseStart_3580033 baseEnd_3580033 := by
    simpa [prefixWord, tailWord_3580033, baseEnd_3580033] using wordTrace_append hprefix tailTrace_3580033
  have hstable : (prefixWord ++ tailWord_3580033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580033).length < 2 ^ (prefixWord ++ tailWord_3580033).sum := by decide
  have hdescent : baseEnd_3580033 < baseStart_3580033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580160 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 2, 6]
def baseStart_3580160 : Nat := 118140960795 + 3580160 * 2 ^ 59
def prefixEnd_3580160 : Nat := 4983230072969 + 3 ^ 40 * 3580160 * 2
def baseEnd_3580160 : Nat := 1225561933333878560823433

theorem tailTrace_3580160 : CollatzResearch.WordTrace tailWord_3580160 prefixEnd_3580160 1225561933333878560823433 := by
  unfold tailWord_3580160
  simp only [CollatzResearch.WordTrace]
  refine ⟨65289581354849618746836967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87052775139799491662449289 65289581354849618746836967)
  ·
    refine ⟨97934372032274428120255451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65289581354849618746836967 97934372032274428120255451)
    ·
      refine ⟨146901558048411642180383177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97934372032274428120255451 146901558048411642180383177)
      ·
        refine ⟨110176168536308731635287383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146901558048411642180383177 110176168536308731635287383)
        ·
          refine ⟨165264252804463097452931075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110176168536308731635287383 165264252804463097452931075)
          ·
            refine ⟨247896379206694646179396613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165264252804463097452931075 247896379206694646179396613)
            ·
              refine ⟨46480571101255246158636865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 247896379206694646179396613 46480571101255246158636865)
              ·
                refine ⟨34860428325941434618977649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46480571101255246158636865 34860428325941434618977649)
                ·
                  refine ⟨26145321244456075964233237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34860428325941434618977649 26145321244456075964233237)
                  ·
                    refine ⟨1225561933333878560823433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26145321244456075964233237 1225561933333878560823433)
                    ·
                      rfl

theorem cell22_3580160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 2, 6].length) (baseStart_3580160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580160 prefixEnd_3580160 := by exact prefixLift 3580160
  have htrace : WordTrace (prefixWord ++ tailWord_3580160) baseStart_3580160 baseEnd_3580160 := by
    simpa [prefixWord, tailWord_3580160, baseEnd_3580160] using wordTrace_append hprefix tailTrace_3580160
  have hstable : (prefixWord ++ tailWord_3580160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580160).length < 2 ^ (prefixWord ++ tailWord_3580160).sum := by decide
  have hdescent : baseEnd_3580160 < baseStart_3580160 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580192 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 7]
def baseStart_3580192 : Nat := 118140960795 + 3580192 * 2 ^ 59
def prefixEnd_3580192 : Nat := 4983230072969 + 3 ^ 40 * 3580192 * 2
def baseEnd_3580192 : Nat := 408524295862613714674445

theorem tailTrace_3580192 : CollatzResearch.WordTrace tailWord_3580192 prefixEnd_3580192 408524295862613714674445 := by
  unfold tailWord_3580192
  simp only [CollatzResearch.WordTrace]
  refine ⟨65290164922791653479419415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87053553230388871305892553 65290164922791653479419415)
  ·
    refine ⟨97935247384187480219129123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65290164922791653479419415 97935247384187480219129123)
    ·
      refine ⟨146902871076281220328693685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97935247384187480219129123 146902871076281220328693685)
      ·
        refine ⟨13772144163401364405815033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 146902871076281220328693685 13772144163401364405815033)
        ·
          refine ⟨10329108122551023304361275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13772144163401364405815033 10329108122551023304361275)
          ·
            refine ⟨15493662183826534956541913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10329108122551023304361275 15493662183826534956541913)
            ·
              refine ⟨11620246637869901217406435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15493662183826534956541913 11620246637869901217406435)
              ·
                refine ⟨17430369956804851826109653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11620246637869901217406435 17430369956804851826109653)
                ·
                  refine ⟨408524295862613714674445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17430369956804851826109653 408524295862613714674445)
                  ·
                    rfl

theorem cell22_3580192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 7].length) (baseStart_3580192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580192 prefixEnd_3580192 := by exact prefixLift 3580192
  have htrace : WordTrace (prefixWord ++ tailWord_3580192) baseStart_3580192 baseEnd_3580192 := by
    simpa [prefixWord, tailWord_3580192, baseEnd_3580192] using wordTrace_append hprefix tailTrace_3580192
  have hstable : (prefixWord ++ tailWord_3580192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580192).length < 2 ^ (prefixWord ++ tailWord_3580192).sum := by decide
  have hdescent : baseEnd_3580192 < baseStart_3580192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580196 : List Nat := [2, 3, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_3580196 : Nat := 118140960795 + 3580196 * 2 ^ 59
def prefixEnd_3580196 : Nat := 4983230072969 + 3 ^ 40 * 3580196 * 2
def baseEnd_3580196 : Nat := 1225574256869586466923323

theorem tailTrace_3580196 : CollatzResearch.WordTrace tailWord_3580196 prefixEnd_3580196 1225574256869586466923323 := by
  unfold tailWord_3580196
  simp only [CollatzResearch.WordTrace]
  refine ⟨65290237868784407820992221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87053650491712543761322961 65290237868784407820992221)
  ·
    refine ⟨24483839200794152932872083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65290237868784407820992221 24483839200794152932872083)
    ·
      refine ⟨36725758801191229399308125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24483839200794152932872083 36725758801191229399308125)
      ·
        refine ⟨13772159550446711024740547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36725758801191229399308125 13772159550446711024740547)
        ·
          refine ⟨20658239325670066537110821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13772159550446711024740547 20658239325670066537110821)
          ·
            refine ⟨3873419873563137475708279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 20658239325670066537110821 3873419873563137475708279)
            ·
              refine ⟨5810129810344706213562419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3873419873563137475708279 5810129810344706213562419)
              ·
                refine ⟨8715194715517059320343629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5810129810344706213562419 8715194715517059320343629)
                ·
                  refine ⟨3268198018318897245128861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8715194715517059320343629 3268198018318897245128861)
                  ·
                    refine ⟨1225574256869586466923323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3268198018318897245128861 1225574256869586466923323)
                    ·
                      rfl

theorem cell22_3580196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_3580196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580196 prefixEnd_3580196 := by exact prefixLift 3580196
  have htrace : WordTrace (prefixWord ++ tailWord_3580196) baseStart_3580196 baseEnd_3580196 := by
    simpa [prefixWord, tailWord_3580196, baseEnd_3580196] using wordTrace_append hprefix tailTrace_3580196
  have hstable : (prefixWord ++ tailWord_3580196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580196).length < 2 ^ (prefixWord ++ tailWord_3580196).sum := by decide
  have hdescent : baseEnd_3580196 < baseStart_3580196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580209 : List Nat := [1, 2, 2, 3, 4, 1, 1, 3, 5]
def baseStart_3580209 : Nat := 118140960795 + 3580209 * 2 ^ 59
def prefixEnd_3580209 : Nat := 4983230072969 + 3 ^ 40 * 3580209 * 2
def baseEnd_3580209 : Nat := 408526235678419588782761

theorem tailTrace_3580209 : CollatzResearch.WordTrace tailWord_3580209 prefixEnd_3580209 408526235678419588782761 := by
  unfold tailWord_3580209
  simp only [CollatzResearch.WordTrace]
  refine ⟨130580949886521718862207681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87053966591014479241471787 130580949886521718862207681)
  ·
    refine ⟨97935712414891289146655761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130580949886521718862207681 97935712414891289146655761)
    ·
      refine ⟨73451784311168466859991821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97935712414891289146655761 73451784311168466859991821)
      ·
        refine ⟨27544419116688175072496933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73451784311168466859991821 27544419116688175072496933)
        ·
          refine ⟨5164578584379032826093175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27544419116688175072496933 5164578584379032826093175)
          ·
            refine ⟨7746867876568549239139763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5164578584379032826093175 7746867876568549239139763)
            ·
              refine ⟨11620301814852823858709645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7746867876568549239139763 11620301814852823858709645)
              ·
                refine ⟨4357613180569808947016117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11620301814852823858709645 4357613180569808947016117)
                ·
                  refine ⟨408526235678419588782761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4357613180569808947016117 408526235678419588782761)
                  ·
                    rfl

theorem cell22_3580209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 3, 5].length) (baseStart_3580209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580209 prefixEnd_3580209 := by exact prefixLift 3580209
  have htrace : WordTrace (prefixWord ++ tailWord_3580209) baseStart_3580209 baseEnd_3580209 := by
    simpa [prefixWord, tailWord_3580209, baseEnd_3580209] using wordTrace_append hprefix tailTrace_3580209
  have hstable : (prefixWord ++ tailWord_3580209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580209).length < 2 ^ (prefixWord ++ tailWord_3580209).sum := by decide
  have hdescent : baseEnd_3580209 < baseStart_3580209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580269 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 1, 5]
def baseStart_3580269 : Nat := 118140960795 + 3580269 * 2 ^ 59
def prefixEnd_3580269 : Nat := 4983230072969 + 3 ^ 40 * 3580269 * 2
def baseEnd_3580269 : Nat := 1225599246261438609848099

theorem tailTrace_3580269 : CollatzResearch.WordTrace tailWord_3580269 prefixEnd_3580269 1225599246261438609848099 := by
  unfold tailWord_3580269
  simp only [CollatzResearch.WordTrace]
  refine ⟨130583138266304349109391861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87055425510869566072927907 130583138266304349109391861)
  ·
    refine ⟨12242169212466032729005487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130583138266304349109391861 12242169212466032729005487)
    ·
      refine ⟨18363253818699049093508231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12242169212466032729005487 18363253818699049093508231)
      ·
        refine ⟨27544880728048573640262347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18363253818699049093508231 27544880728048573640262347)
        ·
          refine ⟨41317321092072860460393521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27544880728048573640262347 41317321092072860460393521)
          ·
            refine ⟨30987990819054645345295141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41317321092072860460393521 30987990819054645345295141)
            ·
              refine ⟨5810248278572746002242839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 30987990819054645345295141 5810248278572746002242839)
              ·
                refine ⟨8715372417859119003364259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5810248278572746002242839 8715372417859119003364259)
                ·
                  refine ⟨13073058626788678505046389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8715372417859119003364259 13073058626788678505046389)
                  ·
                    refine ⟨1225599246261438609848099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13073058626788678505046389 1225599246261438609848099)
                    ·
                      rfl

theorem cell22_3580269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 1, 5].length) (baseStart_3580269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580269 prefixEnd_3580269 := by exact prefixLift 3580269
  have htrace : WordTrace (prefixWord ++ tailWord_3580269) baseStart_3580269 baseEnd_3580269 := by
    simpa [prefixWord, tailWord_3580269, baseEnd_3580269] using wordTrace_append hprefix tailTrace_3580269
  have hstable : (prefixWord ++ tailWord_3580269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580269).length < 2 ^ (prefixWord ++ tailWord_3580269).sum := by decide
  have hdescent : baseEnd_3580269 < baseStart_3580269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580333 : List Nat := [1, 5, 2, 2, 2, 2, 2, 6]
def baseStart_3580333 : Nat := 118140960795 + 3580333 * 2 ^ 59
def prefixEnd_3580333 : Nat := 4983230072969 + 3 ^ 40 * 3580333 * 2
def baseEnd_3580333 : Nat := 136180128307707086249767

theorem tailTrace_3580333 : CollatzResearch.WordTrace tailWord_3580333 prefixEnd_3580333 136180128307707086249767 := by
  unfold tailWord_3580333
  simp only [CollatzResearch.WordTrace]
  refine ⟨130585472538072488039721653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87056981692048325359814435 130585472538072488039721653)
  ·
    refine ⟨12242388050444295753723905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130585472538072488039721653 12242388050444295753723905)
    ·
      refine ⟨9181791037833221815292929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12242388050444295753723905 9181791037833221815292929)
      ·
        refine ⟨6886343278374916361469697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9181791037833221815292929 6886343278374916361469697)
        ·
          refine ⟨5164757458781187271102273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6886343278374916361469697 5164757458781187271102273)
          ·
            refine ⟨3873568094085890453326705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5164757458781187271102273 3873568094085890453326705)
            ·
              refine ⟨2905176070564417839995029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3873568094085890453326705 2905176070564417839995029)
              ·
                refine ⟨136180128307707086249767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2905176070564417839995029 136180128307707086249767)
                ·
                  rfl

theorem cell22_3580333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 6].length) (baseStart_3580333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580333 prefixEnd_3580333 := by exact prefixLift 3580333
  have htrace : WordTrace (prefixWord ++ tailWord_3580333) baseStart_3580333 baseEnd_3580333 := by
    simpa [prefixWord, tailWord_3580333, baseEnd_3580333] using wordTrace_append hprefix tailTrace_3580333
  have hstable : (prefixWord ++ tailWord_3580333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580333).length < 2 ^ (prefixWord ++ tailWord_3580333).sum := by decide
  have hdescent : baseEnd_3580333 < baseStart_3580333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580419 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 2, 4]
def baseStart_3580419 : Nat := 118140960795 + 3580419 * 2 ^ 59
def prefixEnd_3580419 : Nat := 4983230072969 + 3 ^ 40 * 3580419 * 2
def baseEnd_3580419 : Nat := 1225650594326888218597639

theorem tailTrace_3580419 : CollatzResearch.WordTrace tailWord_3580419 prefixEnd_3580419 1225650594326888218597639 := by
  unfold tailWord_3580419
  simp only [CollatzResearch.WordTrace]
  refine ⟨130588609215760924727352311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87059072810507283151568207 130588609215760924727352311)
  ·
    refine ⟨195882913823641387091028467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130588609215760924727352311 195882913823641387091028467)
    ·
      refine ⟨293824370735462080636542701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195882913823641387091028467 293824370735462080636542701)
      ·
        refine ⟨110184139025798280238703513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 293824370735462080636542701 110184139025798280238703513)
        ·
          refine ⟨82638104269348710179027635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110184139025798280238703513 82638104269348710179027635)
          ·
            refine ⟨123957156404023065268541453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82638104269348710179027635 123957156404023065268541453)
            ·
              refine ⟨46483933651508649475703045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123957156404023065268541453 46483933651508649475703045)
              ·
                refine ⟨8715737559657871776694321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46483933651508649475703045 8715737559657871776694321)
                ·
                  refine ⟨6536803169743403832520741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8715737559657871776694321 6536803169743403832520741)
                  ·
                    refine ⟨1225650594326888218597639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6536803169743403832520741 1225650594326888218597639)
                    ·
                      rfl

theorem cell22_3580419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 2, 4].length) (baseStart_3580419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580419 prefixEnd_3580419 := by exact prefixLift 3580419
  have htrace : WordTrace (prefixWord ++ tailWord_3580419) baseStart_3580419 baseEnd_3580419 := by
    simpa [prefixWord, tailWord_3580419, baseEnd_3580419] using wordTrace_append hprefix tailTrace_3580419
  have hstable : (prefixWord ++ tailWord_3580419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580419).length < 2 ^ (prefixWord ++ tailWord_3580419).sum := by decide
  have hdescent : baseEnd_3580419 < baseStart_3580419 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580421 : List Nat := [1, 3, 1, 1, 2, 2, 3, 4, 2, 3]
def baseStart_3580421 : Nat := 118140960795 + 3580421 * 2 ^ 59
def prefixEnd_3580421 : Nat := 4983230072969 + 3 ^ 40 * 3580421 * 2
def baseEnd_3580421 : Nat := 1225651278967760880047633

theorem tailTrace_3580421 : CollatzResearch.WordTrace tailWord_3580421 prefixEnd_3580421 1225651278967760880047633 := by
  unfold tailWord_3580421
  simp only [CollatzResearch.WordTrace]
  refine ⟨130588682161753679068925117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87059121441169119379283411 130588682161753679068925117)
  ·
    refine ⟨48970755810657629650846919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130588682161753679068925117 48970755810657629650846919)
    ·
      refine ⟨73456133715986444476270379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48970755810657629650846919 73456133715986444476270379)
      ·
        refine ⟨110184200573979666714405569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73456133715986444476270379 110184200573979666714405569)
        ·
          refine ⟨82638150430484750035804177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110184200573979666714405569 82638150430484750035804177)
          ·
            refine ⟨61978612822863562526853133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82638150430484750035804177 61978612822863562526853133)
            ·
              refine ⟨23241979808573835947569925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61978612822863562526853133 23241979808573835947569925)
              ·
                refine ⟨4357871214107594240169361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23241979808573835947569925 4357871214107594240169361)
                ·
                  refine ⟨3268403410580695680127021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4357871214107594240169361 3268403410580695680127021)
                  ·
                    refine ⟨1225651278967760880047633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3268403410580695680127021 1225651278967760880047633)
                    ·
                      rfl

theorem cell22_3580421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 4, 2, 3].length) (baseStart_3580421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580421 prefixEnd_3580421 := by exact prefixLift 3580421
  have htrace : WordTrace (prefixWord ++ tailWord_3580421) baseStart_3580421 baseEnd_3580421 := by
    simpa [prefixWord, tailWord_3580421, baseEnd_3580421] using wordTrace_append hprefix tailTrace_3580421
  have hstable : (prefixWord ++ tailWord_3580421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580421).length < 2 ^ (prefixWord ++ tailWord_3580421).sum := by decide
  have hdescent : baseEnd_3580421 < baseStart_3580421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580423 : List Nat := [1, 1, 4, 3, 3, 1, 1, 4, 4]
def baseStart_3580423 : Nat := 118140960795 + 3580423 * 2 ^ 59
def prefixEnd_3580423 : Nat := 4983230072969 + 3 ^ 40 * 3580423 * 2
def baseEnd_3580423 : Nat := 408550654536211180499209

theorem tailTrace_3580423 : CollatzResearch.WordTrace tailWord_3580423 prefixEnd_3580423 408550654536211180499209 := by
  unfold tailWord_3580423
  simp only [CollatzResearch.WordTrace]
  refine ⟨130588755107746433410497923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87059170071830955606998615 130588755107746433410497923)
  ·
    refine ⟨195883132661619650115746885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130588755107746433410497923 195883132661619650115746885)
    ·
      refine ⟨36728087374053684396702541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 195883132661619650115746885 36728087374053684396702541)
      ·
        refine ⟨13773032765270131648763453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36728087374053684396702541 13773032765270131648763453)
        ·
          refine ⟨5164887286976299368286295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13773032765270131648763453 5164887286976299368286295)
          ·
            refine ⟨7747330930464449052429443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5164887286976299368286295 7747330930464449052429443)
            ·
              refine ⟨11620996395696673578644165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7747330930464449052429443 11620996395696673578644165)
              ·
                refine ⟨2178936824193126295995781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11620996395696673578644165 2178936824193126295995781)
                ·
                  refine ⟨408550654536211180499209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2178936824193126295995781 408550654536211180499209)
                  ·
                    rfl

theorem cell22_3580423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 4, 4].length) (baseStart_3580423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580423 prefixEnd_3580423 := by exact prefixLift 3580423
  have htrace : WordTrace (prefixWord ++ tailWord_3580423) baseStart_3580423 baseEnd_3580423 := by
    simpa [prefixWord, tailWord_3580423, baseEnd_3580423] using wordTrace_append hprefix tailTrace_3580423
  have hstable : (prefixWord ++ tailWord_3580423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580423).length < 2 ^ (prefixWord ++ tailWord_3580423).sum := by decide
  have hdescent : baseEnd_3580423 < baseStart_3580423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580451 : List Nat := [1, 1, 1, 4, 4, 2, 3, 6]
def baseStart_3580451 : Nat := 118140960795 + 3580451 * 2 ^ 59
def prefixEnd_3580451 : Nat := 4983230072969 + 3 ^ 40 * 3580451 * 2
def baseEnd_3580451 : Nat := 136184616508983422421949

theorem tailTrace_3580451 : CollatzResearch.WordTrace tailWord_3580451 prefixEnd_3580451 136184616508983422421949 := by
  unfold tailWord_3580451
  simp only [CollatzResearch.WordTrace]
  refine ⟨130589776351644994192517207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87059850901096662795011471 130589776351644994192517207)
  ·
    refine ⟨195884664527467491288775811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130589776351644994192517207 195884664527467491288775811)
    ·
      refine ⟨293826996791201236933163717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195884664527467491288775811 293826996791201236933163717)
      ·
        refine ⟨55092561898350231924968197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 293826996791201236933163717 55092561898350231924968197)
        ·
          refine ⟨10329855355940668485931537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55092561898350231924968197 10329855355940668485931537)
          ·
            refine ⟨7747391516955501364448653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10329855355940668485931537 7747391516955501364448653)
            ·
              refine ⟨2905271818858313011668245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7747391516955501364448653 2905271818858313011668245)
              ·
                refine ⟨136184616508983422421949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2905271818858313011668245 136184616508983422421949)
                ·
                  rfl

theorem cell22_3580451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 3, 6].length) (baseStart_3580451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580451 prefixEnd_3580451 := by exact prefixLift 3580451
  have htrace : WordTrace (prefixWord ++ tailWord_3580451) baseStart_3580451 baseEnd_3580451 := by
    simpa [prefixWord, tailWord_3580451, baseEnd_3580451] using wordTrace_append hprefix tailTrace_3580451
  have hstable : (prefixWord ++ tailWord_3580451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580451).length < 2 ^ (prefixWord ++ tailWord_3580451).sum := by decide
  have hdescent : baseEnd_3580451 < baseStart_3580451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580468 : List Nat := [2, 5, 1, 3, 1, 1, 9]
def baseStart_3580468 : Nat := 118140960795 + 3580468 * 2 ^ 59
def prefixEnd_3580468 : Nat := 4983230072969 + 3 ^ 40 * 3580468 * 2
def baseEnd_3580468 : Nat := 45395087704750682374907

theorem tailTrace_3580468 : CollatzResearch.WordTrace tailWord_3580468 prefixEnd_3580468 45395087704750682374907 := by
  unfold tailWord_3580468
  simp only [CollatzResearch.WordTrace]
  refine ⟨65295198196291703047943029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87060264261722270730590705 65295198196291703047943029)
  ·
    refine ⟨6121424830902347160744659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 65295198196291703047943029 6121424830902347160744659)
    ·
      refine ⟨9182137246353520741116989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6121424830902347160744659 9182137246353520741116989)
      ·
        refine ⟨3443301467382570277918871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9182137246353520741116989 3443301467382570277918871)
        ·
          refine ⟨5164952201073855416878307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3443301467382570277918871 5164952201073855416878307)
          ·
            refine ⟨7747428301610783125317461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5164952201073855416878307 7747428301610783125317461)
            ·
              refine ⟨45395087704750682374907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7747428301610783125317461 45395087704750682374907)
              ·
                rfl

theorem cell22_3580468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 9].length) (baseStart_3580468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580468 prefixEnd_3580468 := by exact prefixLift 3580468
  have htrace : WordTrace (prefixWord ++ tailWord_3580468) baseStart_3580468 baseEnd_3580468 := by
    simpa [prefixWord, tailWord_3580468, baseEnd_3580468] using wordTrace_append hprefix tailTrace_3580468
  have hstable : (prefixWord ++ tailWord_3580468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580468).length < 2 ^ (prefixWord ++ tailWord_3580468).sum := by decide
  have hdescent : baseEnd_3580468 < baseStart_3580468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580479 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 7]
def baseStart_3580479 : Nat := 118140960795 + 3580479 * 2 ^ 59
def prefixEnd_3580479 : Nat := 4983230072969 + 3 ^ 40 * 3580479 * 2
def baseEnd_3580479 : Nat := 408557044517689354032485

theorem tailTrace_3580479 : CollatzResearch.WordTrace tailWord_3580479 prefixEnd_3580479 408557044517689354032485 := by
  unfold tailWord_3580479
  simp only [CollatzResearch.WordTrace]
  refine ⟨130590797595543554974536491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87060531730362369983024327 130590797595543554974536491)
  ·
    refine ⟨195886196393315332461804737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130590797595543554974536491 195886196393315332461804737)
    ·
      refine ⟨146914647294986499346353553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195886196393315332461804737 146914647294986499346353553)
      ·
        refine ⟨110185985471239874509765165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146914647294986499346353553 110185985471239874509765165)
        ·
          refine ⟨41319744551714952941161937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110185985471239874509765165 41319744551714952941161937)
          ·
            refine ⟨30989808413786214705871453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41319744551714952941161937 30989808413786214705871453)
            ·
              refine ⟨11621178155169830514701795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 30989808413786214705871453 11621178155169830514701795)
              ·
                refine ⟨17431767232754745772052693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11621178155169830514701795 17431767232754745772052693)
                ·
                  refine ⟨408557044517689354032485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17431767232754745772052693 408557044517689354032485)
                  ·
                    rfl

theorem cell22_3580479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 7].length) (baseStart_3580479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580479 prefixEnd_3580479 := by exact prefixLift 3580479
  have htrace : WordTrace (prefixWord ++ tailWord_3580479) baseStart_3580479 baseEnd_3580479 := by
    simpa [prefixWord, tailWord_3580479, baseEnd_3580479] using wordTrace_append hprefix tailTrace_3580479
  have hstable : (prefixWord ++ tailWord_3580479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580479).length < 2 ^ (prefixWord ++ tailWord_3580479).sum := by decide
  have hdescent : baseEnd_3580479 < baseStart_3580479 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580517 : List Nat := [1, 3, 1, 3, 4, 2, 1, 3, 1, 3]
def baseStart_3580517 : Nat := 118140960795 + 3580517 * 2 ^ 59
def prefixEnd_3580517 : Nat := 4983230072969 + 3 ^ 40 * 3580517 * 2
def baseEnd_3580517 : Nat := 1225684141729648629647339

theorem tailTrace_3580517 : CollatzResearch.WordTrace tailWord_3580517 prefixEnd_3580517 1225684141729648629647339 := by
  unfold tailWord_3580517
  simp only [CollatzResearch.WordTrace]
  refine ⟨130592183569405887464419805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87061455712937258309613203 130592183569405887464419805)
  ·
    refine ⟨48972068838527207799157427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130592183569405887464419805 48972068838527207799157427)
    ·
      refine ⟨73458103257790811698736141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48972068838527207799157427 73458103257790811698736141)
      ·
        refine ⟨27546788721671554387026053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73458103257790811698736141 27546788721671554387026053)
        ·
          refine ⟨5165022885313416447567385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27546788721671554387026053 5165022885313416447567385)
          ·
            refine ⟨3873767163985062335675539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5165022885313416447567385 3873767163985062335675539)
            ·
              refine ⟨5810650745977593503513309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3873767163985062335675539 5810650745977593503513309)
              ·
                refine ⟨2178994029741597563817491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5810650745977593503513309 2178994029741597563817491)
                ·
                  refine ⟨3268491044612396345726237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2178994029741597563817491 3268491044612396345726237)
                  ·
                    refine ⟨1225684141729648629647339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3268491044612396345726237 1225684141729648629647339)
                    ·
                      rfl

theorem cell22_3580517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 3, 1, 3].length) (baseStart_3580517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580517 prefixEnd_3580517 := by exact prefixLift 3580517
  have htrace : WordTrace (prefixWord ++ tailWord_3580517) baseStart_3580517 baseEnd_3580517 := by
    simpa [prefixWord, tailWord_3580517, baseEnd_3580517] using wordTrace_append hprefix tailTrace_3580517
  have hstable : (prefixWord ++ tailWord_3580517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580517).length < 2 ^ (prefixWord ++ tailWord_3580517).sum := by decide
  have hdescent : baseEnd_3580517 < baseStart_3580517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580524 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 8]
def baseStart_3580524 : Nat := 118140960795 + 3580524 * 2 ^ 59
def prefixEnd_3580524 : Nat := 4983230072969 + 3 ^ 40 * 3580524 * 2
def baseEnd_3580524 : Nat := 408562179324234314907439

theorem tailTrace_3580524 : CollatzResearch.WordTrace tailWord_3580524 prefixEnd_3580524 408562179324234314907439 := by
  unfold tailWord_3580524
  simp only [CollatzResearch.WordTrace]
  refine ⟨65296219440190263829962313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87061625920253685106616417 65296219440190263829962313)
  ·
    refine ⟨48972164580142697872471735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65296219440190263829962313 48972164580142697872471735)
    ·
      refine ⟨73458246870214046808707603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48972164580142697872471735 73458246870214046808707603)
      ·
        refine ⟨110187370305321070213061405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73458246870214046808707603 110187370305321070213061405)
        ·
          refine ⟨41320263864495401329898027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110187370305321070213061405 41320263864495401329898027)
          ·
            refine ⟨61980395796743101994847041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41320263864495401329898027 61980395796743101994847041)
            ·
              refine ⟨46485296847557326496135281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 61980395796743101994847041 46485296847557326496135281)
              ·
                refine ⟨34863972635667994872101461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46485296847557326496135281 34863972635667994872101461)
                ·
                  refine ⟨408562179324234314907439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34863972635667994872101461 408562179324234314907439)
                  ·
                    rfl

theorem cell22_3580524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 8].length) (baseStart_3580524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580524 prefixEnd_3580524 := by exact prefixLift 3580524
  have htrace : WordTrace (prefixWord ++ tailWord_3580524) baseStart_3580524 baseEnd_3580524 := by
    simpa [prefixWord, tailWord_3580524, baseEnd_3580524] using wordTrace_append hprefix tailTrace_3580524
  have hstable : (prefixWord ++ tailWord_3580524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580524).length < 2 ^ (prefixWord ++ tailWord_3580524).sum := by decide
  have hdescent : baseEnd_3580524 < baseStart_3580524 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580534 : List Nat := [5, 1, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_3580534 : Nat := 118140960795 + 3580534 * 2 ^ 59
def prefixEnd_3580534 : Nat := 4983230072969 + 3 ^ 40 * 3580534 * 2
def baseEnd_3580534 : Nat := 1225689961177066251972287

theorem tailTrace_3580534 : CollatzResearch.WordTrace tailWord_3580534 prefixEnd_3580534 1225689961177066251972287 := by
  unfold tailWord_3580534
  simp only [CollatzResearch.WordTrace]
  refine ⟨8162050225646518710486791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87061869073562866245192437 8162050225646518710486791)
  ·
    refine ⟨12243075338469778065730187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8162050225646518710486791 12243075338469778065730187)
    ·
      refine ⟨18364613007704667098595281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12243075338469778065730187 18364613007704667098595281)
      ·
        refine ⟨13773459755778500323946461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18364613007704667098595281 13773459755778500323946461)
        ·
          refine ⟨5165047408416937621479923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13773459755778500323946461 5165047408416937621479923)
          ·
            refine ⟨7747571112625406432219885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165047408416937621479923 7747571112625406432219885)
            ·
              refine ⟨2905339167234527412082457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7747571112625406432219885 2905339167234527412082457)
              ·
                refine ⟨2179004375425895559061843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2905339167234527412082457 2179004375425895559061843)
                ·
                  refine ⟨3268506563138843338592765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179004375425895559061843 3268506563138843338592765)
                  ·
                    refine ⟨1225689961177066251972287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3268506563138843338592765 1225689961177066251972287)
                    ·
                      rfl

theorem cell22_3580534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_3580534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580534 prefixEnd_3580534 := by exact prefixLift 3580534
  have htrace : WordTrace (prefixWord ++ tailWord_3580534) baseStart_3580534 baseEnd_3580534 := by
    simpa [prefixWord, tailWord_3580534, baseEnd_3580534] using wordTrace_append hprefix tailTrace_3580534
  have hstable : (prefixWord ++ tailWord_3580534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580534).length < 2 ^ (prefixWord ++ tailWord_3580534).sum := by decide
  have hdescent : baseEnd_3580534 < baseStart_3580534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580539 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 5, 5]
def baseStart_3580539 : Nat := 118140960795 + 3580539 * 2 ^ 59
def prefixEnd_3580539 : Nat := 4983230072969 + 3 ^ 40 * 3580539 * 2
def baseEnd_3580539 : Nat := 1225691672779247905597271

theorem tailTrace_3580539 : CollatzResearch.WordTrace tailWord_3580539 prefixEnd_3580539 1225691672779247905597271 := by
  unfold tailWord_3580539
  simp only [CollatzResearch.WordTrace]
  refine ⟨130592985975326185221720671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87061990650217456814480447 130592985975326185221720671)
  ·
    refine ⟨195889478962989277832581007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130592985975326185221720671 195889478962989277832581007)
    ·
      refine ⟨293834218444483916748871511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195889478962989277832581007 293834218444483916748871511)
      ·
        refine ⟨440751327666725875123307267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293834218444483916748871511 440751327666725875123307267)
        ·
          refine ⟨661126991500088812684960901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440751327666725875123307267 661126991500088812684960901)
          ·
            refine ⟨123961310906266652378430169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 661126991500088812684960901 123961310906266652378430169)
            ·
              refine ⟨92970983179699989283822627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123961310906266652378430169 92970983179699989283822627)
              ·
                refine ⟨139456474769549983925733941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 92970983179699989283822627 139456474769549983925733941)
                ·
                  refine ⟨13074044509645310993037557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139456474769549983925733941 13074044509645310993037557)
                  ·
                    refine ⟨1225691672779247905597271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13074044509645310993037557 1225691672779247905597271)
                    ·
                      rfl

theorem cell22_3580539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 5, 5].length) (baseStart_3580539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580539 prefixEnd_3580539 := by exact prefixLift 3580539
  have htrace : WordTrace (prefixWord ++ tailWord_3580539) baseStart_3580539 baseEnd_3580539 := by
    simpa [prefixWord, tailWord_3580539, baseEnd_3580539] using wordTrace_append hprefix tailTrace_3580539
  have hstable : (prefixWord ++ tailWord_3580539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580539).length < 2 ^ (prefixWord ++ tailWord_3580539).sum := by decide
  have hdescent : baseEnd_3580539 < baseStart_3580539 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580556 : List Nat := [2, 2, 1, 2, 1, 1, 2, 2, 6, 3]
def baseStart_3580556 : Nat := 118140960795 + 3580556 * 2 ^ 59
def prefixEnd_3580556 : Nat := 4983230072969 + 3 ^ 40 * 3580556 * 2
def baseEnd_3580556 : Nat := 1225697492226665527922219

theorem tailTrace_3580556 : CollatzResearch.WordTrace tailWord_3580556 prefixEnd_3580556 1225697492226665527922219 := by
  unfold tailWord_3580556
  simp only [CollatzResearch.WordTrace]
  refine ⟨65296803008132298562544761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87062404010843064750059681 65296803008132298562544761)
  ·
    refine ⟨48972602256099223921908571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65296803008132298562544761 48972602256099223921908571)
    ·
      refine ⟨73458903384148835882862857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48972602256099223921908571 73458903384148835882862857)
      ·
        refine ⟨55094177538111626912147143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73458903384148835882862857 55094177538111626912147143)
        ·
          refine ⟨82641266307167440368220715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55094177538111626912147143 82641266307167440368220715)
          ·
            refine ⟨123961899460751160552331073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82641266307167440368220715 123961899460751160552331073)
            ·
              refine ⟨92971424595563370414248305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 123961899460751160552331073 92971424595563370414248305)
              ·
                refine ⟨69728568446672527810686229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 92971424595563370414248305 69728568446672527810686229)
                ·
                  refine ⟨3268526645937774741125917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69728568446672527810686229 3268526645937774741125917)
                  ·
                    refine ⟨1225697492226665527922219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3268526645937774741125917 1225697492226665527922219)
                    ·
                      rfl

theorem cell22_3580556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 6, 3].length) (baseStart_3580556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580556 prefixEnd_3580556 := by exact prefixLift 3580556
  have htrace : WordTrace (prefixWord ++ tailWord_3580556) baseStart_3580556 baseEnd_3580556 := by
    simpa [prefixWord, tailWord_3580556, baseEnd_3580556] using wordTrace_append hprefix tailTrace_3580556
  have hstable : (prefixWord ++ tailWord_3580556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580556).length < 2 ^ (prefixWord ++ tailWord_3580556).sum := by decide
  have hdescent : baseEnd_3580556 < baseStart_3580556 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580569 : List Nat := [1, 2, 1, 2, 1, 2, 3, 10]
def baseStart_3580569 : Nat := 118140960795 + 3580569 * 2 ^ 59
def prefixEnd_3580569 : Nat := 4983230072969 + 3 ^ 40 * 3580569 * 2
def baseEnd_3580569 : Nat := 136189104710259758594131

theorem tailTrace_3580569 : CollatzResearch.WordTrace tailWord_3580569 prefixEnd_3580569 136189104710259758594131 := by
  unfold tailWord_3580569
  simp only [CollatzResearch.WordTrace]
  refine ⟨130594080165217500345312761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87062720110145000230208507 130594080165217500345312761)
  ·
    refine ⟨97945560123913125258984571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130594080165217500345312761 97945560123913125258984571)
    ·
      refine ⟨146918340185869687888476857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97945560123913125258984571 146918340185869687888476857)
      ·
        refine ⟨110188755139402265916357643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146918340185869687888476857 110188755139402265916357643)
        ·
          refine ⟨165283132709103398874536465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110188755139402265916357643 165283132709103398874536465)
          ·
            refine ⟨123962349531827549155902349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165283132709103398874536465 123962349531827549155902349)
            ·
              refine ⟨46485881074435330933463381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123962349531827549155902349 46485881074435330933463381)
              ·
                refine ⟨136189104710259758594131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 46485881074435330933463381 136189104710259758594131)
                ·
                  rfl

theorem cell22_3580569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 10].length) (baseStart_3580569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580569 prefixEnd_3580569 := by exact prefixLift 3580569
  have htrace : WordTrace (prefixWord ++ tailWord_3580569) baseStart_3580569 baseEnd_3580569 := by
    simpa [prefixWord, tailWord_3580569, baseEnd_3580569] using wordTrace_append hprefix tailTrace_3580569
  have hstable : (prefixWord ++ tailWord_3580569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580569).length < 2 ^ (prefixWord ++ tailWord_3580569).sum := by decide
  have hdescent : baseEnd_3580569 < baseStart_3580569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580618 : List Nat := [3, 1, 2, 1, 4, 1, 1, 1, 5, 3]
def baseStart_3580618 : Nat := 118140960795 + 3580618 * 2 ^ 59
def prefixEnd_3580618 : Nat := 4983230072969 + 3 ^ 40 * 3580618 * 2
def baseEnd_3580618 : Nat := 1225718716093718032872029

theorem tailTrace_3580618 : CollatzResearch.WordTrace tailWord_3580618 prefixEnd_3580618 1225718716093718032872029 := by
  unfold tailWord_3580618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32648966835509995428461627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87063911561359987809231005 32648966835509995428461627)
  ·
    refine ⟨48973450253264993142692441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32648966835509995428461627 48973450253264993142692441)
    ·
      refine ⟨36730087689948744857019331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48973450253264993142692441 36730087689948744857019331)
      ·
        refine ⟨55095131534923117285528997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36730087689948744857019331 55095131534923117285528997)
        ·
          refine ⟨10330337162798084491036687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55095131534923117285528997 10330337162798084491036687)
          ·
            refine ⟨15495505744197126736555031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10330337162798084491036687 15495505744197126736555031)
            ·
              refine ⟨23243258616295690104832547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15495505744197126736555031 23243258616295690104832547)
              ·
                refine ⟨34864887924443535157248821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23243258616295690104832547 34864887924443535157248821)
                ·
                  refine ⟨3268583242916581420992077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34864887924443535157248821 3268583242916581420992077)
                  ·
                    refine ⟨1225718716093718032872029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3268583242916581420992077 1225718716093718032872029)
                    ·
                      rfl

theorem cell22_3580618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 1, 5, 3].length) (baseStart_3580618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580618 prefixEnd_3580618 := by exact prefixLift 3580618
  have htrace : WordTrace (prefixWord ++ tailWord_3580618) baseStart_3580618 baseEnd_3580618 := by
    simpa [prefixWord, tailWord_3580618, baseEnd_3580618] using wordTrace_append hprefix tailTrace_3580618
  have hstable : (prefixWord ++ tailWord_3580618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580618).length < 2 ^ (prefixWord ++ tailWord_3580618).sum := by decide
  have hdescent : baseEnd_3580618 < baseStart_3580618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580648 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 7]
def baseStart_3580648 : Nat := 118140960795 + 3580648 * 2 ^ 59
def prefixEnd_3580648 : Nat := 4983230072969 + 3 ^ 40 * 3580648 * 2
def baseEnd_3580648 : Nat := 408576328568935984873979

theorem tailTrace_3580648 : CollatzResearch.WordTrace tailWord_3580648 prefixEnd_3580648 408576328568935984873979 := by
  unfold tailWord_3580648
  simp only [CollatzResearch.WordTrace]
  refine ⟨65298480765965648418719299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87064641021287531224959065 65298480765965648418719299)
  ·
    refine ⟨97947721148948472628078949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65298480765965648418719299 97947721148948472628078949)
    ·
      refine ⟨18365197715427838617764803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 97947721148948472628078949 18365197715427838617764803)
      ·
        refine ⟨27547796573141757926647205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18365197715427838617764803 27547796573141757926647205)
        ·
          refine ⟨5165211857464079611246351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27547796573141757926647205 5165211857464079611246351)
          ·
            refine ⟨7747817786196119416869527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5165211857464079611246351 7747817786196119416869527)
            ·
              refine ⟨11621726679294179125304291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7747817786196119416869527 11621726679294179125304291)
              ·
                refine ⟨17432590018941268687956437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11621726679294179125304291 17432590018941268687956437)
                ·
                  refine ⟨408576328568935984873979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17432590018941268687956437 408576328568935984873979)
                  ·
                    rfl

theorem cell22_3580648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 7].length) (baseStart_3580648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580648 prefixEnd_3580648 := by exact prefixLift 3580648
  have htrace : WordTrace (prefixWord ++ tailWord_3580648) baseStart_3580648 baseEnd_3580648 := by
    simpa [prefixWord, tailWord_3580648, baseEnd_3580648] using wordTrace_append hprefix tailTrace_3580648
  have hstable : (prefixWord ++ tailWord_3580648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580648).length < 2 ^ (prefixWord ++ tailWord_3580648).sum := by decide
  have hdescent : baseEnd_3580648 < baseStart_3580648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580691 : List Nat := [1, 1, 1, 2, 1, 3, 4, 1, 3, 5]
def baseStart_3580691 : Nat := 118140960795 + 3580691 * 2 ^ 59
def prefixEnd_3580691 : Nat := 4983230072969 + 3 ^ 40 * 3580691 * 2
def baseEnd_3580691 : Nat := 1225743705485570175796805

theorem tailTrace_3580691 : CollatzResearch.WordTrace tailWord_3580691 prefixEnd_3580691 1225743705485570175796805 := by
  unfold tailWord_3580691
  simp only [CollatzResearch.WordTrace]
  refine ⟨130598529870775515181253927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87065686580517010120835951 130598529870775515181253927)
  ·
    refine ⟨195897794806163272771880891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130598529870775515181253927 195897794806163272771880891)
    ·
      refine ⟨293846692209244909157821337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195897794806163272771880891 293846692209244909157821337)
      ·
        refine ⟨220385019156933681868366003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293846692209244909157821337 220385019156933681868366003)
        ·
          refine ⟨330577528735400522802549005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220385019156933681868366003 330577528735400522802549005)
          ·
            refine ⟨123966573275775196050955877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330577528735400522802549005 123966573275775196050955877)
            ·
              refine ⟨23243732489207849259554227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 123966573275775196050955877 23243732489207849259554227)
              ·
                refine ⟨34865598733811773889331341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23243732489207849259554227 34865598733811773889331341)
                ·
                  refine ⟨13074599525179415208499253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34865598733811773889331341 13074599525179415208499253)
                  ·
                    refine ⟨1225743705485570175796805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13074599525179415208499253 1225743705485570175796805)
                    ·
                      rfl

theorem cell22_3580691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 5].length) (baseStart_3580691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580691 prefixEnd_3580691 := by exact prefixLift 3580691
  have htrace : WordTrace (prefixWord ++ tailWord_3580691) baseStart_3580691 baseEnd_3580691 := by
    simpa [prefixWord, tailWord_3580691, baseEnd_3580691] using wordTrace_append hprefix tailTrace_3580691
  have hstable : (prefixWord ++ tailWord_3580691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580691).length < 2 ^ (prefixWord ++ tailWord_3580691).sum := by decide
  have hdescent : baseEnd_3580691 < baseStart_3580691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580736 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 2, 7]
def baseStart_3580736 : Nat := 118140960795 + 3580736 * 2 ^ 59
def prefixEnd_3580736 : Nat := 4983230072969 + 3 ^ 40 * 3580736 * 2
def baseEnd_3580736 : Nat := 1225759109905205058421667

theorem tailTrace_3580736 : CollatzResearch.WordTrace tailWord_3580736 prefixEnd_3580736 1225759109905205058421667 := by
  unfold tailWord_3580736
  simp only [CollatzResearch.WordTrace]
  refine ⟨65300085577806243933321031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87066780770408325244428041 65300085577806243933321031)
  ·
    refine ⟨97950128366709365899981547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65300085577806243933321031 97950128366709365899981547)
    ·
      refine ⟨146925192550064048849972321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97950128366709365899981547 146925192550064048849972321)
      ·
        refine ⟨110193894412548036637479241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146925192550064048849972321 110193894412548036637479241)
        ·
          refine ⟨82645420809411027478109431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110193894412548036637479241 82645420809411027478109431)
          ·
            refine ⟨123968131214116541217164147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82645420809411027478109431 123968131214116541217164147)
            ·
              refine ⟨185952196821174811825746221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123968131214116541217164147 185952196821174811825746221)
              ·
                refine ⟨69732073807940554434654833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 185952196821174811825746221 69732073807940554434654833)
                ·
                  refine ⟨52299055355955415825991125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69732073807940554434654833 52299055355955415825991125)
                  ·
                    refine ⟨1225759109905205058421667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52299055355955415825991125 1225759109905205058421667)
                    ·
                      rfl

theorem cell22_3580736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 2, 7].length) (baseStart_3580736 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580736 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580736 prefixEnd_3580736 := by exact prefixLift 3580736
  have htrace : WordTrace (prefixWord ++ tailWord_3580736) baseStart_3580736 baseEnd_3580736 := by
    simpa [prefixWord, tailWord_3580736, baseEnd_3580736] using wordTrace_append hprefix tailTrace_3580736
  have hstable : (prefixWord ++ tailWord_3580736).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580736).length < 2 ^ (prefixWord ++ tailWord_3580736).sum := by decide
  have hdescent : baseEnd_3580736 < baseStart_3580736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580751 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 6, 6]
def baseStart_3580751 : Nat := 118140960795 + 3580751 * 2 ^ 59
def prefixEnd_3580751 : Nat := 4983230072969 + 3 ^ 40 * 3580751 * 2
def baseEnd_3580751 : Nat := 1225764244711750019296621

theorem tailTrace_3580751 : CollatzResearch.WordTrace tailWord_3580751 prefixEnd_3580751 1225764244711750019296621 := by
  unfold tailWord_3580751
  simp only [CollatzResearch.WordTrace]
  refine ⟨130600718250558145428438107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87067145500372096952292071 130600718250558145428438107)
  ·
    refine ⟨195901077375837218142657161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130600718250558145428438107 195901077375837218142657161)
    ·
      refine ⟨146925808031877913606992871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195901077375837218142657161 146925808031877913606992871)
      ·
        refine ⟨220388712047816870410489307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146925808031877913606992871 220388712047816870410489307)
        ·
          refine ⟨330583068071725305615733961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220388712047816870410489307 330583068071725305615733961)
          ·
            refine ⟨247937301053793979211800471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330583068071725305615733961 247937301053793979211800471)
            ·
              refine ⟨371905951580690968817700707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 247937301053793979211800471 371905951580690968817700707)
              ·
                refine ⟨557858927371036453226551061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 371905951580690968817700707 557858927371036453226551061)
                ·
                  refine ⟨26149637220517333744994581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 557858927371036453226551061 26149637220517333744994581)
                  ·
                    refine ⟨1225764244711750019296621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26149637220517333744994581 1225764244711750019296621)
                    ·
                      rfl

theorem cell22_3580751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 6].length) (baseStart_3580751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580751 prefixEnd_3580751 := by exact prefixLift 3580751
  have htrace : WordTrace (prefixWord ++ tailWord_3580751) baseStart_3580751 baseEnd_3580751 := by
    simpa [prefixWord, tailWord_3580751, baseEnd_3580751] using wordTrace_append hprefix tailTrace_3580751
  have hstable : (prefixWord ++ tailWord_3580751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580751).length < 2 ^ (prefixWord ++ tailWord_3580751).sum := by decide
  have hdescent : baseEnd_3580751 < baseStart_3580751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580858 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 1, 6]
def baseStart_3580858 : Nat := 118140960795 + 3580858 * 2 ^ 59
def prefixEnd_3580858 : Nat := 4983230072969 + 3 ^ 40 * 3580858 * 2
def baseEnd_3580858 : Nat := 1225800872998437406871293

theorem tailTrace_3580858 : CollatzResearch.WordTrace tailWord_3580858 prefixEnd_3580858 1225800872998437406871293 := by
  unfold tailWord_3580858
  simp only [CollatzResearch.WordTrace]
  refine ⟨32651155215292625675645807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87069747240780335135055485 32651155215292625675645807)
  ·
    refine ⟨48976732822938938513468711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32651155215292625675645807 48976732822938938513468711)
    ·
      refine ⟨73465099234408407770203067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48976732822938938513468711 73465099234408407770203067)
      ·
        refine ⟨110197648851612611655304601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73465099234408407770203067 110197648851612611655304601)
        ·
          refine ⟨82648236638709458741478451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110197648851612611655304601 82648236638709458741478451)
          ·
            refine ⟨123972354958064188112217677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82648236638709458741478451 123972354958064188112217677)
            ·
              refine ⟨46489633109274070542081629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 123972354958064188112217677 46489633109274070542081629)
              ·
                refine ⟨17433612415977776453280611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46489633109274070542081629 17433612415977776453280611)
                ·
                  refine ⟨26150418623966664679920917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17433612415977776453280611 26150418623966664679920917)
                  ·
                    refine ⟨1225800872998437406871293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26150418623966664679920917 1225800872998437406871293)
                    ·
                      rfl

theorem cell22_3580858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 1, 6].length) (baseStart_3580858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580858 prefixEnd_3580858 := by exact prefixLift 3580858
  have htrace : WordTrace (prefixWord ++ tailWord_3580858) baseStart_3580858 baseEnd_3580858 := by
    simpa [prefixWord, tailWord_3580858, baseEnd_3580858] using wordTrace_append hprefix tailTrace_3580858
  have hstable : (prefixWord ++ tailWord_3580858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580858).length < 2 ^ (prefixWord ++ tailWord_3580858).sum := by decide
  have hdescent : baseEnd_3580858 < baseStart_3580858 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580875 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 2, 4]
def baseStart_3580875 : Nat := 118140960795 + 3580875 * 2 ^ 59
def prefixEnd_3580875 : Nat := 4983230072969 + 3 ^ 40 * 3580875 * 2
def baseEnd_3580875 : Nat := 1225806692445855029196241

theorem tailTrace_3580875 : CollatzResearch.WordTrace tailWord_3580875 prefixEnd_3580875 1225806692445855029196241 := by
  unfold tailWord_3580875
  simp only [CollatzResearch.WordTrace]
  refine ⟨130605240902108914605952079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87070160601405943070634719 130605240902108914605952079)
  ·
    refine ⟨195907861353163371908928119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130605240902108914605952079 195907861353163371908928119)
    ·
      refine ⟨293861792029745057863392179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195907861353163371908928119 293861792029745057863392179)
      ·
        refine ⟨440792688044617586795088269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293861792029745057863392179 440792688044617586795088269)
        ·
          refine ⟨165297258016731595048158101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 440792688044617586795088269 165297258016731595048158101)
          ·
            refine ⟨7748308969534293517882411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165297258016731595048158101 7748308969534293517882411)
            ·
              refine ⟨11622463454301440276823617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7748308969534293517882411 11622463454301440276823617)
              ·
                refine ⟨8716847590726080207617713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11622463454301440276823617 8716847590726080207617713)
                ·
                  refine ⟨6537635693044560155713285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8716847590726080207617713 6537635693044560155713285)
                  ·
                    refine ⟨1225806692445855029196241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6537635693044560155713285 1225806692445855029196241)
                    ·
                      rfl

theorem cell22_3580875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 2, 4].length) (baseStart_3580875 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580875 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580875 prefixEnd_3580875 := by exact prefixLift 3580875
  have htrace : WordTrace (prefixWord ++ tailWord_3580875) baseStart_3580875 baseEnd_3580875 := by
    simpa [prefixWord, tailWord_3580875, baseEnd_3580875] using wordTrace_append hprefix tailTrace_3580875
  have hstable : (prefixWord ++ tailWord_3580875).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580875).length < 2 ^ (prefixWord ++ tailWord_3580875).sum := by decide
  have hdescent : baseEnd_3580875 < baseStart_3580875 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580890 : List Nat := [3, 1, 1, 2, 4, 2, 2, 7]
def baseStart_3580890 : Nat := 118140960795 + 3580890 * 2 ^ 59
def prefixEnd_3580890 : Nat := 4983230072969 + 3 ^ 40 * 3580890 * 2
def baseEnd_3580890 : Nat := 136201314139155554452355

theorem tailTrace_3580890 : CollatzResearch.WordTrace tailWord_3580890 prefixEnd_3580890 136201314139155554452355 := by
  unfold tailWord_3580890
  simp only [CollatzResearch.WordTrace]
  refine ⟨32651446999263643041937031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87070525331369714778498749 32651446999263643041937031)
  ·
    refine ⟨48977170498895464562905547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32651446999263643041937031 48977170498895464562905547)
    ·
      refine ⟨73465755748343196844358321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48977170498895464562905547 73465755748343196844358321)
      ·
        refine ⟨55099316811257397633268741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73465755748343196844358321 55099316811257397633268741)
        ·
          refine ⟨10331121902110762056237889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55099316811257397633268741 10331121902110762056237889)
          ·
            refine ⟨7748341426583071542178417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10331121902110762056237889 7748341426583071542178417)
            ·
              refine ⟨5811256069937303656633813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7748341426583071542178417 5811256069937303656633813)
              ·
                refine ⟨136201314139155554452355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5811256069937303656633813 136201314139155554452355)
                ·
                  rfl

theorem cell22_3580890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 7].length) (baseStart_3580890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580890 prefixEnd_3580890 := by exact prefixLift 3580890
  have htrace : WordTrace (prefixWord ++ tailWord_3580890) baseStart_3580890 baseEnd_3580890 := by
    simpa [prefixWord, tailWord_3580890, baseEnd_3580890] using wordTrace_append hprefix tailTrace_3580890
  have hstable : (prefixWord ++ tailWord_3580890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580890).length < 2 ^ (prefixWord ++ tailWord_3580890).sum := by decide
  have hdescent : baseEnd_3580890 < baseStart_3580890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580930 : List Nat := [3, 4, 1, 3, 2, 1, 2, 2, 4]
def baseStart_3580930 : Nat := 118140960795 + 3580930 * 2 ^ 59
def prefixEnd_3580930 : Nat := 4983230072969 + 3 ^ 40 * 3580930 * 2
def baseEnd_3580930 : Nat := 408608506689951073023691

theorem tailTrace_3580930 : CollatzResearch.WordTrace tailWord_3580930 prefixEnd_3580930 408608506689951073023691 := by
  unfold tailWord_3580930
  simp only [CollatzResearch.WordTrace]
  refine ⟨32651811729227414749801061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87071497944606439332802829 32651811729227414749801061)
  ·
    refine ⟨6122214699230140265587699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32651811729227414749801061 6122214699230140265587699)
    ·
      refine ⟨9183322048845210398381549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6122214699230140265587699 9183322048845210398381549)
      ·
        refine ⟨3443745768316953899393081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9183322048845210398381549 3443745768316953899393081)
        ·
          refine ⟨2582809326237715424544811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3443745768316953899393081 2582809326237715424544811)
          ·
            refine ⟨3874213989356573136817217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2582809326237715424544811 3874213989356573136817217)
            ·
              refine ⟨2905660492017429852612913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3874213989356573136817217 2905660492017429852612913)
              ·
                refine ⟨2179245369013072389459685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2905660492017429852612913 2179245369013072389459685)
                ·
                  refine ⟨408608506689951073023691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2179245369013072389459685 408608506689951073023691)
                  ·
                    rfl

theorem cell22_3580930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_3580930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580930 prefixEnd_3580930 := by exact prefixLift 3580930
  have htrace : WordTrace (prefixWord ++ tailWord_3580930) baseStart_3580930 baseEnd_3580930 := by
    simpa [prefixWord, tailWord_3580930, baseEnd_3580930] using wordTrace_append hprefix tailTrace_3580930
  have hstable : (prefixWord ++ tailWord_3580930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580930).length < 2 ^ (prefixWord ++ tailWord_3580930).sum := by decide
  have hdescent : baseEnd_3580930 < baseStart_3580930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580939 : List Nat := [1, 1, 1, 1, 6, 3, 1, 4, 1, 3]
def baseStart_3580939 : Nat := 118140960795 + 3580939 * 2 ^ 59
def prefixEnd_3580939 : Nat := 4983230072969 + 3 ^ 40 * 3580939 * 2
def baseEnd_3580939 : Nat := 1225828600953780195596045

theorem tailTrace_3580939 : CollatzResearch.WordTrace tailWord_3580939 prefixEnd_3580939 1225828600953780195596045 := by
  unfold tailWord_3580939
  simp only [CollatzResearch.WordTrace]
  refine ⟨130607575173877053536281871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87071716782584702357521247 130607575173877053536281871)
  ·
    refine ⟨195911362760815580304422807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130607575173877053536281871 195911362760815580304422807)
    ·
      refine ⟨293867044141223370456634211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195911362760815580304422807 293867044141223370456634211)
      ·
        refine ⟨440800566211835055684951317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293867044141223370456634211 440800566211835055684951317)
        ·
          refine ⟨20662526541179768235232093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 440800566211835055684951317 20662526541179768235232093)
          ·
            refine ⟨7748447452942413088212035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20662526541179768235232093 7748447452942413088212035)
            ·
              refine ⟨11622671179413619632318053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7748447452942413088212035 11622671179413619632318053)
              ·
                refine ⟨2179250846140053681059635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11622671179413619632318053 2179250846140053681059635)
                ·
                  refine ⟨3268876269210080521589453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179250846140053681059635 3268876269210080521589453)
                  ·
                    refine ⟨1225828600953780195596045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3268876269210080521589453 1225828600953780195596045)
                    ·
                      rfl

theorem cell22_3580939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 4, 1, 3].length) (baseStart_3580939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580939 prefixEnd_3580939 := by exact prefixLift 3580939
  have htrace : WordTrace (prefixWord ++ tailWord_3580939) baseStart_3580939 baseEnd_3580939 := by
    simpa [prefixWord, tailWord_3580939, baseEnd_3580939] using wordTrace_append hprefix tailTrace_3580939
  have hstable : (prefixWord ++ tailWord_3580939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580939).length < 2 ^ (prefixWord ++ tailWord_3580939).sum := by decide
  have hdescent : baseEnd_3580939 < baseStart_3580939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580965 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 3, 4]
def baseStart_3580965 : Nat := 118140960795 + 3580965 * 2 ^ 59
def prefixEnd_3580965 : Nat := 4983230072969 + 3 ^ 40 * 3580965 * 2
def baseEnd_3580965 : Nat := 1225837501285124794445965

theorem tailTrace_3580965 : CollatzResearch.WordTrace tailWord_3580965 prefixEnd_3580965 1225837501285124794445965 := by
  unfold tailWord_3580965
  simp only [CollatzResearch.WordTrace]
  refine ⟨130608523471782859976728349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87072348981188573317818899 130608523471782859976728349)
  ·
    refine ⟨48978196301918572491273131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130608523471782859976728349 48978196301918572491273131)
    ·
      refine ⟨73467294452877858736909697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48978196301918572491273131 73467294452877858736909697)
      ·
        refine ⟨55100470839658394052682273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73467294452877858736909697 55100470839658394052682273)
        ·
          refine ⟨41325353129743795539511705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55100470839658394052682273 41325353129743795539511705)
          ·
            refine ⟨30994014847307846654633779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41325353129743795539511705 30994014847307846654633779)
            ·
              refine ⟨46491022270961769981950669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30994014847307846654633779 46491022270961769981950669)
              ·
                refine ⟨17434133351610663743231501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46491022270961769981950669 17434133351610663743231501)
                ·
                  refine ⟨6537800006853998903711813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17434133351610663743231501 6537800006853998903711813)
                  ·
                    refine ⟨1225837501285124794445965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6537800006853998903711813 1225837501285124794445965)
                    ·
                      rfl

theorem cell22_3580965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 4].length) (baseStart_3580965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580965 prefixEnd_3580965 := by exact prefixLift 3580965
  have htrace : WordTrace (prefixWord ++ tailWord_3580965) baseStart_3580965 baseEnd_3580965 := by
    simpa [prefixWord, tailWord_3580965, baseEnd_3580965] using wordTrace_append hprefix tailTrace_3580965
  have hstable : (prefixWord ++ tailWord_3580965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580965).length < 2 ^ (prefixWord ++ tailWord_3580965).sum := by decide
  have hdescent : baseEnd_3580965 < baseStart_3580965 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3580997 : List Nat := [1, 3, 1, 1, 1, 3, 4, 4, 4]
def baseStart_3580997 : Nat := 118140960795 + 3580997 * 2 ^ 59
def prefixEnd_3580997 : Nat := 4983230072969 + 3 ^ 40 * 3580997 * 2
def baseEnd_3580997 : Nat := 408616151846362459215289

theorem tailTrace_3580997 : CollatzResearch.WordTrace tailWord_3580997 prefixEnd_3580997 408616151846362459215289 := by
  unfold tailWord_3580997
  simp only [CollatzResearch.WordTrace]
  refine ⟨130609690607666929441893245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87073127071777952961262163 130609690607666929441893245)
  ·
    refine ⟨48978633977875098540709967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130609690607666929441893245 48978633977875098540709967)
    ·
      refine ⟨73467950966812647811064951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48978633977875098540709967 73467950966812647811064951)
      ·
        refine ⟨110201926450218971716597427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73467950966812647811064951 110201926450218971716597427)
        ·
          refine ⟨165302889675328457574896141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110201926450218971716597427 165302889675328457574896141)
          ·
            refine ⟨61988583628248171590586053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165302889675328457574896141 61988583628248171590586053)
            ·
              refine ⟨11622859430296532173234885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61988583628248171590586053 11622859430296532173234885)
              ·
                refine ⟨2179286143180599782481541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11622859430296532173234885 2179286143180599782481541)
                ·
                  refine ⟨408616151846362459215289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2179286143180599782481541 408616151846362459215289)
                  ·
                    rfl

theorem cell22_3580997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_3580997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3580997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3580997 prefixEnd_3580997 := by exact prefixLift 3580997
  have htrace : WordTrace (prefixWord ++ tailWord_3580997) baseStart_3580997 baseEnd_3580997 := by
    simpa [prefixWord, tailWord_3580997, baseEnd_3580997] using wordTrace_append hprefix tailTrace_3580997
  have hstable : (prefixWord ++ tailWord_3580997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3580997).length < 2 ^ (prefixWord ++ tailWord_3580997).sum := by decide
  have hdescent : baseEnd_3580997 < baseStart_3580997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3580997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581012 : List Nat := [2, 4, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_3581012 : Nat := 118140960795 + 3581012 * 2 ^ 59
def prefixEnd_3581012 : Nat := 4983230072969 + 3 ^ 40 * 3581012 * 2
def baseEnd_3581012 : Nat := 1225853590345632338520821

theorem tailTrace_3581012 : CollatzResearch.WordTrace tailWord_3581012 prefixEnd_3581012 1225853590345632338520821 := by
  unfold tailWord_3581012
  simp only [CollatzResearch.WordTrace]
  refine ⟨65305118851306293501844645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87073491801741724669126193 65305118851306293501844645)
  ·
    refine ⟨12244709784619930031595871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65305118851306293501844645 12244709784619930031595871)
    ·
      refine ⟨18367064676929895047393807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12244709784619930031595871 18367064676929895047393807)
      ·
        refine ⟨27550597015394842571090711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18367064676929895047393807 27550597015394842571090711)
        ·
          refine ⟨41325895523092263856636067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27550597015394842571090711 41325895523092263856636067)
          ·
            refine ⟨61988843284638395784954101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41325895523092263856636067 61988843284638395784954101)
            ·
              refine ⟨5811454057934849604839447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 61988843284638395784954101 5811454057934849604839447)
              ·
                refine ⟨8717181086902274407259171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5811454057934849604839447 8717181086902274407259171)
                ·
                  refine ⟨13075771630353411610888757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8717181086902274407259171 13075771630353411610888757)
                  ·
                    refine ⟨1225853590345632338520821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13075771630353411610888757 1225853590345632338520821)
                    ·
                      rfl

theorem cell22_3581012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_3581012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581012 prefixEnd_3581012 := by exact prefixLift 3581012
  have htrace : WordTrace (prefixWord ++ tailWord_3581012) baseStart_3581012 baseEnd_3581012 := by
    simpa [prefixWord, tailWord_3581012, baseEnd_3581012] using wordTrace_append hprefix tailTrace_3581012
  have hstable : (prefixWord ++ tailWord_3581012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581012).length < 2 ^ (prefixWord ++ tailWord_3581012).sum := by decide
  have hdescent : baseEnd_3581012 < baseStart_3581012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581117 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 3, 4]
def baseStart_3581117 : Nat := 118140960795 + 3581117 * 2 ^ 59
def prefixEnd_3581117 : Nat := 4983230072969 + 3 ^ 40 * 3581117 * 2
def baseEnd_3581117 : Nat := 1225889533991447064645499

theorem tailTrace_3581117 : CollatzResearch.WordTrace tailWord_3581117 prefixEnd_3581117 1225889533991447064645499 := by
  unfold tailWord_3581117
  simp only [CollatzResearch.WordTrace]
  refine ⟨130614067367232189936261605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87076044911488126624174403 130614067367232189936261605)
  ·
    refine ⟨24490137631356035613049051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130614067367232189936261605 24490137631356035613049051)
    ·
      refine ⟨36735206447034053419573577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24490137631356035613049051 36735206447034053419573577)
      ·
        refine ⟨27551404835275540064680183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36735206447034053419573577 27551404835275540064680183)
        ·
          refine ⟨41327107252913310097020275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27551404835275540064680183 41327107252913310097020275)
          ·
            refine ⟨61990660879369965145530413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41327107252913310097020275 61990660879369965145530413)
            ·
              refine ⟨23246497829763736929573905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 61990660879369965145530413 23246497829763736929573905)
              ·
                refine ⟨17434873372322802697180429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23246497829763736929573905 17434873372322802697180429)
                ·
                  refine ⟨6538077514621051011442661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17434873372322802697180429 6538077514621051011442661)
                  ·
                    refine ⟨1225889533991447064645499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6538077514621051011442661 1225889533991447064645499)
                    ·
                      rfl

theorem cell22_3581117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_3581117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581117 prefixEnd_3581117 := by exact prefixLift 3581117
  have htrace : WordTrace (prefixWord ++ tailWord_3581117) baseStart_3581117 baseEnd_3581117 := by
    simpa [prefixWord, tailWord_3581117, baseEnd_3581117] using wordTrace_append hprefix tailTrace_3581117
  have hstable : (prefixWord ++ tailWord_3581117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581117).length < 2 ^ (prefixWord ++ tailWord_3581117).sum := by decide
  have hdescent : baseEnd_3581117 < baseStart_3581117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581164 : List Nat := [2, 2, 1, 1, 2, 5, 1, 1, 4, 3]
def baseStart_3581164 : Nat := 118140960795 + 3581164 * 2 ^ 59
def prefixEnd_3581164 : Nat := 4983230072969 + 3 ^ 40 * 3581164 * 2
def baseEnd_3581164 : Nat := 1225905623051954608720355

theorem tailTrace_3581164 : CollatzResearch.WordTrace tailWord_3581164 prefixEnd_3581164 1225905623051954608720355 := by
  unfold tailWord_3581164
  simp only [CollatzResearch.WordTrace]
  refine ⟨65307890799030958481611273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87077187732041277975481697 65307890799030958481611273)
  ·
    refine ⟨48980918099273218861208455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65307890799030958481611273 48980918099273218861208455)
    ·
      refine ⟨73471377148909828291812683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48980918099273218861208455 73471377148909828291812683)
      ·
        refine ⟨110207065723364742437719025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73471377148909828291812683 110207065723364742437719025)
        ·
          refine ⟨82655299292523556828289269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110207065723364742437719025 82655299292523556828289269)
          ·
            refine ⟨7748934308674083452652119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82655299292523556828289269 7748934308674083452652119)
            ·
              refine ⟨11623401463011125178978179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7748934308674083452652119 11623401463011125178978179)
              ·
                refine ⟨17435102194516687768467269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11623401463011125178978179 17435102194516687768467269)
                ·
                  refine ⟨3269081661471878956587613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17435102194516687768467269 3269081661471878956587613)
                  ·
                    refine ⟨1225905623051954608720355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3269081661471878956587613 1225905623051954608720355)
                    ·
                      rfl

theorem cell22_3581164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 3].length) (baseStart_3581164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581164 prefixEnd_3581164 := by exact prefixLift 3581164
  have htrace : WordTrace (prefixWord ++ tailWord_3581164) baseStart_3581164 baseEnd_3581164 := by
    simpa [prefixWord, tailWord_3581164, baseEnd_3581164] using wordTrace_append hprefix tailTrace_3581164
  have hstable : (prefixWord ++ tailWord_3581164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581164).length < 2 ^ (prefixWord ++ tailWord_3581164).sum := by decide
  have hdescent : baseEnd_3581164 < baseStart_3581164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581301 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 6]
def baseStart_3581301 : Nat := 118140960795 + 3581301 * 2 ^ 59
def prefixEnd_3581301 : Nat := 4983230072969 + 3 ^ 40 * 3581301 * 2
def baseEnd_3581301 : Nat := 408650840317243972681645

theorem tailTrace_3581301 : CollatzResearch.WordTrace tailWord_3581301 prefixEnd_3581301 408650840317243972681645 := by
  unfold tailWord_3581301
  simp only [CollatzResearch.WordTrace]
  refine ⟨130620778398565589360959757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87080518932377059573973171 130620778398565589360959757)
  ·
    refine ⟨48982791899462096010359909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130620778398565589360959757 48982791899462096010359909)
    ·
      refine ⟨9184273481149143001942483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 48982791899462096010359909 9184273481149143001942483)
      ·
        refine ⟨13776410221723714502913725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9184273481149143001942483 13776410221723714502913725)
        ·
          refine ⟨5166153833146392938592647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13776410221723714502913725 5166153833146392938592647)
          ·
            refine ⟨7749230749719589407888971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166153833146392938592647 7749230749719589407888971)
            ·
              refine ⟨11623846124579384111833457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7749230749719589407888971 11623846124579384111833457)
              ·
                refine ⟨8717884593434538083875093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11623846124579384111833457 8717884593434538083875093)
                ·
                  refine ⟨408650840317243972681645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8717884593434538083875093 408650840317243972681645)
                  ·
                    rfl

theorem cell22_3581301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 6].length) (baseStart_3581301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581301 prefixEnd_3581301 := by exact prefixLift 3581301
  have htrace : WordTrace (prefixWord ++ tailWord_3581301) baseStart_3581301 baseEnd_3581301 := by
    simpa [prefixWord, tailWord_3581301, baseEnd_3581301] using wordTrace_append hprefix tailTrace_3581301
  have hstable : (prefixWord ++ tailWord_3581301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581301).length < 2 ^ (prefixWord ++ tailWord_3581301).sum := by decide
  have hdescent : baseEnd_3581301 < baseStart_3581301 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581312 : List Nat := [2, 1, 1, 2, 1, 2, 1, 12]
def baseStart_3581312 : Nat := 118140960795 + 3581312 * 2 ^ 59
def prefixEnd_3581312 : Nat := 4983230072969 + 3 ^ 40 * 3581312 * 2
def baseEnd_3581312 : Nat := 136217365164059061779989

theorem tailTrace_3581312 : CollatzResearch.WordTrace tailWord_3581312 prefixEnd_3581312 136217365164059061779989 := by
  unfold tailWord_3581312
  simp only [CollatzResearch.WordTrace]
  refine ⟨65310589800762869119805095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87080786401017158826406793 65310589800762869119805095)
  ·
    refine ⟨97965884701144303679707643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65310589800762869119805095 97965884701144303679707643)
    ·
      refine ⟨146948827051716455519561465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97965884701144303679707643 146948827051716455519561465)
      ·
        refine ⟨110211620288787341639671099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146948827051716455519561465 110211620288787341639671099)
        ·
          refine ⟨165317430433181012459506649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110211620288787341639671099 165317430433181012459506649)
          ·
            refine ⟨123988072824885759344629987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165317430433181012459506649 123988072824885759344629987)
            ·
              refine ⟨185982109237328639016944981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 123988072824885759344629987 185982109237328639016944981)
              ·
                refine ⟨136217365164059061779989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 185982109237328639016944981 136217365164059061779989)
                ·
                  rfl

theorem cell22_3581312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 12].length) (baseStart_3581312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581312 prefixEnd_3581312 := by exact prefixLift 3581312
  have htrace : WordTrace (prefixWord ++ tailWord_3581312) baseStart_3581312 baseEnd_3581312 := by
    simpa [prefixWord, tailWord_3581312, baseEnd_3581312] using wordTrace_append hprefix tailTrace_3581312
  have hstable : (prefixWord ++ tailWord_3581312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581312).length < 2 ^ (prefixWord ++ tailWord_3581312).sum := by decide
  have hdescent : baseEnd_3581312 < baseStart_3581312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581361 : List Nat := [1, 2, 2, 4, 1, 1, 1, 4, 3, 3]
def baseStart_3581361 : Nat := 118140960795 + 3581361 * 2 ^ 59
def prefixEnd_3581361 : Nat := 4983230072969 + 3 ^ 40 * 3581361 * 2
def baseEnd_3581361 : Nat := 1225973060177911761544751

theorem tailTrace_3581361 : CollatzResearch.WordTrace tailWord_3581361 prefixEnd_3581361 1225973060177911761544751 := by
  unfold tailWord_3581361
  simp only [CollatzResearch.WordTrace]
  refine ⟨130622966778348219608143937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87081977852232146405429291 130622966778348219608143937)
  ·
    refine ⟨97967225083761164706107953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130622966778348219608143937 97967225083761164706107953)
    ·
      refine ⟨73475418812820873529580965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97967225083761164706107953 73475418812820873529580965)
      ·
        refine ⟨13776641027403913786796431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73475418812820873529580965 13776641027403913786796431)
        ·
          refine ⟨20664961541105870680194647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13776641027403913786796431 20664961541105870680194647)
          ·
            refine ⟨30997442311658806020291971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20664961541105870680194647 30997442311658806020291971)
            ·
              refine ⟨46496163467488209030437957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30997442311658806020291971 46496163467488209030437957)
              ·
                refine ⟨8718030650154039193207117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46496163467488209030437957 8718030650154039193207117)
                ·
                  refine ⟨3269261493807764697452669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8718030650154039193207117 3269261493807764697452669)
                  ·
                    refine ⟨1225973060177911761544751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3269261493807764697452669 1225973060177911761544751)
                    ·
                      rfl

theorem cell22_3581361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 4, 3, 3].length) (baseStart_3581361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581361 prefixEnd_3581361 := by exact prefixLift 3581361
  have htrace : WordTrace (prefixWord ++ tailWord_3581361) baseStart_3581361 baseEnd_3581361 := by
    simpa [prefixWord, tailWord_3581361, baseEnd_3581361] using wordTrace_append hprefix tailTrace_3581361
  have hstable : (prefixWord ++ tailWord_3581361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581361).length < 2 ^ (prefixWord ++ tailWord_3581361).sum := by decide
  have hdescent : baseEnd_3581361 < baseStart_3581361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581446 : List Nat := [6, 2, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_3581446 : Nat := 118140960795 + 3581446 * 2 ^ 59
def prefixEnd_3581446 : Nat := 4983230072969 + 3 ^ 40 * 3581446 * 2
def baseEnd_3581446 : Nat := 1226002157414999873169491

theorem tailTrace_3581446 : CollatzResearch.WordTrace tailWord_3581446 prefixEnd_3581446 1226002157414999873169491 := by
  unfold tailWord_3581446
  simp only [CollatzResearch.WordTrace]
  refine ⟨4082064593220008722655881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87084044655360186083325461 4082064593220008722655881)
  ·
    refine ⟨3061548444915006541991911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4082064593220008722655881 3061548444915006541991911)
    ·
      refine ⟨4592322667372509812987867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3061548444915006541991911 4592322667372509812987867)
      ·
        refine ⟨6888484001058764719481801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4592322667372509812987867 6888484001058764719481801)
        ·
          refine ⟨5166363000794073539611351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6888484001058764719481801 5166363000794073539611351)
          ·
            refine ⟨7749544501191110309417027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5166363000794073539611351 7749544501191110309417027)
            ·
              refine ⟨11624316751786665464125541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7749544501191110309417027 11624316751786665464125541)
              ·
                refine ⟨2179559390959999774523539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11624316751786665464125541 2179559390959999774523539)
                ·
                  refine ⟨3269339086439999661785309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179559390959999774523539 3269339086439999661785309)
                  ·
                    refine ⟨1226002157414999873169491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3269339086439999661785309 1226002157414999873169491)
                    ·
                      rfl

theorem cell22_3581446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_3581446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581446 prefixEnd_3581446 := by exact prefixLift 3581446
  have htrace : WordTrace (prefixWord ++ tailWord_3581446) baseStart_3581446 baseEnd_3581446 := by
    simpa [prefixWord, tailWord_3581446, baseEnd_3581446] using wordTrace_append hprefix tailTrace_3581446
  have hstable : (prefixWord ++ tailWord_3581446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581446).length < 2 ^ (prefixWord ++ tailWord_3581446).sum := by decide
  have hdescent : baseEnd_3581446 < baseStart_3581446 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581468 : List Nat := [2, 2, 3, 1, 2, 1, 1, 5, 2, 3]
def baseStart_3581468 : Nat := 118140960795 + 3581468 * 2 ^ 59
def prefixEnd_3581468 : Nat := 4983230072969 + 3 ^ 40 * 3581468 * 2
def baseEnd_3581468 : Nat := 1226009688464599149119423

theorem tailTrace_3581468 : CollatzResearch.WordTrace tailWord_3581468 prefixEnd_3581468 1226009688464599149119423 := by
  unfold tailWord_3581468
  simp only [CollatzResearch.WordTrace]
  refine ⟨65313434694480288441144529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87084579592640384588192705 65313434694480288441144529)
  ·
    refine ⟨48985076020860216330858397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65313434694480288441144529 48985076020860216330858397)
    ·
      refine ⟨18369403507822581124071899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48985076020860216330858397 18369403507822581124071899)
      ·
        refine ⟨27554105261733871686107849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18369403507822581124071899 27554105261733871686107849)
        ·
          refine ⟨20665578946300403764580887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27554105261733871686107849 20665578946300403764580887)
          ·
            refine ⟨30998368419450605646871331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20665578946300403764580887 30998368419450605646871331)
            ·
              refine ⟨46497552629175908470306997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 30998368419450605646871331 46497552629175908470306997)
              ·
                refine ⟨4359145558985241419091281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46497552629175908470306997 4359145558985241419091281)
                ·
                  refine ⟨3269359169238931064318461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4359145558985241419091281 3269359169238931064318461)
                  ·
                    refine ⟨1226009688464599149119423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3269359169238931064318461 1226009688464599149119423)
                    ·
                      rfl

theorem cell22_3581468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_3581468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581468 prefixEnd_3581468 := by exact prefixLift 3581468
  have htrace : WordTrace (prefixWord ++ tailWord_3581468) baseStart_3581468 baseEnd_3581468 := by
    simpa [prefixWord, tailWord_3581468, baseEnd_3581468] using wordTrace_append hprefix tailTrace_3581468
  have hstable : (prefixWord ++ tailWord_3581468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581468).length < 2 ^ (prefixWord ++ tailWord_3581468).sum := by decide
  have hdescent : baseEnd_3581468 < baseStart_3581468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581618 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_3581618 : Nat := 118140960795 + 3581618 * 2 ^ 59
def prefixEnd_3581618 : Nat := 4983230072969 + 3 ^ 40 * 3581618 * 2
def baseEnd_3581618 : Nat := 1226061036530048757868963

theorem tailTrace_3581618 : CollatzResearch.WordTrace tailWord_3581618 prefixEnd_3581618 1226061036530048757868963 := by
  unfold tailWord_3581618
  simp only [CollatzResearch.WordTrace]
  refine ⟨32658085084604288125062377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87088226892278101666833005 32658085084604288125062377)
  ·
    refine ⟨24493563813453216093796783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32658085084604288125062377 24493563813453216093796783)
    ·
      refine ⟨36740345720179824140695175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24493563813453216093796783 36740345720179824140695175)
      ·
        refine ⟨55110518580269736211042763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36740345720179824140695175 55110518580269736211042763)
        ·
          refine ⟨82665777870404604316564145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55110518580269736211042763 82665777870404604316564145)
          ·
            refine ⟨61999333402803453237423109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82665777870404604316564145 61999333402803453237423109)
            ·
              refine ⟨11624875013025647482016833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 61999333402803453237423109 11624875013025647482016833)
              ·
                refine ⟨8718656259769235611512625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11624875013025647482016833 8718656259769235611512625)
                ·
                  refine ⟨6538992194826926708634469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8718656259769235611512625 6538992194826926708634469)
                  ·
                    refine ⟨1226061036530048757868963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6538992194826926708634469 1226061036530048757868963)
                    ·
                      rfl

theorem cell22_3581618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_3581618 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581618 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581618 prefixEnd_3581618 := by exact prefixLift 3581618
  have htrace : WordTrace (prefixWord ++ tailWord_3581618) baseStart_3581618 baseEnd_3581618 := by
    simpa [prefixWord, tailWord_3581618, baseEnd_3581618] using wordTrace_append hprefix tailTrace_3581618
  have hstable : (prefixWord ++ tailWord_3581618).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581618).length < 2 ^ (prefixWord ++ tailWord_3581618).sum := by decide
  have hdescent : baseEnd_3581618 < baseStart_3581618 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581650 : List Nat := [3, 2, 2, 2, 2, 2, 3, 6]
def baseStart_3581650 : Nat := 118140960795 + 3581650 * 2 ^ 59
def prefixEnd_3581650 : Nat := 4983230072969 + 3 ^ 40 * 3581650 * 2
def baseEnd_3581650 : Nat := 136230221198223482340985

theorem tailTrace_3581650 : CollatzResearch.WordTrace tailWord_3581650 prefixEnd_3581650 136230221198223482340985 := by
  unfold tailWord_3581650
  simp only [CollatzResearch.WordTrace]
  refine ⟨32658376868575305491353601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87089004982867481310276269 32658376868575305491353601)
  ·
    refine ⟨24493782651431479118515201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32658376868575305491353601 24493782651431479118515201)
    ·
      refine ⟨18370336988573609338886401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24493782651431479118515201 18370336988573609338886401)
      ·
        refine ⟨13777752741430207004164801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18370336988573609338886401 13777752741430207004164801)
        ·
          refine ⟨10333314556072655253123601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13777752741430207004164801 10333314556072655253123601)
          ·
            refine ⟨7749985917054491439842701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10333314556072655253123601 7749985917054491439842701)
            ·
              refine ⟨2906244718895434289941013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7749985917054491439842701 2906244718895434289941013)
              ·
                refine ⟨136230221198223482340985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2906244718895434289941013 136230221198223482340985)
                ·
                  rfl

theorem cell22_3581650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 3, 6].length) (baseStart_3581650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581650 prefixEnd_3581650 := by exact prefixLift 3581650
  have htrace : WordTrace (prefixWord ++ tailWord_3581650) baseStart_3581650 baseEnd_3581650 := by
    simpa [prefixWord, tailWord_3581650, baseEnd_3581650] using wordTrace_append hprefix tailTrace_3581650
  have hstable : (prefixWord ++ tailWord_3581650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581650).length < 2 ^ (prefixWord ++ tailWord_3581650).sum := by decide
  have hdescent : baseEnd_3581650 < baseStart_3581650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581652 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_3581652 : Nat := 118140960795 + 3581652 * 2 ^ 59
def prefixEnd_3581652 : Nat := 4983230072969 + 3 ^ 40 * 3581652 * 2
def baseEnd_3581652 : Nat := 1226072675424884002518859

theorem tailTrace_3581652 : CollatzResearch.WordTrace tailWord_3581652 prefixEnd_3581652 1226072675424884002518859 := by
  unfold tailWord_3581652
  simp only [CollatzResearch.WordTrace]
  refine ⟨65316790210146988153493605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87089053613529317537991473 65316790210146988153493605)
  ·
    refine ⟨12246898164402560278780051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65316790210146988153493605 12246898164402560278780051)
    ·
      refine ⟨18370347246603840418170077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12246898164402560278780051 18370347246603840418170077)
      ·
        refine ⟨6888880217476440156813779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18370347246603840418170077 6888880217476440156813779)
        ·
          refine ⟨10333320326214660235220669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6888880217476440156813779 10333320326214660235220669)
          ·
            refine ⟨3874995122330497588207751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10333320326214660235220669 3874995122330497588207751)
            ·
              refine ⟨5812492683495746382311627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3874995122330497588207751 5812492683495746382311627)
              ·
                refine ⟨8718739025243619573467441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812492683495746382311627 8718739025243619573467441)
                ·
                  refine ⟨6539054268932714680100581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8718739025243619573467441 6539054268932714680100581)
                  ·
                    refine ⟨1226072675424884002518859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6539054268932714680100581 1226072675424884002518859)
                    ·
                      rfl

theorem cell22_3581652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_3581652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581652 prefixEnd_3581652 := by exact prefixLift 3581652
  have htrace : WordTrace (prefixWord ++ tailWord_3581652) baseStart_3581652 baseEnd_3581652 := by
    simpa [prefixWord, tailWord_3581652, baseEnd_3581652] using wordTrace_append hprefix tailTrace_3581652
  have hstable : (prefixWord ++ tailWord_3581652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581652).length < 2 ^ (prefixWord ++ tailWord_3581652).sum := by decide
  have hdescent : baseEnd_3581652 < baseStart_3581652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581671 : List Nat := [1, 1, 5, 4, 2, 1, 1, 2, 2, 3]
def baseStart_3581671 : Nat := 118140960795 + 3581671 * 2 ^ 59
def prefixEnd_3581671 : Nat := 4983230072969 + 3 ^ 40 * 3581671 * 2
def baseEnd_3581671 : Nat := 1226079179513174286293801

theorem tailTrace_3581671 : CollatzResearch.WordTrace tailWord_3581671 prefixEnd_3581671 1226079179513174286293801 := by
  unfold tailWord_3581671
  simp only [CollatzResearch.WordTrace]
  refine ⟨130634273407225142551928867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87089515604816761701285911 130634273407225142551928867)
  ·
    refine ⟨195951410110837713827893301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130634273407225142551928867 195951410110837713827893301)
    ·
      refine ⟨18370444697891035671364997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 195951410110837713827893301 18370444697891035671364997)
      ·
        refine ⟨3444458380854569188380937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 18370444697891035671364997 3444458380854569188380937)
        ·
          refine ⟨2583343785640926891285703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3444458380854569188380937 2583343785640926891285703)
          ·
            refine ⟨3875015678461390336928555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583343785640926891285703 3875015678461390336928555)
            ·
              refine ⟨5812523517692085505392833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875015678461390336928555 5812523517692085505392833)
              ·
                refine ⟨4359392638269064129044625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5812523517692085505392833 4359392638269064129044625)
                ·
                  refine ⟨3269544478701798096783469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4359392638269064129044625 3269544478701798096783469)
                  ·
                    refine ⟨1226079179513174286293801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3269544478701798096783469 1226079179513174286293801)
                    ·
                      rfl

theorem cell22_3581671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_3581671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581671 prefixEnd_3581671 := by exact prefixLift 3581671
  have htrace : WordTrace (prefixWord ++ tailWord_3581671) baseStart_3581671 baseEnd_3581671 := by
    simpa [prefixWord, tailWord_3581671, baseEnd_3581671] using wordTrace_append hprefix tailTrace_3581671
  have hstable : (prefixWord ++ tailWord_3581671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581671).length < 2 ^ (prefixWord ++ tailWord_3581671).sum := by decide
  have hdescent : baseEnd_3581671 < baseStart_3581671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581678 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 7]
def baseStart_3581678 : Nat := 118140960795 + 3581678 * 2 ^ 59
def prefixEnd_3581678 : Nat := 4983230072969 + 3 ^ 40 * 3581678 * 2
def baseEnd_3581678 : Nat := 408693858585409533789593

theorem tailTrace_3581678 : CollatzResearch.WordTrace tailWord_3581678 prefixEnd_3581678 408693858585409533789593 := by
  unfold tailWord_3581678
  simp only [CollatzResearch.WordTrace]
  refine ⟨16329316089774972843429211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87089685812133188498289125 16329316089774972843429211)
  ·
    refine ⟨24493974134662459265143817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16329316089774972843429211 24493974134662459265143817)
    ·
      refine ⟨18370480600996844448857863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24493974134662459265143817 18370480600996844448857863)
      ·
        refine ⟨27555720901495266673286795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18370480600996844448857863 27555720901495266673286795)
        ·
          refine ⟨41333581352242900009930193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27555720901495266673286795 41333581352242900009930193)
          ·
            refine ⟨31000186014182175007447645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41333581352242900009930193 31000186014182175007447645)
            ·
              refine ⟨11625069755318315627792867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31000186014182175007447645 11625069755318315627792867)
              ·
                refine ⟨17437604632977473441689301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11625069755318315627792867 17437604632977473441689301)
                ·
                  refine ⟨408693858585409533789593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17437604632977473441689301 408693858585409533789593)
                  ·
                    rfl

theorem cell22_3581678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 7].length) (baseStart_3581678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581678 prefixEnd_3581678 := by exact prefixLift 3581678
  have htrace : WordTrace (prefixWord ++ tailWord_3581678) baseStart_3581678 baseEnd_3581678 := by
    simpa [prefixWord, tailWord_3581678, baseEnd_3581678] using wordTrace_append hprefix tailTrace_3581678
  have hstable : (prefixWord ++ tailWord_3581678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581678).length < 2 ^ (prefixWord ++ tailWord_3581678).sum := by decide
  have hdescent : baseEnd_3581678 < baseStart_3581678 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581682 : List Nat := [3, 2, 1, 3, 1, 1, 1, 6, 1, 3]
def baseStart_3581682 : Nat := 118140960795 + 3581682 * 2 ^ 59
def prefixEnd_3581682 : Nat := 4983230072969 + 3 ^ 40 * 3581682 * 2
def baseEnd_3581682 : Nat := 1226082945037973924268767

theorem tailTrace_3581682 : CollatzResearch.WordTrace tailWord_3581682 prefixEnd_3581682 1226082945037973924268767 := by
  unfold tailWord_3581682
  simp only [CollatzResearch.WordTrace]
  refine ⟨32658668652546322857644825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87089783073456860953719533 32658668652546322857644825)
  ·
    refine ⟨24494001489409742143233619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32658668652546322857644825 24494001489409742143233619)
    ·
      refine ⟨36741002234114613214850429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24494001489409742143233619 36741002234114613214850429)
      ·
        refine ⟨13777875837792979955568911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36741002234114613214850429 13777875837792979955568911)
        ·
          refine ⟨20666813756689469933353367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13777875837792979955568911 20666813756689469933353367)
          ·
            refine ⟨31000220635034204900030051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20666813756689469933353367 31000220635034204900030051)
            ·
              refine ⟨46500330952551307350045077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31000220635034204900030051 46500330952551307350045077)
              ·
                refine ⟨2179703013400842532033363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46500330952551307350045077 2179703013400842532033363)
                ·
                  refine ⟨3269554520101263798050045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179703013400842532033363 3269554520101263798050045)
                  ·
                    refine ⟨1226082945037973924268767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3269554520101263798050045 1226082945037973924268767)
                    ·
                      rfl

theorem cell22_3581682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 6, 1, 3].length) (baseStart_3581682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581682 prefixEnd_3581682 := by exact prefixLift 3581682
  have htrace : WordTrace (prefixWord ++ tailWord_3581682) baseStart_3581682 baseEnd_3581682 := by
    simpa [prefixWord, tailWord_3581682, baseEnd_3581682] using wordTrace_append hprefix tailTrace_3581682
  have hstable : (prefixWord ++ tailWord_3581682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581682).length < 2 ^ (prefixWord ++ tailWord_3581682).sum := by decide
  have hdescent : baseEnd_3581682 < baseStart_3581682 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581691 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 2, 8]
def baseStart_3581691 : Nat := 118140960795 + 3581691 * 2 ^ 59
def prefixEnd_3581691 : Nat := 4983230072969 + 3 ^ 40 * 3581691 * 2
def baseEnd_3581691 : Nat := 1226086025921900900793739

theorem tailTrace_3581691 : CollatzResearch.WordTrace tailWord_3581691 prefixEnd_3581691 1226086025921900900793739 := by
  unfold tailWord_3581691
  simp only [CollatzResearch.WordTrace]
  refine ⟨130635002867152685967656927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87090001911435123978437951 130635002867152685967656927)
  ·
    refine ⟨195952504300729028951485391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130635002867152685967656927 195952504300729028951485391)
    ·
      refine ⟨293928756451093543427228087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195952504300729028951485391 293928756451093543427228087)
      ·
        refine ⟨440893134676640315140842131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 293928756451093543427228087 440893134676640315140842131)
        ·
          refine ⟨661339702014960472711263197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 440893134676640315140842131 661339702014960472711263197)
          ·
            refine ⟨248002388255610177266723699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 661339702014960472711263197 248002388255610177266723699)
            ·
              refine ⟨372003582383415265900085549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248002388255610177266723699 372003582383415265900085549)
              ·
                refine ⟨139501343393780724712532081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 372003582383415265900085549 139501343393780724712532081)
                ·
                  refine ⟨104626007545335543534399061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139501343393780724712532081 104626007545335543534399061)
                  ·
                    refine ⟨1226086025921900900793739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104626007545335543534399061 1226086025921900900793739)
                    ·
                      rfl

theorem cell22_3581691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 8].length) (baseStart_3581691 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581691 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581691 prefixEnd_3581691 := by exact prefixLift 3581691
  have htrace : WordTrace (prefixWord ++ tailWord_3581691) baseStart_3581691 baseEnd_3581691 := by
    simpa [prefixWord, tailWord_3581691, baseEnd_3581691] using wordTrace_append hprefix tailTrace_3581691
  have hstable : (prefixWord ++ tailWord_3581691).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581691).length < 2 ^ (prefixWord ++ tailWord_3581691).sum := by decide
  have hdescent : baseEnd_3581691 < baseStart_3581691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581708 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_3581708 : Nat := 118140960795 + 3581708 * 2 ^ 59
def prefixEnd_3581708 : Nat := 4983230072969 + 3 ^ 40 * 3581708 * 2
def baseEnd_3581708 : Nat := 1226091845369318523118687

theorem tailTrace_3581708 : CollatzResearch.WordTrace tailWord_3581708 prefixEnd_3581708 1226091845369318523118687 := by
  unfold tailWord_3581708
  simp only [CollatzResearch.WordTrace]
  refine ⟨65317811454045548935512889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87090415272060731914017185 65317811454045548935512889)
  ·
    refine ⟨48988358590534161701634667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65317811454045548935512889 48988358590534161701634667)
    ·
      refine ⟨73482537885801242552452001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48988358590534161701634667 73482537885801242552452001)
      ·
        refine ⟨55111903414350931914339001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73482537885801242552452001 55111903414350931914339001)
        ·
          refine ⟨41333927560763198935754251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55111903414350931914339001 41333927560763198935754251)
          ·
            refine ⟨62000891341144798403631377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41333927560763198935754251 62000891341144798403631377)
            ·
              refine ⟨46500668505858598802723533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62000891341144798403631377 46500668505858598802723533)
              ·
                refine ⟨17437750689696974551021325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46500668505858598802723533 17437750689696974551021325)
                ·
                  refine ⟨6539156508636365456632997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17437750689696974551021325 6539156508636365456632997)
                  ·
                    refine ⟨1226091845369318523118687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6539156508636365456632997 1226091845369318523118687)
                    ·
                      rfl

theorem cell22_3581708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_3581708 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581708 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581708 prefixEnd_3581708 := by exact prefixLift 3581708
  have htrace : WordTrace (prefixWord ++ tailWord_3581708) baseStart_3581708 baseEnd_3581708 := by
    simpa [prefixWord, tailWord_3581708, baseEnd_3581708] using wordTrace_append hprefix tailTrace_3581708
  have hstable : (prefixWord ++ tailWord_3581708).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581708).length < 2 ^ (prefixWord ++ tailWord_3581708).sum := by decide
  have hdescent : baseEnd_3581708 < baseStart_3581708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581740 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 6]
def baseStart_3581740 : Nat := 118140960795 + 3581740 * 2 ^ 59
def prefixEnd_3581740 : Nat := 4983230072969 + 3 ^ 40 * 3581740 * 2
def baseEnd_3581740 : Nat := 408700933207760368772863

theorem tailTrace_3581740 : CollatzResearch.WordTrace tailWord_3581740 prefixEnd_3581740 408700933207760368772863 := by
  unfold tailWord_3581740
  simp only [CollatzResearch.WordTrace]
  refine ⟨65318395021987583668095337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87091193362650111557460449 65318395021987583668095337)
  ·
    refine ⟨48988796266490687751071503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65318395021987583668095337 48988796266490687751071503)
    ·
      refine ⟨73483194399736031626607255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48988796266490687751071503 73483194399736031626607255)
      ·
        refine ⟨110224791599604047439910883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73483194399736031626607255 110224791599604047439910883)
        ·
          refine ⟨165337187399406071159866325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110224791599604047439910883 165337187399406071159866325)
          ·
            refine ⟨3875090329673579792809367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 165337187399406071159866325 3875090329673579792809367)
            ·
              refine ⟨5812635494510369689214051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875090329673579792809367 5812635494510369689214051)
              ·
                refine ⟨8718953241765554533821077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812635494510369689214051 8718953241765554533821077)
                ·
                  refine ⟨408700933207760368772863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8718953241765554533821077 408700933207760368772863)
                  ·
                    rfl

theorem cell22_3581740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 6].length) (baseStart_3581740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581740 prefixEnd_3581740 := by exact prefixLift 3581740
  have htrace : WordTrace (prefixWord ++ tailWord_3581740) baseStart_3581740 baseEnd_3581740 := by
    simpa [prefixWord, tailWord_3581740, baseEnd_3581740] using wordTrace_append hprefix tailTrace_3581740
  have hstable : (prefixWord ++ tailWord_3581740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581740).length < 2 ^ (prefixWord ++ tailWord_3581740).sum := by decide
  have hdescent : baseEnd_3581740 < baseStart_3581740 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581759 : List Nat := [1, 1, 2, 2, 7, 1, 1, 2, 1, 4]
def baseStart_3581759 : Nat := 118140960795 + 3581759 * 2 ^ 59
def prefixEnd_3581759 : Nat := 4983230072969 + 3 ^ 40 * 3581759 * 2
def baseEnd_3581759 : Nat := 1226109303711571390093531

theorem tailTrace_3581759 : CollatzResearch.WordTrace tailWord_3581759 prefixEnd_3581759 1226109303711571390093531 := by
  unfold tailWord_3581759
  simp only [CollatzResearch.WordTrace]
  refine ⟨130637483030906333581132331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87091655353937555720754887 130637483030906333581132331)
  ·
    refine ⟨195956224546359500371698497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130637483030906333581132331 195956224546359500371698497)
    ·
      refine ⟨146967168409769625278773873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195956224546359500371698497 146967168409769625278773873)
      ·
        refine ⟨110225376307327218959080405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146967168409769625278773873 110225376307327218959080405)
        ·
          refine ⟨2583407257202981694353447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 110225376307327218959080405 2583407257202981694353447)
          ·
            refine ⟨3875110885804472541530171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583407257202981694353447 3875110885804472541530171)
            ·
              refine ⟨5812666328706708812295257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875110885804472541530171 5812666328706708812295257)
              ·
                refine ⟨4359499746530031609221443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5812666328706708812295257 4359499746530031609221443)
                ·
                  refine ⟨6539249619795047413832165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4359499746530031609221443 6539249619795047413832165)
                  ·
                    refine ⟨1226109303711571390093531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6539249619795047413832165 1226109303711571390093531)
                    ·
                      rfl

theorem cell22_3581759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 7, 1, 1, 2, 1, 4].length) (baseStart_3581759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581759 prefixEnd_3581759 := by exact prefixLift 3581759
  have htrace : WordTrace (prefixWord ++ tailWord_3581759) baseStart_3581759 baseEnd_3581759 := by
    simpa [prefixWord, tailWord_3581759, baseEnd_3581759] using wordTrace_append hprefix tailTrace_3581759
  have hstable : (prefixWord ++ tailWord_3581759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581759).length < 2 ^ (prefixWord ++ tailWord_3581759).sum := by decide
  have hdescent : baseEnd_3581759 < baseStart_3581759 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581768 : List Nat := [2, 1, 3, 1, 1, 4, 2, 8]
def baseStart_3581768 : Nat := 118140960795 + 3581768 * 2 ^ 59
def prefixEnd_3581768 : Nat := 4983230072969 + 3 ^ 40 * 3581768 * 2
def baseEnd_3581768 : Nat := 136234709399499818513167

theorem tailTrace_3581768 : CollatzResearch.WordTrace tailWord_3581768 prefixEnd_3581768 136234709399499818513167 := by
  unfold tailWord_3581768
  simp only [CollatzResearch.WordTrace]
  refine ⟨65318905643936864059104979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87091874191915818745473305 65318905643936864059104979)
  ·
    refine ⟨97978358465905296088657469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65318905643936864059104979 97978358465905296088657469)
    ·
      refine ⟨36741884424714486033246551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 97978358465905296088657469 36741884424714486033246551)
      ·
        refine ⟨55112826637071729049869827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36741884424714486033246551 55112826637071729049869827)
        ·
          refine ⟨82669239955607593574804741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55112826637071729049869827 82669239955607593574804741)
          ·
            refine ⟨15500482491676423795275889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82669239955607593574804741 15500482491676423795275889)
            ·
              refine ⟨11625361868757317846456917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15500482491676423795275889 11625361868757317846456917)
              ·
                refine ⟨136234709399499818513167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11625361868757317846456917 136234709399499818513167)
                ·
                  rfl

theorem cell22_3581768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 8].length) (baseStart_3581768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581768 prefixEnd_3581768 := by exact prefixLift 3581768
  have htrace : WordTrace (prefixWord ++ tailWord_3581768) baseStart_3581768 baseEnd_3581768 := by
    simpa [prefixWord, tailWord_3581768, baseEnd_3581768] using wordTrace_append hprefix tailTrace_3581768
  have hstable : (prefixWord ++ tailWord_3581768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581768).length < 2 ^ (prefixWord ++ tailWord_3581768).sum := by decide
  have hdescent : baseEnd_3581768 < baseStart_3581768 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581770 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 2, 4]
def baseStart_3581770 : Nat := 118140960795 + 3581770 * 2 ^ 59
def prefixEnd_3581770 : Nat := 4983230072969 + 3 ^ 40 * 3581770 * 2
def baseEnd_3581770 : Nat := 1226113069236371028068497

theorem tailTrace_3581770 : CollatzResearch.WordTrace tailWord_3581770 prefixEnd_3581770 1226113069236371028068497 := by
  unfold tailWord_3581770
  simp only [CollatzResearch.WordTrace]
  refine ⟨32659471058466620614945691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87091922822577654973188509 32659471058466620614945691)
  ·
    refine ⟨48989206587699930922418537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32659471058466620614945691 48989206587699930922418537)
    ·
      refine ⟨36741904940774948191813903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48989206587699930922418537 36741904940774948191813903)
      ·
        refine ⟨55112857411162422287720855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36741904940774948191813903 55112857411162422287720855)
        ·
          refine ⟨82669286116743633431581283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55112857411162422287720855 82669286116743633431581283)
          ·
            refine ⟨124003929175115450147371925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82669286116743633431581283 124003929175115450147371925)
            ·
              refine ⟨5812684180083536725658059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124003929175115450147371925 5812684180083536725658059)
              ·
                refine ⟨8719026270125305088487089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5812684180083536725658059 8719026270125305088487089)
                ·
                  refine ⟨6539269702593978816365317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8719026270125305088487089 6539269702593978816365317)
                  ·
                    refine ⟨1226113069236371028068497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6539269702593978816365317 1226113069236371028068497)
                    ·
                      rfl

theorem cell22_3581770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 2, 4].length) (baseStart_3581770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581770 prefixEnd_3581770 := by exact prefixLift 3581770
  have htrace : WordTrace (prefixWord ++ tailWord_3581770) baseStart_3581770 baseEnd_3581770 := by
    simpa [prefixWord, tailWord_3581770, baseEnd_3581770] using wordTrace_append hprefix tailTrace_3581770
  have hstable : (prefixWord ++ tailWord_3581770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581770).length < 2 ^ (prefixWord ++ tailWord_3581770).sum := by decide
  have hdescent : baseEnd_3581770 < baseStart_3581770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581847 : List Nat := [1, 1, 3, 3, 1, 5, 1, 2, 5]
def baseStart_3581847 : Nat := 118140960795 + 3581847 * 2 ^ 59
def prefixEnd_3581847 : Nat := 4983230072969 + 3 ^ 40 * 3581847 * 2
def baseEnd_3581847 : Nat := 408713142636656164631087

theorem tailTrace_3581847 : CollatzResearch.WordTrace tailWord_3581847 prefixEnd_3581847 408713142636656164631087 := by
  unfold tailWord_3581847
  simp only [CollatzResearch.WordTrace]
  refine ⟨130640692654587524610335795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87093795103058349740223863 130640692654587524610335795)
  ·
    refine ⟨195961038981881286915503693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130640692654587524610335795 195961038981881286915503693)
    ·
      refine ⟨73485389618205482593313885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 195961038981881286915503693 73485389618205482593313885)
      ·
        refine ⟨27557021106827055972492707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73485389618205482593313885 27557021106827055972492707)
        ·
          refine ⟨41335531660240583958739061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27557021106827055972492707 41335531660240583958739061)
          ·
            refine ⟨3875206093147554746131787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 41335531660240583958739061 3875206093147554746131787)
            ·
              refine ⟨5812809139721332119197681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875206093147554746131787 5812809139721332119197681)
              ·
                refine ⟨4359606854790999089398261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5812809139721332119197681 4359606854790999089398261)
                ·
                  refine ⟨408713142636656164631087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4359606854790999089398261 408713142636656164631087)
                  ·
                    rfl

theorem cell22_3581847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 5].length) (baseStart_3581847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581847 prefixEnd_3581847 := by exact prefixLift 3581847
  have htrace : WordTrace (prefixWord ++ tailWord_3581847) baseStart_3581847 baseEnd_3581847 := by
    simpa [prefixWord, tailWord_3581847, baseEnd_3581847] using wordTrace_append hprefix tailTrace_3581847
  have hstable : (prefixWord ++ tailWord_3581847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581847).length < 2 ^ (prefixWord ++ tailWord_3581847).sum := by decide
  have hdescent : baseEnd_3581847 < baseStart_3581847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3581877 : List Nat := [1, 3, 3, 2, 1, 2, 1, 4, 1, 4]
def baseStart_3581877 : Nat := 118140960795 + 3581877 * 2 ^ 59
def prefixEnd_3581877 : Nat := 4983230072969 + 3 ^ 40 * 3581877 * 2
def baseEnd_3581877 : Nat := 1226149697523058415643169

theorem tailTrace_3581877 : CollatzResearch.WordTrace tailWord_3581877 prefixEnd_3581877 1226149697523058415643169 := by
  unfold tailWord_3581877
  simp only [CollatzResearch.WordTrace]
  refine ⟨130641786844478839733927885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87094524562985893155951923 130641786844478839733927885)
  ·
    refine ⟨48990670066679564900222957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130641786844478839733927885 48990670066679564900222957)
    ·
      refine ⟨18371501275004836837583609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 48990670066679564900222957 18371501275004836837583609)
      ·
        refine ⟨13778625956253627628187707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18371501275004836837583609 13778625956253627628187707)
        ·
          refine ⟨20667938934380441442281561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13778625956253627628187707 20667938934380441442281561)
          ·
            refine ⟨15500954200785331081711171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20667938934380441442281561 15500954200785331081711171)
            ·
              refine ⟨23251431301177996622566757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15500954200785331081711171 23251431301177996622566757)
              ·
                refine ⟨4359643368970874366731267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23251431301177996622566757 4359643368970874366731267)
                ·
                  refine ⟨6539465053456311550096901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4359643368970874366731267 6539465053456311550096901)
                  ·
                    refine ⟨1226149697523058415643169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6539465053456311550096901 1226149697523058415643169)
                    ·
                      rfl

theorem cell22_3581877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_3581877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3581877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3581877 prefixEnd_3581877 := by exact prefixLift 3581877
  have htrace : WordTrace (prefixWord ++ tailWord_3581877) baseStart_3581877 baseEnd_3581877 := by
    simpa [prefixWord, tailWord_3581877, baseEnd_3581877] using wordTrace_append hprefix tailTrace_3581877
  have hstable : (prefixWord ++ tailWord_3581877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3581877).length < 2 ^ (prefixWord ++ tailWord_3581877).sum := by decide
  have hdescent : baseEnd_3581877 < baseStart_3581877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3581877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582010 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 10]
def baseStart_3582010 : Nat := 118140960795 + 3582010 * 2 ^ 59
def prefixEnd_3582010 : Nat := 4983230072969 + 3 ^ 40 * 3582010 * 2
def baseEnd_3582010 : Nat := 408731742047030134022587

theorem tailTrace_3582010 : CollatzResearch.WordTrace tailWord_3582010 prefixEnd_3582010 408731742047030134022587 := by
  unfold tailWord_3582010
  simp only [CollatzResearch.WordTrace]
  refine ⟨32661659438249250862129871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87097758501998002299012989 32661659438249250862129871)
  ·
    refine ⟨48992489157373876293194807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32661659438249250862129871 48992489157373876293194807)
    ·
      refine ⟨73488733736060814439792211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48992489157373876293194807 73488733736060814439792211)
      ·
        refine ⟨110233100604091221659688317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73488733736060814439792211 110233100604091221659688317)
        ·
          refine ⟨41337412726534208122383119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110233100604091221659688317 41337412726534208122383119)
          ·
            refine ⟨62006119089801312183574679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41337412726534208122383119 62006119089801312183574679)
            ·
              refine ⟨93009178634701968275362019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62006119089801312183574679 93009178634701968275362019)
              ·
                refine ⟨139513767952052952413043029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93009178634701968275362019 139513767952052952413043029)
                ·
                  refine ⟨408731742047030134022587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 139513767952052952413043029 408731742047030134022587)
                  ·
                    rfl

theorem cell22_3582010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 10].length) (baseStart_3582010 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582010 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582010 prefixEnd_3582010 := by exact prefixLift 3582010
  have htrace : WordTrace (prefixWord ++ tailWord_3582010) baseStart_3582010 baseEnd_3582010 := by
    simpa [prefixWord, tailWord_3582010, baseEnd_3582010] using wordTrace_append hprefix tailTrace_3582010
  have hstable : (prefixWord ++ tailWord_3582010).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582010).length < 2 ^ (prefixWord ++ tailWord_3582010).sum := by decide
  have hdescent : baseEnd_3582010 < baseStart_3582010 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582057 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 2, 4]
def baseStart_3582057 : Nat := 118140960795 + 3582057 * 2 ^ 59
def prefixEnd_3582057 : Nat := 4983230072969 + 3 ^ 40 * 3582057 * 2
def baseEnd_3582057 : Nat := 1226211315201597946142617

theorem tailTrace_3582057 : CollatzResearch.WordTrace tailWord_3582057 prefixEnd_3582057 1226211315201597946142617 := by
  unfold tailWord_3582057
  simp only [CollatzResearch.WordTrace]
  refine ⟨130648351983826730475480425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87098901322551153650320283 130648351983826730475480425)
  ·
    refine ⟨97986263987870047856610319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130648351983826730475480425 97986263987870047856610319)
    ·
      refine ⟨146979395981805071784915479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97986263987870047856610319 146979395981805071784915479)
      ·
        refine ⟨220469093972707607677373219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146979395981805071784915479 220469093972707607677373219)
        ·
          refine ⟨330703640959061411516059829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220469093972707607677373219 330703640959061411516059829)
          ·
            refine ⟨31003466339912007329630609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 330703640959061411516059829 31003466339912007329630609)
            ·
              refine ⟨23252599754934005497222957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31003466339912007329630609 23252599754934005497222957)
              ·
                refine ⟨8719724908100252061458609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23252599754934005497222957 8719724908100252061458609)
                ·
                  refine ⟨6539793681075189046093957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8719724908100252061458609 6539793681075189046093957)
                  ·
                    refine ⟨1226211315201597946142617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6539793681075189046093957 1226211315201597946142617)
                    ·
                      rfl

theorem cell22_3582057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_3582057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582057 prefixEnd_3582057 := by exact prefixLift 3582057
  have htrace : WordTrace (prefixWord ++ tailWord_3582057) baseStart_3582057 baseEnd_3582057 := by
    simpa [prefixWord, tailWord_3582057, baseEnd_3582057] using wordTrace_append hprefix tailTrace_3582057
  have hstable : (prefixWord ++ tailWord_3582057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582057).length < 2 ^ (prefixWord ++ tailWord_3582057).sum := by decide
  have hdescent : baseEnd_3582057 < baseStart_3582057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582138 : List Nat := [3, 1, 1, 1, 2, 2, 6, 2, 1, 3]
def baseStart_3582138 : Nat := 118140960795 + 3582138 * 2 ^ 59
def prefixEnd_3582138 : Nat := 4983230072969 + 3 ^ 40 * 3582138 * 2
def baseEnd_3582138 : Nat := 1226239043156940734867369

theorem tailTrace_3582138 : CollatzResearch.WordTrace tailWord_3582138 prefixEnd_3582138 1226239043156940734867369 := by
  unfold tailWord_3582138
  simp only [CollatzResearch.WordTrace]
  refine ⟨32662826574133320327294767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87100870864355520872786045 32662826574133320327294767)
  ·
    refine ⟨48994239861199980490942151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32662826574133320327294767 48994239861199980490942151)
    ·
      refine ⟨73491359791799970736413227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48994239861199980490942151 73491359791799970736413227)
      ·
        refine ⟨110237039687699956104619841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73491359791799970736413227 110237039687699956104619841)
        ·
          refine ⟨82677779765774967078464881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110237039687699956104619841 82677779765774967078464881)
          ·
            refine ⟨62008334824331225308848661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82677779765774967078464881 62008334824331225308848661)
            ·
              refine ⟨2906640694890526186352281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 62008334824331225308848661 2906640694890526186352281)
              ·
                refine ⟨2179980521167894639764211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2906640694890526186352281 2179980521167894639764211)
                ·
                  refine ⟨3269970781751841959646317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2179980521167894639764211 3269970781751841959646317)
                  ·
                    refine ⟨1226239043156940734867369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3269970781751841959646317 1226239043156940734867369)
                    ·
                      rfl

theorem cell22_3582138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 6, 2, 1, 3].length) (baseStart_3582138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582138 prefixEnd_3582138 := by exact prefixLift 3582138
  have htrace : WordTrace (prefixWord ++ tailWord_3582138) baseStart_3582138 baseEnd_3582138 := by
    simpa [prefixWord, tailWord_3582138, baseEnd_3582138] using wordTrace_append hprefix tailTrace_3582138
  have hstable : (prefixWord ++ tailWord_3582138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582138).length < 2 ^ (prefixWord ++ tailWord_3582138).sum := by decide
  have hdescent : baseEnd_3582138 < baseStart_3582138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582172 : List Nat := [2, 2, 5, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3582172 : Nat := 118140960795 + 3582172 * 2 ^ 59
def prefixEnd_3582172 : Nat := 4983230072969 + 3 ^ 40 * 3582172 * 2
def baseEnd_3582172 : Nat := 1226250682051775979517265

theorem tailTrace_3582172 : CollatzResearch.WordTrace tailWord_3582172 prefixEnd_3582172 1226250682051775979517265 := by
  unfold tailWord_3582172
  simp only [CollatzResearch.WordTrace]
  refine ⟨65326273189205052557958385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87101697585606736743944513 65326273189205052557958385)
  ·
    refine ⟨48994704891903789418468789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65326273189205052557958385 48994704891903789418468789)
    ·
      refine ⟨4593253583615980257981449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 48994704891903789418468789 4593253583615980257981449)
      ·
        refine ⟨3444940187711985193486087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4593253583615980257981449 3444940187711985193486087)
        ·
          refine ⟨5167410281567977790229131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3444940187711985193486087 5167410281567977790229131)
          ·
            refine ⟨7751115422351966685343697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167410281567977790229131 7751115422351966685343697)
            ·
              refine ⟨5813336566763975014007773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7751115422351966685343697 5813336566763975014007773)
              ·
                refine ⟨2180001212536490630252915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5813336566763975014007773 2180001212536490630252915)
                ·
                  refine ⟨3270001818804735945379373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180001212536490630252915 3270001818804735945379373)
                  ·
                    refine ⟨1226250682051775979517265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3270001818804735945379373 1226250682051775979517265)
                    ·
                      rfl

theorem cell22_3582172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3582172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582172 prefixEnd_3582172 := by exact prefixLift 3582172
  have htrace : WordTrace (prefixWord ++ tailWord_3582172) baseStart_3582172 baseEnd_3582172 := by
    simpa [prefixWord, tailWord_3582172, baseEnd_3582172] using wordTrace_append hprefix tailTrace_3582172
  have hstable : (prefixWord ++ tailWord_3582172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582172).length < 2 ^ (prefixWord ++ tailWord_3582172).sum := by decide
  have hdescent : baseEnd_3582172 < baseStart_3582172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582181 : List Nat := [1, 3, 1, 4, 2, 2, 1, 3, 1, 4]
def baseStart_3582181 : Nat := 118140960795 + 3582181 * 2 ^ 59
def prefixEnd_3582181 : Nat := 4983230072969 + 3 ^ 40 * 3582181 * 2
def baseEnd_3582181 : Nat := 1226253762935702956042237

theorem tailTrace_3582181 : CollatzResearch.WordTrace tailWord_3582181 prefixEnd_3582181 1226253762935702956042237 := by
  unfold tailWord_3582181
  simp only [CollatzResearch.WordTrace]
  refine ⟨130652874635377499652994397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87101916423584999768662931 130652874635377499652994397)
  ·
    refine ⟨48994827988266562369872899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130652874635377499652994397 48994827988266562369872899)
    ·
      refine ⟨73492241982399843554809349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48994827988266562369872899 73492241982399843554809349)
      ·
        refine ⟨13779795371699970666526753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73492241982399843554809349 13779795371699970666526753)
        ·
          refine ⟨10334846528774977999895065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13779795371699970666526753 10334846528774977999895065)
          ·
            refine ⟨7751134896581233499921299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10334846528774977999895065 7751134896581233499921299)
            ·
              refine ⟨11626702344871850249881949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751134896581233499921299 11626702344871850249881949)
              ·
                refine ⟨4360013379326943843705731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11626702344871850249881949 4360013379326943843705731)
                ·
                  refine ⟨6540020068990415765558597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360013379326943843705731 6540020068990415765558597)
                  ·
                    refine ⟨1226253762935702956042237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6540020068990415765558597 1226253762935702956042237)
                    ·
                      rfl

theorem cell22_3582181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 4].length) (baseStart_3582181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582181 prefixEnd_3582181 := by exact prefixLift 3582181
  have htrace : WordTrace (prefixWord ++ tailWord_3582181) baseStart_3582181 baseEnd_3582181 := by
    simpa [prefixWord, tailWord_3582181, baseEnd_3582181] using wordTrace_append hprefix tailTrace_3582181
  have hstable : (prefixWord ++ tailWord_3582181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582181).length < 2 ^ (prefixWord ++ tailWord_3582181).sum := by decide
  have hdescent : baseEnd_3582181 < baseStart_3582181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582207 : List Nat := [1, 1, 2, 2, 1, 4, 2, 9]
def baseStart_3582207 : Nat := 118140960795 + 3582207 * 2 ^ 59
def prefixEnd_3582207 : Nat := 4983230072969 + 3 ^ 40 * 3582207 * 2
def baseEnd_3582207 : Nat := 136251407029671950543573

theorem tailTrace_3582207 : CollatzResearch.WordTrace tailWord_3582207 prefixEnd_3582207 136251407029671950543573 := by
  unfold tailWord_3582207
  simp only [CollatzResearch.WordTrace]
  refine ⟨130653822933283306093440875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87102548622188870728960583 130653822933283306093440875)
  ·
    refine ⟨195980734399924959140161313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130653822933283306093440875 195980734399924959140161313)
    ·
      refine ⟨146985550799943719355120985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195980734399924959140161313 146985550799943719355120985)
      ·
        refine ⟨110239163099957789516340739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 146985550799943719355120985 110239163099957789516340739)
        ·
          refine ⟨165358744649936684274511109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110239163099957789516340739 165358744649936684274511109)
          ·
            refine ⟨31004764621863128301470833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165358744649936684274511109 31004764621863128301470833)
            ·
              refine ⟨23253573466397346226103125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31004764621863128301470833 23253573466397346226103125)
              ·
                refine ⟨136251407029671950543573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 23253573466397346226103125 136251407029671950543573)
                ·
                  rfl

theorem cell22_3582207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 9].length) (baseStart_3582207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582207 prefixEnd_3582207 := by exact prefixLift 3582207
  have htrace : WordTrace (prefixWord ++ tailWord_3582207) baseStart_3582207 baseEnd_3582207 := by
    simpa [prefixWord, tailWord_3582207, baseEnd_3582207] using wordTrace_append hprefix tailTrace_3582207
  have hstable : (prefixWord ++ tailWord_3582207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582207).length < 2 ^ (prefixWord ++ tailWord_3582207).sum := by decide
  have hdescent : baseEnd_3582207 < baseStart_3582207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582247 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 6]
def baseStart_3582247 : Nat := 118140960795 + 3582247 * 2 ^ 59
def prefixEnd_3582247 : Nat := 4983230072969 + 3 ^ 40 * 3582247 * 2
def baseEnd_3582247 : Nat := 408758785361500261297345

theorem tailTrace_3582247 : CollatzResearch.WordTrace tailWord_3582247 prefixEnd_3582247 408758785361500261297345 := by
  unfold tailWord_3582247
  simp only [CollatzResearch.WordTrace]
  refine ⟨130655281853138392924896995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87103521235425595283264663 130655281853138392924896995)
  ·
    refine ⟨195982922779707589387345493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130655281853138392924896995 195982922779707589387345493)
    ·
      refine ⟨2296674876324698313132955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 195982922779707589387345493 2296674876324698313132955)
      ·
        refine ⟨3445012314487047469699433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2296674876324698313132955 3445012314487047469699433)
        ·
          refine ⟨2583759235865285602274575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3445012314487047469699433 2583759235865285602274575)
          ·
            refine ⟨3875638853797928403411863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2583759235865285602274575 3875638853797928403411863)
            ·
              refine ⟨5813458280696892605117795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3875638853797928403411863 5813458280696892605117795)
              ·
                refine ⟨8720187421045338907676693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5813458280696892605117795 8720187421045338907676693)
                ·
                  refine ⟨408758785361500261297345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8720187421045338907676693 408758785361500261297345)
                  ·
                    rfl

theorem cell22_3582247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 6].length) (baseStart_3582247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582247 prefixEnd_3582247 := by exact prefixLift 3582247
  have htrace : WordTrace (prefixWord ++ tailWord_3582247) baseStart_3582247 baseEnd_3582247 := by
    simpa [prefixWord, tailWord_3582247, baseEnd_3582247] using wordTrace_append hprefix tailTrace_3582247
  have hstable : (prefixWord ++ tailWord_3582247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582247).length < 2 ^ (prefixWord ++ tailWord_3582247).sum := by decide
  have hdescent : baseEnd_3582247 < baseStart_3582247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582348 : List Nat := [2, 2, 1, 2, 1, 5, 2, 3, 4]
def baseStart_3582348 : Nat := 118140960795 + 3582348 * 2 ^ 59
def prefixEnd_3582348 : Nat := 4983230072969 + 3 ^ 40 * 3582348 * 2
def baseEnd_3582348 : Nat := 408770310149523395705575

theorem tailTrace_3582348 : CollatzResearch.WordTrace tailWord_3582348 prefixEnd_3582348 408770310149523395705575 := by
  unfold tailWord_3582348
  simp only [CollatzResearch.WordTrace]
  refine ⟨65329482812886243587161849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87105977083848324782882465 65329482812886243587161849)
  ·
    refine ⟨48997112109664682690371387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65329482812886243587161849 48997112109664682690371387)
    ·
      refine ⟨73495668164497024035557081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 48997112109664682690371387 73495668164497024035557081)
      ·
        refine ⟨55121751123372768026667811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73495668164497024035557081 55121751123372768026667811)
        ·
          refine ⟨82682626685059152040001717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55121751123372768026667811 82682626685059152040001717)
          ·
            refine ⟨7751496251724295503750161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82682626685059152040001717 7751496251724295503750161)
            ·
              refine ⟨5813622188793221627812621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7751496251724295503750161 5813622188793221627812621)
              ·
                refine ⟨2180108320797458110429733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5813622188793221627812621 2180108320797458110429733)
                ·
                  refine ⟨408770310149523395705575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2180108320797458110429733 408770310149523395705575)
                  ·
                    rfl

theorem cell22_3582348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_3582348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582348 prefixEnd_3582348 := by exact prefixLift 3582348
  have htrace : WordTrace (prefixWord ++ tailWord_3582348) baseStart_3582348 baseEnd_3582348 := by
    simpa [prefixWord, tailWord_3582348, baseEnd_3582348] using wordTrace_append hprefix tailTrace_3582348
  have hstable : (prefixWord ++ tailWord_3582348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582348).length < 2 ^ (prefixWord ++ tailWord_3582348).sum := by decide
  have hdescent : baseEnd_3582348 < baseStart_3582348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582350 : List Nat := [4, 1, 1, 4, 1, 1, 4, 1, 1, 4]
def baseStart_3582350 : Nat := 118140960795 + 3582350 * 2 ^ 59
def prefixEnd_3582350 : Nat := 4983230072969 + 3 ^ 40 * 3582350 * 2
def baseEnd_3582350 : Nat := 1226311615089442848566719

theorem tailTrace_3582350 : CollatzResearch.WordTrace tailWord_3582350 prefixEnd_3582350 1226311615089442848566719 := by
  unfold tailWord_3582350
  simp only [CollatzResearch.WordTrace]
  refine ⟨16332379821470655189487063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87106025714510161010597669 16332379821470655189487063)
  ·
    refine ⟨24498569732205982784230595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16332379821470655189487063 24498569732205982784230595)
    ·
      refine ⟨36747854598308974176345893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24498569732205982784230595 36747854598308974176345893)
      ·
        refine ⟨6890222737182932658064855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36747854598308974176345893 6890222737182932658064855)
        ·
          refine ⟨10335334105774398987097283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6890222737182932658064855 10335334105774398987097283)
          ·
            refine ⟨15503001158661598480645925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10335334105774398987097283 15503001158661598480645925)
            ·
              refine ⟨2906812717249049715121111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15503001158661598480645925 2906812717249049715121111)
              ·
                refine ⟨4360219075873574572681667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2906812717249049715121111 4360219075873574572681667)
                ·
                  refine ⟨6540328613810361859022501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360219075873574572681667 6540328613810361859022501)
                  ·
                    refine ⟨1226311615089442848566719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6540328613810361859022501 1226311615089442848566719)
                    ·
                      rfl

theorem cell22_3582350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 4, 1, 1, 4].length) (baseStart_3582350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582350 prefixEnd_3582350 := by exact prefixLift 3582350
  have htrace : WordTrace (prefixWord ++ tailWord_3582350) baseStart_3582350 baseEnd_3582350 := by
    simpa [prefixWord, tailWord_3582350, baseEnd_3582350] using wordTrace_append hprefix tailTrace_3582350
  have hstable : (prefixWord ++ tailWord_3582350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582350).length < 2 ^ (prefixWord ++ tailWord_3582350).sum := by decide
  have hdescent : baseEnd_3582350 < baseStart_3582350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582393 : List Nat := [1, 2, 1, 4, 3, 3, 2, 6]
def baseStart_3582393 : Nat := 118140960795 + 3582393 * 2 ^ 59
def prefixEnd_3582393 : Nat := 4983230072969 + 3 ^ 40 * 3582393 * 2
def baseEnd_3582393 : Nat := 136258481652022785526843

theorem tailTrace_3582393 : CollatzResearch.WordTrace tailWord_3582393 prefixEnd_3582393 136258481652022785526843 := by
  unfold tailWord_3582393
  simp only [CollatzResearch.WordTrace]
  refine ⟨130660606910609459859711833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87107071273739639906474555 130660606910609459859711833)
  ·
    refine ⟨97995455182957094894783875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130660606910609459859711833 97995455182957094894783875)
    ·
      refine ⟨146993182774435642342175813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 97995455182957094894783875 146993182774435642342175813)
      ·
        refine ⟨27561221770206682939157965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 146993182774435642342175813 27561221770206682939157965)
        ·
          refine ⟨10335458163827506102184237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27561221770206682939157965 10335458163827506102184237)
          ·
            refine ⟨3875796811435314788319089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10335458163827506102184237 3875796811435314788319089)
            ·
              refine ⟨2906847608576486091239317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3875796811435314788319089 2906847608576486091239317)
              ·
                refine ⟨136258481652022785526843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2906847608576486091239317 136258481652022785526843)
                ·
                  rfl

theorem cell22_3582393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 2, 6].length) (baseStart_3582393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582393 prefixEnd_3582393 := by exact prefixLift 3582393
  have htrace : WordTrace (prefixWord ++ tailWord_3582393) baseStart_3582393 baseEnd_3582393 := by
    simpa [prefixWord, tailWord_3582393, baseEnd_3582393] using wordTrace_append hprefix tailTrace_3582393
  have hstable : (prefixWord ++ tailWord_3582393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582393).length < 2 ^ (prefixWord ++ tailWord_3582393).sum := by decide
  have hdescent : baseEnd_3582393 < baseStart_3582393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582421 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 7]
def baseStart_3582421 : Nat := 118140960795 + 3582421 * 2 ^ 59
def prefixEnd_3582421 : Nat := 4983230072969 + 3 ^ 40 * 3582421 * 2
def baseEnd_3582421 : Nat := 408778639946807443347167

theorem tailTrace_3582421 : CollatzResearch.WordTrace tailWord_3582421 prefixEnd_3582421 408778639946807443347167 := by
  unfold tailWord_3582421
  simp only [CollatzResearch.WordTrace]
  refine ⟨130661628154508020641731117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87107752103005347094487411 130661628154508020641731117)
  ·
    refine ⟨48998110557940507740649169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130661628154508020641731117 48998110557940507740649169)
    ·
      refine ⟨36748582918455380805486877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 48998110557940507740649169 36748582918455380805486877)
      ·
        refine ⟨13780718594420767802057579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36748582918455380805486877 13780718594420767802057579)
        ·
          refine ⟨20671077891631151703086369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13780718594420767802057579 20671077891631151703086369)
          ·
            refine ⟨15503308418723363777314777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20671077891631151703086369 15503308418723363777314777)
            ·
              refine ⟨11627481314042522832986083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15503308418723363777314777 11627481314042522832986083)
              ·
                refine ⟨17441221971063784249479125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11627481314042522832986083 17441221971063784249479125)
                ·
                  refine ⟨408778639946807443347167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17441221971063784249479125 408778639946807443347167)
                  ·
                    rfl

theorem cell22_3582421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 7].length) (baseStart_3582421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582421 prefixEnd_3582421 := by exact prefixLift 3582421
  have htrace : WordTrace (prefixWord ++ tailWord_3582421) baseStart_3582421 baseEnd_3582421 := by
    simpa [prefixWord, tailWord_3582421, baseEnd_3582421] using wordTrace_append hprefix tailTrace_3582421
  have hstable : (prefixWord ++ tailWord_3582421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582421).length < 2 ^ (prefixWord ++ tailWord_3582421).sum := by decide
  have hdescent : baseEnd_3582421 < baseStart_3582421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582451 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 3, 4]
def baseStart_3582451 : Nat := 118140960795 + 3582451 * 2 ^ 59
def prefixEnd_3582451 : Nat := 4983230072969 + 3 ^ 40 * 3582451 * 2
def baseEnd_3582451 : Nat := 1226346189453512251791409

theorem tailTrace_3582451 : CollatzResearch.WordTrace tailWord_3582451 prefixEnd_3582451 1226346189453512251791409 := by
  unfold tailWord_3582451
  simp only [CollatzResearch.WordTrace]
  refine ⟨130662722344399335765323207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87108481562932890510215471 130662722344399335765323207)
  ·
    refine ⟨195994083516599003647984811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130662722344399335765323207 195994083516599003647984811)
    ·
      refine ⟨293991125274898505471977217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195994083516599003647984811 293991125274898505471977217)
      ·
        refine ⟨220493343956173879103982913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293991125274898505471977217 220493343956173879103982913)
        ·
          refine ⟨165370007967130409327987185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 220493343956173879103982913 165370007967130409327987185)
          ·
            refine ⟨124027505975347806995990389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165370007967130409327987185 124027505975347806995990389)
            ·
              refine ⟨11627578685188856905874099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124027505975347806995990389 11627578685188856905874099)
              ·
                refine ⟨17441368027783285358811149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11627578685188856905874099 17441368027783285358811149)
                ·
                  refine ⟨6540513010418732009554181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17441368027783285358811149 6540513010418732009554181)
                  ·
                    refine ⟨1226346189453512251791409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6540513010418732009554181 1226346189453512251791409)
                    ·
                      rfl

theorem cell22_3582451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 3, 4].length) (baseStart_3582451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582451 prefixEnd_3582451 := by exact prefixLift 3582451
  have htrace : WordTrace (prefixWord ++ tailWord_3582451) baseStart_3582451 baseEnd_3582451 := by
    simpa [prefixWord, tailWord_3582451, baseEnd_3582451] using wordTrace_append hprefix tailTrace_3582451
  have hstable : (prefixWord ++ tailWord_3582451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582451).length < 2 ^ (prefixWord ++ tailWord_3582451).sum := by decide
  have hdescent : baseEnd_3582451 < baseStart_3582451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582483 : List Nat := [1, 1, 1, 2, 1, 5, 3, 4, 4]
def baseStart_3582483 : Nat := 118140960795 + 3582483 * 2 ^ 59
def prefixEnd_3582483 : Nat := 4983230072969 + 3 ^ 40 * 3582483 * 2
def baseEnd_3582483 : Nat := 408785714569158278330437

theorem tailTrace_3582483 : CollatzResearch.WordTrace tailWord_3582483 prefixEnd_3582483 408785714569158278330437 := by
  unfold tailWord_3582483
  simp only [CollatzResearch.WordTrace]
  refine ⟨130663889480283405230488103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87109259653522270153658735 130663889480283405230488103)
  ·
    refine ⟨195995834220425107845732155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130663889480283405230488103 195995834220425107845732155)
    ·
      refine ⟨293993751330637661768598233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 195995834220425107845732155 293993751330637661768598233)
      ·
        refine ⟨220495313497978246326448675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 293993751330637661768598233 220495313497978246326448675)
        ·
          refine ⟨330742970246967369489673013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220495313497978246326448675 330742970246967369489673013)
          ·
            refine ⟨31007153460653190889656845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 330742970246967369489673013 31007153460653190889656845)
            ·
              refine ⟨11627682547744946583621317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31007153460653190889656845 11627682547744946583621317)
              ·
                refine ⟨2180190477702177484428997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11627682547744946583621317 2180190477702177484428997)
                ·
                  refine ⟨408785714569158278330437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2180190477702177484428997 408785714569158278330437)
                  ·
                    rfl

theorem cell22_3582483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 4, 4].length) (baseStart_3582483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582483 prefixEnd_3582483 := by exact prefixLift 3582483
  have htrace : WordTrace (prefixWord ++ tailWord_3582483) baseStart_3582483 baseEnd_3582483 := by
    simpa [prefixWord, tailWord_3582483, baseEnd_3582483] using wordTrace_append hprefix tailTrace_3582483
  have hstable : (prefixWord ++ tailWord_3582483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582483).length < 2 ^ (prefixWord ++ tailWord_3582483).sum := by decide
  have hdescent : baseEnd_3582483 < baseStart_3582483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582498 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 6, 3]
def baseStart_3582498 : Nat := 118140960795 + 3582498 * 2 ^ 59
def prefixEnd_3582498 : Nat := 4983230072969 + 3 ^ 40 * 3582498 * 2
def baseEnd_3582498 : Nat := 1226362278514019795866265

theorem tailTrace_3582498 : CollatzResearch.WordTrace tailWord_3582498 prefixEnd_3582498 1226362278514019795866265 := by
  unfold tailWord_3582498
  simp only [CollatzResearch.WordTrace]
  refine ⟨32666109143807265698071037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87109624383486041861522765 32666109143807265698071037)
  ·
    refine ⟨12249790928927724636776639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32666109143807265698071037 12249790928927724636776639)
    ·
      refine ⟨18374686393391586955164959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12249790928927724636776639 18374686393391586955164959)
      ·
        refine ⟨27562029590087380432747439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18374686393391586955164959 27562029590087380432747439)
        ·
          refine ⟨41343044385131070649121159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27562029590087380432747439 41343044385131070649121159)
          ·
            refine ⟨62014566577696605973681739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41343044385131070649121159 62014566577696605973681739)
            ·
              refine ⟨93021849866544908960522609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62014566577696605973681739 93021849866544908960522609)
              ·
                refine ⟨69766387399908681720391957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93021849866544908960522609 69766387399908681720391957)
                ·
                  refine ⟨3270299409370719455643373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 69766387399908681720391957 3270299409370719455643373)
                  ·
                    refine ⟨1226362278514019795866265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3270299409370719455643373 1226362278514019795866265)
                    ·
                      rfl

theorem cell22_3582498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_3582498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582498 prefixEnd_3582498 := by exact prefixLift 3582498
  have htrace : WordTrace (prefixWord ++ tailWord_3582498) baseStart_3582498 baseEnd_3582498 := by
    simpa [prefixWord, tailWord_3582498, baseEnd_3582498] using wordTrace_append hprefix tailTrace_3582498
  have hstable : (prefixWord ++ tailWord_3582498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582498).length < 2 ^ (prefixWord ++ tailWord_3582498).sum := by decide
  have hdescent : baseEnd_3582498 < baseStart_3582498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582500 : List Nat := [2, 3, 1, 5, 1, 1, 1, 2, 6]
def baseStart_3582500 : Nat := 118140960795 + 3582500 * 2 ^ 59
def prefixEnd_3582500 : Nat := 4983230072969 + 3 ^ 40 * 3582500 * 2
def baseEnd_3582500 : Nat := 408787654384964152438753

theorem tailTrace_3582500 : CollatzResearch.WordTrace tailWord_3582500 prefixEnd_3582500 408787654384964152438753 := by
  unfold tailWord_3582500
  simp only [CollatzResearch.WordTrace]
  refine ⟨65332254760610908566928477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87109673014147878089237969 65332254760610908566928477)
  ·
    refine ⟨24499595535229090712598179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65332254760610908566928477 24499595535229090712598179)
    ·
      refine ⟨36749393302843636068897269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24499595535229090712598179 36749393302843636068897269)
      ·
        refine ⟨3445255622141590881459119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 36749393302843636068897269 3445255622141590881459119)
        ·
          refine ⟨5167883433212386322188679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3445255622141590881459119 5167883433212386322188679)
          ·
            refine ⟨7751825149818579483283019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5167883433212386322188679 7751825149818579483283019)
            ·
              refine ⟨11627737724727869224924529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7751825149818579483283019 11627737724727869224924529)
              ·
                refine ⟨8720803293545901918693397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11627737724727869224924529 8720803293545901918693397)
                ·
                  refine ⟨408787654384964152438753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8720803293545901918693397 408787654384964152438753)
                  ·
                    rfl

theorem cell22_3582500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_3582500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582500 prefixEnd_3582500 := by exact prefixLift 3582500
  have htrace : WordTrace (prefixWord ++ tailWord_3582500) baseStart_3582500 baseEnd_3582500 := by
    simpa [prefixWord, tailWord_3582500, baseEnd_3582500] using wordTrace_append hprefix tailTrace_3582500
  have hstable : (prefixWord ++ tailWord_3582500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582500).length < 2 ^ (prefixWord ++ tailWord_3582500).sum := by decide
  have hdescent : baseEnd_3582500 < baseStart_3582500 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582513 : List Nat := [1, 2, 2, 3, 1, 1, 5, 1, 2, 4]
def baseStart_3582513 : Nat := 118140960795 + 3582513 * 2 ^ 59
def prefixEnd_3582513 : Nat := 4983230072969 + 3 ^ 40 * 3582513 * 2
def baseEnd_3582513 : Nat := 1226367413320564756741219

theorem tailTrace_3582513 : CollatzResearch.WordTrace tailWord_3582513 prefixEnd_3582513 1226367413320564756741219 := by
  unfold tailWord_3582513
  simp only [CollatzResearch.WordTrace]
  refine ⟨130664983670174720354080193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87109989113449813569386795 130664983670174720354080193)
  ·
    refine ⟨97998737752631040265560145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130664983670174720354080193 97998737752631040265560145)
    ·
      refine ⟨73499053314473280199170109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 97998737752631040265560145 73499053314473280199170109)
      ·
        refine ⟨27562144992927480074688791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73499053314473280199170109 27562144992927480074688791)
        ·
          refine ⟨41343217489391220112033187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27562144992927480074688791 41343217489391220112033187)
          ·
            refine ⟨62014826234086830168049781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41343217489391220112033187 62014826234086830168049781)
            ·
              refine ⟨5813889959445640328254667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62014826234086830168049781 5813889959445640328254667)
              ·
                refine ⟨8720834939168460492382001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5813889959445640328254667 8720834939168460492382001)
                ·
                  refine ⟨6540626204376345369286501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8720834939168460492382001 6540626204376345369286501)
                  ·
                    refine ⟨1226367413320564756741219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6540626204376345369286501 1226367413320564756741219)
                    ·
                      rfl

theorem cell22_3582513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 5, 1, 2, 4].length) (baseStart_3582513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582513 prefixEnd_3582513 := by exact prefixLift 3582513
  have htrace : WordTrace (prefixWord ++ tailWord_3582513) baseStart_3582513 baseEnd_3582513 := by
    simpa [prefixWord, tailWord_3582513, baseEnd_3582513] using wordTrace_append hprefix tailTrace_3582513
  have hstable : (prefixWord ++ tailWord_3582513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582513).length < 2 ^ (prefixWord ++ tailWord_3582513).sum := by decide
  have hdescent : baseEnd_3582513 < baseStart_3582513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582543 : List Nat := [1, 1, 2, 1, 1, 2, 5, 3, 3, 3]
def baseStart_3582543 : Nat := 118140960795 + 3582543 * 2 ^ 59
def prefixEnd_3582543 : Nat := 4983230072969 + 3 ^ 40 * 3582543 * 2
def baseEnd_3582543 : Nat := 1226377682933654678491127

theorem tailTrace_3582543 : CollatzResearch.WordTrace tailWord_3582543 prefixEnd_3582543 1226377682933654678491127 := by
  unfold tailWord_3582543
  simp only [CollatzResearch.WordTrace]
  refine ⟨130666077860066035477672283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87110718573377356985114855 130666077860066035477672283)
  ·
    refine ⟨195999116790099053216508425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130666077860066035477672283 195999116790099053216508425)
    ·
      refine ⟨146999337592574289912381319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 195999116790099053216508425 146999337592574289912381319)
      ·
        refine ⟨220499006388861434868571979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 146999337592574289912381319 220499006388861434868571979)
        ·
          refine ⟨330748509583292152302857969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220499006388861434868571979 330748509583292152302857969)
          ·
            refine ⟨248061382187469114227143477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330748509583292152302857969 248061382187469114227143477)
            ·
              refine ⟨23255754580075229458794701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 248061382187469114227143477 23255754580075229458794701)
              ·
                refine ⟨8720907967528211047048013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23255754580075229458794701 8720907967528211047048013)
                ·
                  refine ⟨3270340487823079142643005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8720907967528211047048013 3270340487823079142643005)
                  ·
                    refine ⟨1226377682933654678491127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3270340487823079142643005 1226377682933654678491127)
                    ·
                      rfl

theorem cell22_3582543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 3, 3, 3].length) (baseStart_3582543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582543 prefixEnd_3582543 := by exact prefixLift 3582543
  have htrace : WordTrace (prefixWord ++ tailWord_3582543) baseStart_3582543 baseEnd_3582543 := by
    simpa [prefixWord, tailWord_3582543, baseEnd_3582543] using wordTrace_append hprefix tailTrace_3582543
  have hstable : (prefixWord ++ tailWord_3582543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582543).length < 2 ^ (prefixWord ++ tailWord_3582543).sum := by decide
  have hdescent : baseEnd_3582543 < baseStart_3582543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582571 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 4, 5]
def baseStart_3582571 : Nat := 118140960795 + 3582571 * 2 ^ 59
def prefixEnd_3582571 : Nat := 4983230072969 + 3 ^ 40 * 3582571 * 2
def baseEnd_3582571 : Nat := 1226387267905871938791041

theorem tailTrace_3582571 : CollatzResearch.WordTrace tailWord_3582571 prefixEnd_3582571 1226387267905871938791041 := by
  unfold tailWord_3582571
  simp only [CollatzResearch.WordTrace]
  refine ⟨130667099103964596259691567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87111399402643064173127711 130667099103964596259691567)
  ·
    refine ⟨196000648655946894389537351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130667099103964596259691567 196000648655946894389537351)
    ·
      refine ⟨294000972983920341584306027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196000648655946894389537351 294000972983920341584306027)
      ·
        refine ⟨441001459475880512376459041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294000972983920341584306027 441001459475880512376459041)
        ·
          refine ⟨330751094606910384282344281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441001459475880512376459041 330751094606910384282344281)
          ·
            refine ⟨248063320955182788211758211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 330751094606910384282344281 248063320955182788211758211)
            ·
              refine ⟨372094981432774182317637317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248063320955182788211758211 372094981432774182317637317)
              ·
                refine ⟨69767809018645159184556997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 372094981432774182317637317 69767809018645159184556997)
                ·
                  refine ⟨13081464190995967347104437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69767809018645159184556997 13081464190995967347104437)
                  ·
                    refine ⟨1226387267905871938791041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13081464190995967347104437 1226387267905871938791041)
                    ·
                      rfl

theorem cell22_3582571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 4, 5].length) (baseStart_3582571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582571 prefixEnd_3582571 := by exact prefixLift 3582571
  have htrace : WordTrace (prefixWord ++ tailWord_3582571) baseStart_3582571 baseEnd_3582571 := by
    simpa [prefixWord, tailWord_3582571, baseEnd_3582571] using wordTrace_append hprefix tailTrace_3582571
  have hstable : (prefixWord ++ tailWord_3582571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582571).length < 2 ^ (prefixWord ++ tailWord_3582571).sum := by decide
  have hdescent : baseEnd_3582571 < baseStart_3582571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582573 : List Nat := [1, 5, 1, 1, 3, 1, 1, 2, 7]
def baseStart_3582573 : Nat := 118140960795 + 3582573 * 2 ^ 59
def prefixEnd_3582573 : Nat := 4983230072969 + 3 ^ 40 * 3582573 * 2
def baseEnd_3582573 : Nat := 408795984182248200080345

theorem tailTrace_3582573 : CollatzResearch.WordTrace tailWord_3582573 prefixEnd_3582573 408795984182248200080345 := by
  unfold tailWord_3582573
  simp only [CollatzResearch.WordTrace]
  refine ⟨130667172049957350601264373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87111448033304900400842915 130667172049957350601264373)
  ·
    refine ⟨12250047379683501618868535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130667172049957350601264373 12250047379683501618868535)
    ·
      refine ⟨18375071069525252428302803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12250047379683501618868535 18375071069525252428302803)
      ·
        refine ⟨27562606604287878642454205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18375071069525252428302803 27562606604287878642454205)
        ·
          refine ⟨10335977476607954490920327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27562606604287878642454205 10335977476607954490920327)
          ·
            refine ⟨15503966214911931736380491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10335977476607954490920327 15503966214911931736380491)
            ·
              refine ⟨23255949322367897604570737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15503966214911931736380491 23255949322367897604570737)
              ·
                refine ⟨17441961991775923203428053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23255949322367897604570737 17441961991775923203428053)
                ·
                  refine ⟨408795984182248200080345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17441961991775923203428053 408795984182248200080345)
                  ·
                    rfl

theorem cell22_3582573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_3582573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582573 prefixEnd_3582573 := by exact prefixLift 3582573
  have htrace : WordTrace (prefixWord ++ tailWord_3582573) baseStart_3582573 baseEnd_3582573 := by
    simpa [prefixWord, tailWord_3582573, baseEnd_3582573] using wordTrace_append hprefix tailTrace_3582573
  have hstable : (prefixWord ++ tailWord_3582573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582573).length < 2 ^ (prefixWord ++ tailWord_3582573).sum := by decide
  have hdescent : baseEnd_3582573 < baseStart_3582573 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582586 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 1, 10]
def baseStart_3582586 : Nat := 118140960795 + 3582586 * 2 ^ 59
def prefixEnd_3582586 : Nat := 4983230072969 + 3 ^ 40 * 3582586 * 2
def baseEnd_3582586 : Nat := 1226392402712416899665995

theorem tailTrace_3582586 : CollatzResearch.WordTrace tailWord_3582586 prefixEnd_3582586 1226392402712416899665995 := by
  unfold tailWord_3582586
  simp only [CollatzResearch.WordTrace]
  refine ⟨32666911549727563455371903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87111764132606835880991741 32666911549727563455371903)
  ·
    refine ⟨49000367324591345183057855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32666911549727563455371903 49000367324591345183057855)
    ·
      refine ⟨73500550986887017774586783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49000367324591345183057855 73500550986887017774586783)
      ·
        refine ⟨110250826480330526661880175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73500550986887017774586783 110250826480330526661880175)
        ·
          refine ⟨165376239720495789992820263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110250826480330526661880175 165376239720495789992820263)
          ·
            refine ⟨248064359580743684989230395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165376239720495789992820263 248064359580743684989230395)
            ·
              refine ⟨372096539371115527483845593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248064359580743684989230395 372096539371115527483845593)
              ·
                refine ⟨279072404528336645612884195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372096539371115527483845593 279072404528336645612884195)
                ·
                  refine ⟨418608606792504968419326293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279072404528336645612884195 418608606792504968419326293)
                  ·
                    refine ⟨1226392402712416899665995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 418608606792504968419326293 1226392402712416899665995)
                    ·
                      rfl

theorem cell22_3582586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 1, 10].length) (baseStart_3582586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582586 prefixEnd_3582586 := by exact prefixLift 3582586
  have htrace : WordTrace (prefixWord ++ tailWord_3582586) baseStart_3582586 baseEnd_3582586 := by
    simpa [prefixWord, tailWord_3582586, baseEnd_3582586] using wordTrace_append hprefix tailTrace_3582586
  have hstable : (prefixWord ++ tailWord_3582586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582586).length < 2 ^ (prefixWord ++ tailWord_3582586).sum := by decide
  have hdescent : baseEnd_3582586 < baseStart_3582586 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582620 : List Nat := [2, 2, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_3582620 : Nat := 118140960795 + 3582620 * 2 ^ 59
def prefixEnd_3582620 : Nat := 4983230072969 + 3 ^ 40 * 3582620 * 2
def baseEnd_3582620 : Nat := 1226404041607252144315891

theorem tailTrace_3582620 : CollatzResearch.WordTrace tailWord_3582620 prefixEnd_3582620 1226404041607252144315891 := by
  unfold tailWord_3582620
  simp only [CollatzResearch.WordTrace]
  refine ⟨65334443140393538814112657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87112590853858051752150209 65334443140393538814112657)
  ·
    refine ⟨49000832355295154110584493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65334443140393538814112657 49000832355295154110584493)
    ·
      refine ⟨18375312133235682791469185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49000832355295154110584493 18375312133235682791469185)
      ·
        refine ⟨13781484099926762093601889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18375312133235682791469185 13781484099926762093601889)
        ·
          refine ⟨10336113074945071570201417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13781484099926762093601889 10336113074945071570201417)
          ·
            refine ⟨7752084806208803677651063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10336113074945071570201417 7752084806208803677651063)
            ·
              refine ⟨11628127209313205516476595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7752084806208803677651063 11628127209313205516476595)
              ·
                refine ⟨17442190813969808274714893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11628127209313205516476595 17442190813969808274714893)
                ·
                  refine ⟨6540821555238678103018085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17442190813969808274714893 6540821555238678103018085)
                  ·
                    refine ⟨1226404041607252144315891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6540821555238678103018085 1226404041607252144315891)
                    ·
                      rfl

theorem cell22_3582620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_3582620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582620 prefixEnd_3582620 := by exact prefixLift 3582620
  have htrace : WordTrace (prefixWord ++ tailWord_3582620) baseStart_3582620 baseEnd_3582620 := by
    simpa [prefixWord, tailWord_3582620, baseEnd_3582620] using wordTrace_append hprefix tailTrace_3582620
  have hstable : (prefixWord ++ tailWord_3582620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582620).length < 2 ^ (prefixWord ++ tailWord_3582620).sum := by decide
  have hdescent : baseEnd_3582620 < baseStart_3582620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582680 : List Nat := [2, 1, 2, 2, 3, 3, 3, 6]
def baseStart_3582680 : Nat := 118140960795 + 3582680 * 2 ^ 59
def prefixEnd_3582680 : Nat := 4983230072969 + 3 ^ 40 * 3582680 * 2
def baseEnd_3582680 : Nat := 136269397870381331979523

theorem tailTrace_3582680 : CollatzResearch.WordTrace tailWord_3582680 prefixEnd_3582680 136269397870381331979523 := by
  unfold tailWord_3582680
  simp only [CollatzResearch.WordTrace]
  refine ⟨65335537330284853937704747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87114049773713138583606329 65335537330284853937704747)
  ·
    refine ⟨98003305995427280906557121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65335537330284853937704747 98003305995427280906557121)
    ·
      refine ⟨73502479496570460679917841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98003305995427280906557121 73502479496570460679917841)
      ·
        refine ⟨55126859622427845509938381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73502479496570460679917841 55126859622427845509938381)
        ·
          refine ⟨20672572358410442066226893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55126859622427845509938381 20672572358410442066226893)
          ·
            refine ⟨7752214634403915774835085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20672572358410442066226893 7752214634403915774835085)
            ·
              refine ⟨2907080487901468415563157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7752214634403915774835085 2907080487901468415563157)
              ·
                refine ⟨136269397870381331979523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2907080487901468415563157 136269397870381331979523)
                ·
                  rfl

theorem cell22_3582680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 3, 3, 6].length) (baseStart_3582680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582680 prefixEnd_3582680 := by exact prefixLift 3582680
  have htrace : WordTrace (prefixWord ++ tailWord_3582680) baseStart_3582680 baseEnd_3582680 := by
    simpa [prefixWord, tailWord_3582680, baseEnd_3582680] using wordTrace_append hprefix tailTrace_3582680
  have hstable : (prefixWord ++ tailWord_3582680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582680).length < 2 ^ (prefixWord ++ tailWord_3582680).sum := by decide
  have hdescent : baseEnd_3582680 < baseStart_3582680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582712 : List Nat := [2, 1, 2, 1, 1, 2, 3, 6, 1, 3]
def baseStart_3582712 : Nat := 118140960795 + 3582712 * 2 ^ 59
def prefixEnd_3582712 : Nat := 4983230072969 + 3 ^ 40 * 3582712 * 2
def baseEnd_3582712 : Nat := 1226435535087394571015609

theorem tailTrace_3582712 : CollatzResearch.WordTrace tailWord_3582712 prefixEnd_3582712 1226435535087394571015609 := by
  unfold tailWord_3582712
  simp only [CollatzResearch.WordTrace]
  refine ⟨65336120898226888670287195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87114827864302518227049593 65336120898226888670287195)
  ·
    refine ⟨98004181347340333005430793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65336120898226888670287195 98004181347340333005430793)
    ·
      refine ⟨73503136010505249754073095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98004181347340333005430793 73503136010505249754073095)
      ·
        refine ⟨110254704015757874631109643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73503136010505249754073095 110254704015757874631109643)
        ·
          refine ⟨165382056023636811946664465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110254704015757874631109643 165382056023636811946664465)
          ·
            refine ⟨124036542017727608959998349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165382056023636811946664465 124036542017727608959998349)
            ·
              refine ⟨46513703256647853359999381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124036542017727608959998349 46513703256647853359999381)
              ·
                refine ⟨2180329840155368126249971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46513703256647853359999381 2180329840155368126249971)
                ·
                  refine ⟨3270494760233052189374957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180329840155368126249971 3270494760233052189374957)
                  ·
                    refine ⟨1226435535087394571015609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3270494760233052189374957 1226435535087394571015609)
                    ·
                      rfl

theorem cell22_3582712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_3582712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582712 prefixEnd_3582712 := by exact prefixLift 3582712
  have htrace : WordTrace (prefixWord ++ tailWord_3582712) baseStart_3582712 baseEnd_3582712 := by
    simpa [prefixWord, tailWord_3582712, baseEnd_3582712] using wordTrace_append hprefix tailTrace_3582712
  have hstable : (prefixWord ++ tailWord_3582712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582712).length < 2 ^ (prefixWord ++ tailWord_3582712).sum := by decide
  have hdescent : baseEnd_3582712 < baseStart_3582712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582800 : List Nat := [2, 1, 1, 1, 1, 4, 3, 3, 2, 4]
def baseStart_3582800 : Nat := 118140960795 + 3582800 * 2 ^ 59
def prefixEnd_3582800 : Nat := 4983230072969 + 3 ^ 40 * 3582800 * 2
def baseEnd_3582800 : Nat := 1226465659285791674815339

theorem tailTrace_3582800 : CollatzResearch.WordTrace tailWord_3582800 prefixEnd_3582800 1226465659285791674815339 := by
  unfold tailWord_3582800
  simp only [CollatzResearch.WordTrace]
  refine ⟨65337725710067484184888927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87116967613423312246518569 65337725710067484184888927)
  ·
    refine ⟨98006588565101226277333391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65337725710067484184888927 98006588565101226277333391)
    ·
      refine ⟨147009882847651839416000087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98006588565101226277333391 147009882847651839416000087)
      ·
        refine ⟨220514824271477759124000131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147009882847651839416000087 220514824271477759124000131)
        ·
          refine ⟨330772236407216638686000197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220514824271477759124000131 330772236407216638686000197)
          ·
            refine ⟨62019794326353119753625037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 330772236407216638686000197 62019794326353119753625037)
            ·
              refine ⟨23257422872382419907609389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62019794326353119753625037 23257422872382419907609389)
              ·
                refine ⟨8721533577143407465353521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23257422872382419907609389 8721533577143407465353521)
                ·
                  refine ⟨6541150182857555599015141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8721533577143407465353521 6541150182857555599015141)
                  ·
                    refine ⟨1226465659285791674815339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6541150182857555599015141 1226465659285791674815339)
                    ·
                      rfl

theorem cell22_3582800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_3582800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582800 prefixEnd_3582800 := by exact prefixLift 3582800
  have htrace : WordTrace (prefixWord ++ tailWord_3582800) baseStart_3582800 baseEnd_3582800 := by
    simpa [prefixWord, tailWord_3582800, baseEnd_3582800] using wordTrace_append hprefix tailTrace_3582800
  have hstable : (prefixWord ++ tailWord_3582800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582800).length < 2 ^ (prefixWord ++ tailWord_3582800).sum := by decide
  have hdescent : baseEnd_3582800 < baseStart_3582800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582819 : List Nat := [1, 1, 1, 5, 3, 2, 2, 2, 2, 3]
def baseStart_3582819 : Nat := 118140960795 + 3582819 * 2 ^ 59
def prefixEnd_3582819 : Nat := 4983230072969 + 3 ^ 40 * 3582819 * 2
def baseEnd_3582819 : Nat := 1226472163374081958590281

theorem tailTrace_3582819 : CollatzResearch.WordTrace tailWord_3582819 prefixEnd_3582819 1226472163374081958590281 := by
  unfold tailWord_3582819
  simp only [CollatzResearch.WordTrace]
  refine ⟨130676144407066134614719511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87117429604710756409813007 130676144407066134614719511)
  ·
    refine ⟨196014216610599201922079267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130676144407066134614719511 196014216610599201922079267)
    ·
      refine ⟨294021324915898802883118901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196014216610599201922079267 294021324915898802883118901)
      ·
        refine ⟨27564499210865512770292397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294021324915898802883118901 27564499210865512770292397)
        ·
          refine ⟨10336687204074567288859649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27564499210865512770292397 10336687204074567288859649)
          ·
            refine ⟨7752515403055925466644737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10336687204074567288859649 7752515403055925466644737)
            ·
              refine ⟨5814386552291944099983553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7752515403055925466644737 5814386552291944099983553)
              ·
                refine ⟨4360789914218958074987665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5814386552291944099983553 4360789914218958074987665)
                ·
                  refine ⟨3270592435664218556240749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4360789914218958074987665 3270592435664218556240749)
                  ·
                    refine ⟨1226472163374081958590281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3270592435664218556240749 1226472163374081958590281)
                    ·
                      rfl

theorem cell22_3582819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 2, 2, 2, 3].length) (baseStart_3582819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582819 prefixEnd_3582819 := by exact prefixLift 3582819
  have htrace : WordTrace (prefixWord ++ tailWord_3582819) baseStart_3582819 baseEnd_3582819 := by
    simpa [prefixWord, tailWord_3582819, baseEnd_3582819] using wordTrace_append hprefix tailTrace_3582819
  have hstable : (prefixWord ++ tailWord_3582819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582819).length < 2 ^ (prefixWord ++ tailWord_3582819).sum := by decide
  have hdescent : baseEnd_3582819 < baseStart_3582819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582870 : List Nat := [5, 3, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_3582870 : Nat := 118140960795 + 3582870 * 2 ^ 59
def prefixEnd_3582870 : Nat := 4983230072969 + 3 ^ 40 * 3582870 * 2
def baseEnd_3582870 : Nat := 1226489621716334825565125

theorem tailTrace_3582870 : CollatzResearch.WordTrace tailWord_3582870 prefixEnd_3582870 1226489621716334825565125 := by
  unfold tailWord_3582870
  simp only [CollatzResearch.WordTrace]
  refine ⟨8167375283117585645301629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87118669686587580216550709 8167375283117585645301629)
  ·
    refine ⟨3062765731169094616988111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8167375283117585645301629 3062765731169094616988111)
    ·
      refine ⟨4594148596753641925482167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3062765731169094616988111 4594148596753641925482167)
      ·
        refine ⟨6891222895130462888223251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594148596753641925482167 6891222895130462888223251)
        ·
          refine ⟨10336834342695694332334877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891222895130462888223251 10336834342695694332334877)
          ·
            refine ⟨3876312878510885374625579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10336834342695694332334877 3876312878510885374625579)
            ·
              refine ⟨5814469317766328061938369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3876312878510885374625579 5814469317766328061938369)
              ·
                refine ⟨4360851988324746046453777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5814469317766328061938369 4360851988324746046453777)
                ·
                  refine ⟨3270638991243559534840333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4360851988324746046453777 3270638991243559534840333)
                  ·
                    refine ⟨1226489621716334825565125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3270638991243559534840333 1226489621716334825565125)
                    ·
                      rfl

theorem cell22_3582870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_3582870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582870 prefixEnd_3582870 := by exact prefixLift 3582870
  have htrace : WordTrace (prefixWord ++ tailWord_3582870) baseStart_3582870 baseEnd_3582870 := by
    simpa [prefixWord, tailWord_3582870, baseEnd_3582870] using wordTrace_append hprefix tailTrace_3582870
  have hstable : (prefixWord ++ tailWord_3582870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582870).length < 2 ^ (prefixWord ++ tailWord_3582870).sum := by decide
  have hdescent : baseEnd_3582870 < baseStart_3582870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582881 : List Nat := [1, 2, 3, 4, 1, 1, 2, 4, 1, 3]
def baseStart_3582881 : Nat := 118140960795 + 3582881 * 2 ^ 59
def prefixEnd_3582881 : Nat := 4983230072969 + 3 ^ 40 * 3582881 * 2
def baseEnd_3582881 : Nat := 1226493387241134463540091

theorem tailTrace_3582881 : CollatzResearch.WordTrace tailWord_3582881 prefixEnd_3582881 1226493387241134463540091 := by
  unfold tailWord_3582881
  simp only [CollatzResearch.WordTrace]
  refine ⟨130678405732841519203476497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87118937155227679468984331 130678405732841519203476497)
  ·
    refine ⟨98008804299631139402607373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130678405732841519203476497 98008804299631139402607373)
    ·
      refine ⟨36753301612361677275977765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98008804299631139402607373 36753301612361677275977765)
      ·
        refine ⟨6891244052317814489245831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36753301612361677275977765 6891244052317814489245831)
        ·
          refine ⟨10336866078476721733868747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6891244052317814489245831 10336866078476721733868747)
          ·
            refine ⟨15505299117715082600803121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10336866078476721733868747 15505299117715082600803121)
            ·
              refine ⟨11628974338286311950602341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15505299117715082600803121 11628974338286311950602341)
              ·
                refine ⟨2180432688428683490737939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11628974338286311950602341 2180432688428683490737939)
                ·
                  refine ⟨3270649032643025236106909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180432688428683490737939 3270649032643025236106909)
                  ·
                    refine ⟨1226493387241134463540091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3270649032643025236106909 1226493387241134463540091)
                    ·
                      rfl

theorem cell22_3582881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 4, 1, 3].length) (baseStart_3582881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582881 prefixEnd_3582881 := by exact prefixLift 3582881
  have htrace : WordTrace (prefixWord ++ tailWord_3582881) baseStart_3582881 baseEnd_3582881 := by
    simpa [prefixWord, tailWord_3582881, baseEnd_3582881] using wordTrace_append hprefix tailTrace_3582881
  have hstable : (prefixWord ++ tailWord_3582881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582881).length < 2 ^ (prefixWord ++ tailWord_3582881).sum := by decide
  have hdescent : baseEnd_3582881 < baseStart_3582881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582935 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 3, 6]
def baseStart_3582935 : Nat := 118140960795 + 3582935 * 2 ^ 59
def prefixEnd_3582935 : Nat := 4983230072969 + 3 ^ 40 * 3582935 * 2
def baseEnd_3582935 : Nat := 1226511872544696322689925

theorem tailTrace_3582935 : CollatzResearch.WordTrace tailWord_3582935 prefixEnd_3582935 1226511872544696322689925 := by
  unfold tailWord_3582935
  simp only [CollatzResearch.WordTrace]
  refine ⟨130680375274645886425942259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87120250183097257617294839 130680375274645886425942259)
  ·
    refine ⟨196020562911968829638913389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130680375274645886425942259 196020562911968829638913389)
    ·
      refine ⟨73507711091988311114592521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196020562911968829638913389 73507711091988311114592521)
      ·
        refine ⟨55130783318991233335944391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73507711091988311114592521 55130783318991233335944391)
        ·
          refine ⟨82696174978486850003916587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55130783318991233335944391 82696174978486850003916587)
          ·
            refine ⟨124044262467730275005874881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82696174978486850003916587 124044262467730275005874881)
            ·
              refine ⟨93033196850797706254406161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124044262467730275005874881 93033196850797706254406161)
              ·
                refine ⟨69774897638098279690804621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93033196850797706254406161 69774897638098279690804621)
                ·
                  refine ⟨26165586614286854884051733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69774897638098279690804621 26165586614286854884051733)
                  ·
                    refine ⟨1226511872544696322689925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26165586614286854884051733 1226511872544696322689925)
                    ·
                      rfl

theorem cell22_3582935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 6].length) (baseStart_3582935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582935 prefixEnd_3582935 := by exact prefixLift 3582935
  have htrace : WordTrace (prefixWord ++ tailWord_3582935) baseStart_3582935 baseEnd_3582935 := by
    simpa [prefixWord, tailWord_3582935, baseEnd_3582935] using wordTrace_append hprefix tailTrace_3582935
  have hstable : (prefixWord ++ tailWord_3582935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582935).length < 2 ^ (prefixWord ++ tailWord_3582935).sum := by decide
  have hdescent : baseEnd_3582935 < baseStart_3582935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582958 : List Nat := [4, 1, 2, 1, 5, 1, 1, 2, 1, 4]
def baseStart_3582958 : Nat := 118140960795 + 3582958 * 2 ^ 59
def prefixEnd_3582958 : Nat := 4983230072969 + 3 ^ 40 * 3582958 * 2
def baseEnd_3582958 : Nat := 1226519745914731929364855

theorem tailTrace_3582958 : CollatzResearch.WordTrace tailWord_3582958 prefixEnd_3582958 1226519745914731929364855 := by
  unfold tailWord_3582958
  simp only [CollatzResearch.WordTrace]
  refine ⟨16335151769195320169253691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87120809435708374236019685 16335151769195320169253691)
  ·
    refine ⟨24502727653792980253880537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16335151769195320169253691 24502727653792980253880537)
    ·
      refine ⟨18377045740344735190410403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24502727653792980253880537 18377045740344735190410403)
      ·
        refine ⟨27565568610517102785615605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18377045740344735190410403 27565568610517102785615605)
        ·
          refine ⟨2584272057235978386151463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 27565568610517102785615605 2584272057235978386151463)
          ·
            refine ⟨3876408085853967579227195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2584272057235978386151463 3876408085853967579227195)
            ·
              refine ⟨5814612128780951368840793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3876408085853967579227195 5814612128780951368840793)
              ·
                refine ⟨4360959096585713526630595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5814612128780951368840793 4360959096585713526630595)
                ·
                  refine ⟨6541438644878570289945893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4360959096585713526630595 6541438644878570289945893)
                  ·
                    refine ⟨1226519745914731929364855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6541438644878570289945893 1226519745914731929364855)
                    ·
                      rfl

theorem cell22_3582958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_3582958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582958 prefixEnd_3582958 := by exact prefixLift 3582958
  have htrace : WordTrace (prefixWord ++ tailWord_3582958) baseStart_3582958 baseEnd_3582958 := by
    simpa [prefixWord, tailWord_3582958, baseEnd_3582958] using wordTrace_append hprefix tailTrace_3582958
  have hstable : (prefixWord ++ tailWord_3582958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582958).length < 2 ^ (prefixWord ++ tailWord_3582958).sum := by decide
  have hdescent : baseEnd_3582958 < baseStart_3582958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3582997 : List Nat := [1, 3, 2, 1, 4, 1, 1, 1, 2, 6]
def baseStart_3582997 : Nat := 118140960795 + 3582997 * 2 ^ 59
def prefixEnd_3582997 : Nat := 4983230072969 + 3 ^ 40 * 3582997 * 2
def baseEnd_3582997 : Nat := 1226533096411748827639735

theorem tailTrace_3582997 : CollatzResearch.WordTrace tailWord_3582997 prefixEnd_3582997 1226533096411748827639735 := by
  unfold tailWord_3582997
  simp only [CollatzResearch.WordTrace]
  refine ⟨130682636600421271014699245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87121757733614180676466163 130682636600421271014699245)
  ·
    refine ⟨49005988725157976630512217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130682636600421271014699245 49005988725157976630512217)
    ·
      refine ⟨36754491543868482472884163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49005988725157976630512217 36754491543868482472884163)
      ·
        refine ⟨55131737315802723709326245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36754491543868482472884163 55131737315802723709326245)
        ·
          refine ⟨10337200746713010695498671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55131737315802723709326245 10337200746713010695498671)
          ·
            refine ⟨15505801120069516043248007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10337200746713010695498671 15505801120069516043248007)
            ·
              refine ⟨23258701680104274064872011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15505801120069516043248007 23258701680104274064872011)
              ·
                refine ⟨34888052520156411097308017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23258701680104274064872011 34888052520156411097308017)
                ·
                  refine ⟨26166039390117308322981013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34888052520156411097308017 26166039390117308322981013)
                  ·
                    refine ⟨1226533096411748827639735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26166039390117308322981013 1226533096411748827639735)
                    ·
                      rfl

theorem cell22_3582997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_3582997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3582997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3582997 prefixEnd_3582997 := by exact prefixLift 3582997
  have htrace : WordTrace (prefixWord ++ tailWord_3582997) baseStart_3582997 baseEnd_3582997 := by
    simpa [prefixWord, tailWord_3582997, baseEnd_3582997] using wordTrace_append hprefix tailTrace_3582997
  have hstable : (prefixWord ++ tailWord_3582997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3582997).length < 2 ^ (prefixWord ++ tailWord_3582997).sum := by decide
  have hdescent : baseEnd_3582997 < baseStart_3582997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3582997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583033 : List Nat := [1, 2, 1, 5, 2, 2, 2, 3, 1, 3]
def baseStart_3583033 : Nat := 118140960795 + 3583033 * 2 ^ 59
def prefixEnd_3583033 : Nat := 4983230072969 + 3 ^ 40 * 3583033 * 2
def baseEnd_3583033 : Nat := 1226545419947456733739625

theorem tailTrace_3583033 : CollatzResearch.WordTrace tailWord_3583033 prefixEnd_3583033 1226545419947456733739625 := by
  unfold tailWord_3583033
  simp only [CollatzResearch.WordTrace]
  refine ⟨130683949628290849163009753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87122633085527232775339835 130683949628290849163009753)
  ·
    refine ⟨98012962221218136872257315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130683949628290849163009753 98012962221218136872257315)
    ·
      refine ⟨147019443331827205308385973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98012962221218136872257315 147019443331827205308385973)
      ·
        refine ⟨13783072812358800497661185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147019443331827205308385973 13783072812358800497661185)
        ·
          refine ⟨10337304609269100373245889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13783072812358800497661185 10337304609269100373245889)
          ·
            refine ⟨7752978456951825279934417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10337304609269100373245889 7752978456951825279934417)
            ·
              refine ⟨5814733842713868959950813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7752978456951825279934417 5814733842713868959950813)
              ·
                refine ⟨2180525191017700859981555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5814733842713868959950813 2180525191017700859981555)
                ·
                  refine ⟨3270787786526551289972333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2180525191017700859981555 3270787786526551289972333)
                  ·
                    refine ⟨1226545419947456733739625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3270787786526551289972333 1226545419947456733739625)
                    ·
                      rfl

theorem cell22_3583033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 2, 3, 1, 3].length) (baseStart_3583033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583033 prefixEnd_3583033 := by exact prefixLift 3583033
  have htrace : WordTrace (prefixWord ++ tailWord_3583033) baseStart_3583033 baseEnd_3583033 := by
    simpa [prefixWord, tailWord_3583033, baseEnd_3583033] using wordTrace_append hprefix tailTrace_3583033
  have hstable : (prefixWord ++ tailWord_3583033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583033).length < 2 ^ (prefixWord ++ tailWord_3583033).sum := by decide
  have hdescent : baseEnd_3583033 < baseStart_3583033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583046 : List Nat := [6, 1, 1, 1, 1, 3, 1, 1, 7]
def baseStart_3583046 : Nat := 118140960795 + 3583046 * 2 ^ 59
def prefixEnd_3583046 : Nat := 4983230072969 + 3 ^ 40 * 3583046 * 2
def baseEnd_3583046 : Nat := 408849956704376344388195

theorem tailTrace_3583046 : CollatzResearch.WordTrace tailWord_3583046 prefixEnd_3583046 408849956704376344388195 := by
  unfold tailWord_3583046
  simp only [CollatzResearch.WordTrace]
  refine ⟨4083888243038867261976031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87122949184829168255488661 4083888243038867261976031)
  ·
    refine ⟨6125832364558300892964047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4083888243038867261976031 6125832364558300892964047)
    ·
      refine ⟨9188748546837451339446071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6125832364558300892964047 9188748546837451339446071)
      ·
        refine ⟨13783122820256177009169107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9188748546837451339446071 13783122820256177009169107)
        ·
          refine ⟨20674684230384265513753661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13783122820256177009169107 20674684230384265513753661)
          ·
            refine ⟨7753006586394099567657623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20674684230384265513753661 7753006586394099567657623)
            ·
              refine ⟨11629509879591149351486435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753006586394099567657623 11629509879591149351486435)
              ·
                refine ⟨17444264819386724027229653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11629509879591149351486435 17444264819386724027229653)
                ·
                  refine ⟨408849956704376344388195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17444264819386724027229653 408849956704376344388195)
                  ·
                    rfl

theorem cell22_3583046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_3583046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583046 prefixEnd_3583046 := by exact prefixLift 3583046
  have htrace : WordTrace (prefixWord ++ tailWord_3583046) baseStart_3583046 baseEnd_3583046 := by
    simpa [prefixWord, tailWord_3583046, baseEnd_3583046] using wordTrace_append hprefix tailTrace_3583046
  have hstable : (prefixWord ++ tailWord_3583046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583046).length < 2 ^ (prefixWord ++ tailWord_3583046).sum := by decide
  have hdescent : baseEnd_3583046 < baseStart_3583046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583057 : List Nat := [1, 2, 2, 1, 3, 1, 3, 3, 6]
def baseStart_3583057 : Nat := 118140960795 + 3583057 * 2 ^ 59
def prefixEnd_3583057 : Nat := 4983230072969 + 3 ^ 40 * 3583057 * 2
def baseEnd_3583057 : Nat := 408851211879309557046517

theorem tailTrace_3583057 : CollatzResearch.WordTrace tailWord_3583057 prefixEnd_3583057 408851211879309557046517 := by
  unfold tailWord_3583057
  simp only [CollatzResearch.WordTrace]
  refine ⟨130684824980203901261883425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87123216653469267507922283 130684824980203901261883425)
  ·
    refine ⟨98013618735152925946412569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130684824980203901261883425 98013618735152925946412569)
    ·
      refine ⟨73510214051364694459809427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98013618735152925946412569 73510214051364694459809427)
      ·
        refine ⟨110265321077047041689714141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73510214051364694459809427 110265321077047041689714141)
        ·
          refine ⟨41349495403892640633642803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110265321077047041689714141 41349495403892640633642803)
          ·
            refine ⟨62024243105838960950464205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41349495403892640633642803 62024243105838960950464205)
            ·
              refine ⟨23259091164689610356424077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62024243105838960950464205 23259091164689610356424077)
              ·
                refine ⟨8722159186758603883659029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23259091164689610356424077 8722159186758603883659029)
                ·
                  refine ⟨408851211879309557046517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8722159186758603883659029 408851211879309557046517)
                  ·
                    rfl

theorem cell22_3583057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 3, 6].length) (baseStart_3583057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583057 prefixEnd_3583057 := by exact prefixLift 3583057
  have htrace : WordTrace (prefixWord ++ tailWord_3583057) baseStart_3583057 baseEnd_3583057 := by
    simpa [prefixWord, tailWord_3583057, baseEnd_3583057] using wordTrace_append hprefix tailTrace_3583057
  have hstable : (prefixWord ++ tailWord_3583057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583057).length < 2 ^ (prefixWord ++ tailWord_3583057).sum := by decide
  have hdescent : baseEnd_3583057 < baseStart_3583057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583087 : List Nat := [1, 1, 2, 1, 3, 3, 1, 3, 1, 6]
def baseStart_3583087 : Nat := 118140960795 + 3583087 * 2 ^ 59
def prefixEnd_3583087 : Nat := 4983230072969 + 3 ^ 40 * 3583087 * 2
def baseEnd_3583087 : Nat := 1226563905251018592889459

theorem tailTrace_3583087 : CollatzResearch.WordTrace tailWord_3583087 prefixEnd_3583087 1226563905251018592889459 := by
  unfold tailWord_3583087
  simp only [CollatzResearch.WordTrace]
  refine ⟨130685919170095216385475515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87123946113396810923650343 130685919170095216385475515)
  ·
    refine ⟨196028878755142824578213273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130685919170095216385475515 196028878755142824578213273)
    ·
      refine ⟨147021659066357118433659955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196028878755142824578213273 147021659066357118433659955)
      ·
        refine ⟨220532488599535677650489933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147021659066357118433659955 220532488599535677650489933)
        ·
          refine ⟨82699683224825879118933725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220532488599535677650489933 82699683224825879118933725)
          ·
            refine ⟨31012381209309704669600147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82699683224825879118933725 31012381209309704669600147)
            ·
              refine ⟨46518571813964557004400221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31012381209309704669600147 46518571813964557004400221)
              ·
                refine ⟨17444464430236708876650083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46518571813964557004400221 17444464430236708876650083)
                ·
                  refine ⟨26166696645355063314975125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17444464430236708876650083 26166696645355063314975125)
                  ·
                    refine ⟨1226563905251018592889459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26166696645355063314975125 1226563905251018592889459)
                    ·
                      rfl

theorem cell22_3583087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 6].length) (baseStart_3583087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583087 prefixEnd_3583087 := by exact prefixLift 3583087
  have htrace : WordTrace (prefixWord ++ tailWord_3583087) baseStart_3583087 baseEnd_3583087 := by
    simpa [prefixWord, tailWord_3583087, baseEnd_3583087] using wordTrace_append hprefix tailTrace_3583087
  have hstable : (prefixWord ++ tailWord_3583087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583087).length < 2 ^ (prefixWord ++ tailWord_3583087).sum := by decide
  have hdescent : baseEnd_3583087 < baseStart_3583087 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583108 : List Nat := [2, 3, 2, 1, 2, 3, 3, 2, 4]
def baseStart_3583108 : Nat := 118140960795 + 3583108 * 2 ^ 59
def prefixEnd_3583108 : Nat := 4983230072969 + 3 ^ 40 * 3583108 * 2
def baseEnd_3583108 : Nat := 408857031326727179371465

theorem tailTrace_3583108 : CollatzResearch.WordTrace tailWord_3583108 prefixEnd_3583108 408857031326727179371465 := by
  unfold tailWord_3583108
  simp only [CollatzResearch.WordTrace]
  refine ⟨65343342551509568485994989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87124456735346091314659985 65343342551509568485994989)
  ·
    refine ⟨24503753456816088182248121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65343342551509568485994989 24503753456816088182248121)
    ·
      refine ⟨18377815092612066136686091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24503753456816088182248121 18377815092612066136686091)
      ·
        refine ⟨27566722638918099205029137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18377815092612066136686091 27566722638918099205029137)
        ·
          refine ⟨20675041979188574403771853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27566722638918099205029137 20675041979188574403771853)
          ·
            refine ⟨7753140742195715401414445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20675041979188574403771853 7753140742195715401414445)
            ·
              refine ⟨2907427778323393275530417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7753140742195715401414445 2907427778323393275530417)
              ·
                refine ⟨2180570833742544956647813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2907427778323393275530417 2180570833742544956647813)
                ·
                  refine ⟨408857031326727179371465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2180570833742544956647813 408857031326727179371465)
                  ·
                    rfl

theorem cell22_3583108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_3583108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583108 prefixEnd_3583108 := by exact prefixLift 3583108
  have htrace : WordTrace (prefixWord ++ tailWord_3583108) baseStart_3583108 baseEnd_3583108 := by
    simpa [prefixWord, tailWord_3583108, baseEnd_3583108] using wordTrace_append hprefix tailTrace_3583108
  have hstable : (prefixWord ++ tailWord_3583108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583108).length < 2 ^ (prefixWord ++ tailWord_3583108).sum := by decide
  have hdescent : baseEnd_3583108 < baseStart_3583108 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583138 : List Nat := [3, 3, 1, 3, 2, 1, 2, 1, 2, 4]
def baseStart_3583138 : Nat := 118140960795 + 3583138 * 2 ^ 59
def prefixEnd_3583138 : Nat := 4983230072969 + 3 ^ 40 * 3583138 * 2
def baseEnd_3583138 : Nat := 1226581363593271459864303

theorem tailTrace_3583138 : CollatzResearch.WordTrace tailWord_3583138 prefixEnd_3583138 1226581363593271459864303 := by
  unfold tailWord_3583138
  simp only [CollatzResearch.WordTrace]
  refine ⟨32671944823227613023895517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87125186195273634730388045 32671944823227613023895517)
  ·
    refine ⟨12251979308710354883960819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32671944823227613023895517 12251979308710354883960819)
    ·
      refine ⟨18377968963065532325941229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12251979308710354883960819 18377968963065532325941229)
      ·
        refine ⟨6891738361149574622227961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18377968963065532325941229 6891738361149574622227961)
        ·
          refine ⟨5168803770862180966670971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6891738361149574622227961 5168803770862180966670971)
          ·
            refine ⟨7753205656293271450006457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5168803770862180966670971 7753205656293271450006457)
            ·
              refine ⟨5814904242219953587504843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7753205656293271450006457 5814904242219953587504843)
              ·
                refine ⟨8722356363329930381257265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5814904242219953587504843 8722356363329930381257265)
                ·
                  refine ⟨6541767272497447785942949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8722356363329930381257265 6541767272497447785942949)
                  ·
                    refine ⟨1226581363593271459864303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6541767272497447785942949 1226581363593271459864303)
                    ·
                      rfl

theorem cell22_3583138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_3583138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583138 prefixEnd_3583138 := by exact prefixLift 3583138
  have htrace : WordTrace (prefixWord ++ tailWord_3583138) baseStart_3583138 baseEnd_3583138 := by
    simpa [prefixWord, tailWord_3583138, baseEnd_3583138] using wordTrace_append hprefix tailTrace_3583138
  have hstable : (prefixWord ++ tailWord_3583138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583138).length < 2 ^ (prefixWord ++ tailWord_3583138).sum := by decide
  have hdescent : baseEnd_3583138 < baseStart_3583138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583170 : List Nat := [3, 5, 1, 1, 2, 2, 1, 7]
def baseStart_3583170 : Nat := 118140960795 + 3583170 * 2 ^ 59
def prefixEnd_3583170 : Nat := 4983230072969 + 3 ^ 40 * 3583170 * 2
def baseEnd_3583170 : Nat := 136288035316359338118245

theorem tailTrace_3583170 : CollatzResearch.WordTrace tailWord_3583170 prefixEnd_3583170 136288035316359338118245 := by
  unfold tailWord_3583170
  simp only [CollatzResearch.WordTrace]
  refine ⟨32672236607198630390186741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87125964285863014373831309 32672236607198630390186741)
  ·
    refine ⟨3063022181924871599080007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 32672236607198630390186741 3063022181924871599080007)
    ·
      refine ⟨4594533272887307398620011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3063022181924871599080007 4594533272887307398620011)
      ·
        refine ⟨6891799909330961097930017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594533272887307398620011 6891799909330961097930017)
        ·
          refine ⟨5168849931998220823447513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6891799909330961097930017 5168849931998220823447513)
          ·
            refine ⟨3876637448998665617585635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5168849931998220823447513 3876637448998665617585635)
            ·
              refine ⟨5814956173497998426378453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3876637448998665617585635 5814956173497998426378453)
              ·
                refine ⟨136288035316359338118245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5814956173497998426378453 136288035316359338118245)
                ·
                  rfl

theorem cell22_3583170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 2, 1, 7].length) (baseStart_3583170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583170 prefixEnd_3583170 := by exact prefixLift 3583170
  have htrace : WordTrace (prefixWord ++ tailWord_3583170) baseStart_3583170 baseEnd_3583170 := by
    simpa [prefixWord, tailWord_3583170, baseEnd_3583170] using wordTrace_append hprefix tailTrace_3583170
  have hstable : (prefixWord ++ tailWord_3583170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583170).length < 2 ^ (prefixWord ++ tailWord_3583170).sum := by decide
  have hdescent : baseEnd_3583170 < baseStart_3583170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583211 : List Nat := [1, 1, 1, 1, 2, 7, 1, 3, 1, 4]
def baseStart_3583211 : Nat := 118140960795 + 3583211 * 2 ^ 59
def prefixEnd_3583211 : Nat := 4983230072969 + 3 ^ 40 * 3583211 * 2
def baseEnd_3583211 : Nat := 1226606352985123602789079

theorem tailTrace_3583211 : CollatzResearch.WordTrace tailWord_3583211 prefixEnd_3583211 1226606352985123602789079 := by
  unfold tailWord_3583211
  simp only [CollatzResearch.WordTrace]
  refine ⟨130690441821645985562989487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87126961214430657041992991 130690441821645985562989487)
  ·
    refine ⟨196035662732468978344484231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130690441821645985562989487 196035662732468978344484231)
    ·
      refine ⟨294053494098703467516726347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196035662732468978344484231 294053494098703467516726347)
      ·
        refine ⟨441080241148055201275089521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294053494098703467516726347 441080241148055201275089521)
        ·
          refine ⟨330810180861041400956317141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 441080241148055201275089521 330810180861041400956317141)
          ·
            refine ⟨7753363613930657834913683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 330810180861041400956317141 7753363613930657834913683)
            ·
              refine ⟨11630045420895986752370525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753363613930657834913683 11630045420895986752370525)
              ·
                refine ⟨4361267032835995032138947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11630045420895986752370525 4361267032835995032138947)
                ·
                  refine ⟨6541900549253992548208421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361267032835995032138947 6541900549253992548208421)
                  ·
                    refine ⟨1226606352985123602789079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6541900549253992548208421 1226606352985123602789079)
                    ·
                      rfl

theorem cell22_3583211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 4].length) (baseStart_3583211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583211 prefixEnd_3583211 := by exact prefixLift 3583211
  have htrace : WordTrace (prefixWord ++ tailWord_3583211) baseStart_3583211 baseEnd_3583211 := by
    simpa [prefixWord, tailWord_3583211, baseEnd_3583211] using wordTrace_append hprefix tailTrace_3583211
  have hstable : (prefixWord ++ tailWord_3583211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583211).length < 2 ^ (prefixWord ++ tailWord_3583211).sum := by decide
  have hdescent : baseEnd_3583211 < baseStart_3583211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583226 : List Nat := [3, 1, 1, 1, 1, 4, 1, 6, 4]
def baseStart_3583226 : Nat := 118140960795 + 3583226 * 2 ^ 59
def prefixEnd_3583226 : Nat := 4983230072969 + 3 ^ 40 * 3583226 * 2
def baseEnd_3583226 : Nat := 408870495930556187888011

theorem tailTrace_3583226 : CollatzResearch.WordTrace tailWord_3583226 prefixEnd_3583226 408870495930556187888011 := by
  unfold tailWord_3583226
  simp only [CollatzResearch.WordTrace]
  refine ⟨32672747229147910781196383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87127325944394428749857021 32672747229147910781196383)
  ·
    refine ⟨49009120843721866171794575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32672747229147910781196383 49009120843721866171794575)
    ·
      refine ⟨73513681265582799257691863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49009120843721866171794575 73513681265582799257691863)
      ·
        refine ⟨110270521898374198886537795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73513681265582799257691863 110270521898374198886537795)
        ·
          refine ⟨165405782847561298329806693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110270521898374198886537795 165405782847561298329806693)
          ·
            refine ⟨31013584283917743436838755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165405782847561298329806693 31013584283917743436838755)
            ·
              refine ⟨46520376425876615155258133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31013584283917743436838755 46520376425876615155258133)
              ·
                refine ⟨2180642644962966335402725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46520376425876615155258133 2180642644962966335402725)
                ·
                  refine ⟨408870495930556187888011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2180642644962966335402725 408870495930556187888011)
                  ·
                    rfl

theorem cell22_3583226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 6, 4].length) (baseStart_3583226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583226 prefixEnd_3583226 := by exact prefixLift 3583226
  have htrace : WordTrace (prefixWord ++ tailWord_3583226) baseStart_3583226 baseEnd_3583226 := by
    simpa [prefixWord, tailWord_3583226, baseEnd_3583226] using wordTrace_append hprefix tailTrace_3583226
  have hstable : (prefixWord ++ tailWord_3583226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583226).length < 2 ^ (prefixWord ++ tailWord_3583226).sum := by decide
  have hdescent : baseEnd_3583226 < baseStart_3583226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583277 : List Nat := [1, 5, 3, 1, 1, 2, 3, 2, 4]
def baseStart_3583277 : Nat := 118140960795 + 3583277 * 2 ^ 59
def prefixEnd_3583277 : Nat := 4983230072969 + 3 ^ 40 * 3583277 * 2
def baseEnd_3583277 : Nat := 408876315377973810212959

theorem tailTrace_3583277 : CollatzResearch.WordTrace tailWord_3583277 prefixEnd_3583277 408876315377973810212959 := by
  unfold tailWord_3583277
  simp only [CollatzResearch.WordTrace]
  refine ⟨130692849039406878834892085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87128566026271252556594723 130692849039406878834892085)
  ·
    refine ⟨12252454597444394890771133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130692849039406878834892085 12252454597444394890771133)
    ·
      refine ⟨4594670474041648084039175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12252454597444394890771133 4594670474041648084039175)
      ·
        refine ⟨6892005711062472126058763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4594670474041648084039175 6892005711062472126058763)
        ·
          refine ⟨10338008566593708189088145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6892005711062472126058763 10338008566593708189088145)
          ·
            refine ⟨7753506424945281141816109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10338008566593708189088145 7753506424945281141816109)
            ·
              refine ⟨2907564909354480428181041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7753506424945281141816109 2907564909354480428181041)
              ·
                refine ⟨2180673682015860321135781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2907564909354480428181041 2180673682015860321135781)
                ·
                  refine ⟨408876315377973810212959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2180673682015860321135781 408876315377973810212959)
                  ·
                    rfl

theorem cell22_3583277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 2, 4].length) (baseStart_3583277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583277 prefixEnd_3583277 := by exact prefixLift 3583277
  have htrace : WordTrace (prefixWord ++ tailWord_3583277) baseStart_3583277 baseEnd_3583277 := by
    simpa [prefixWord, tailWord_3583277, baseEnd_3583277] using wordTrace_append hprefix tailTrace_3583277
  have hstable : (prefixWord ++ tailWord_3583277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583277).length < 2 ^ (prefixWord ++ tailWord_3583277).sum := by decide
  have hdescent : baseEnd_3583277 < baseStart_3583277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583346 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_3583346 : Nat := 118140960795 + 3583346 * 2 ^ 59
def prefixEnd_3583346 : Nat := 4983230072969 + 3 ^ 40 * 3583346 * 2
def baseEnd_3583346 : Nat := 1226652566244028250663665

theorem tailTrace_3583346 : CollatzResearch.WordTrace tailWord_3583346 prefixEnd_3583346 1226652566244028250663665 := by
  unfold tailWord_3583346
  simp only [CollatzResearch.WordTrace]
  refine ⟨32673841419039225904788473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87130243784104602412769261 32673841419039225904788473)
  ·
    refine ⟨24505381064279419428591355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32673841419039225904788473 24505381064279419428591355)
    ·
      refine ⟨36758071596419129142887033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24505381064279419428591355 36758071596419129142887033)
      ·
        refine ⟨27568553697314346857165275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36758071596419129142887033 27568553697314346857165275)
        ·
          refine ⟨41352830545971520285747913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27568553697314346857165275 41352830545971520285747913)
          ·
            refine ⟨31014622909478640214310935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41352830545971520285747913 31014622909478640214310935)
            ·
              refine ⟨46521934364217960321466403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31014622909478640214310935 46521934364217960321466403)
              ·
                refine ⟨69782901546326940482199605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46521934364217960321466403 69782901546326940482199605)
                ·
                  refine ⟨6542147019968150670206213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69782901546326940482199605 6542147019968150670206213)
                  ·
                    refine ⟨1226652566244028250663665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6542147019968150670206213 1226652566244028250663665)
                    ·
                      rfl

theorem cell22_3583346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_3583346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583346 prefixEnd_3583346 := by exact prefixLift 3583346
  have htrace : WordTrace (prefixWord ++ tailWord_3583346) baseStart_3583346 baseEnd_3583346 := by
    simpa [prefixWord, tailWord_3583346, baseEnd_3583346] using wordTrace_append hprefix tailTrace_3583346
  have hstable : (prefixWord ++ tailWord_3583346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583346).length < 2 ^ (prefixWord ++ tailWord_3583346).sum := by decide
  have hdescent : baseEnd_3583346 < baseStart_3583346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583380 : List Nat := [2, 4, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_3583380 : Nat := 118140960795 + 3583380 * 2 ^ 59
def prefixEnd_3583380 : Nat := 4983230072969 + 3 ^ 40 * 3583380 * 2
def baseEnd_3583380 : Nat := 1226664205138863495313561

theorem tailTrace_3583380 : CollatzResearch.WordTrace tailWord_3583380 prefixEnd_3583380 1226664205138863495313561 := by
  unfold tailWord_3583380
  simp only [CollatzResearch.WordTrace]
  refine ⟨65348302879016863712945797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87131070505355818283927729 65348302879016863712945797)
  ·
    refine ⟨12252806789815661946177337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65348302879016863712945797 12252806789815661946177337)
    ·
      refine ⟨9189605092361746459633003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12252806789815661946177337 9189605092361746459633003)
      ·
        refine ⟨13784407638542619689449505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9189605092361746459633003 13784407638542619689449505)
        ·
          refine ⟨10338305728906964767087129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13784407638542619689449505 10338305728906964767087129)
          ·
            refine ⟨7753729296680223575315347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10338305728906964767087129 7753729296680223575315347)
            ·
              refine ⟨11630593945020335362973021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7753729296680223575315347 11630593945020335362973021)
              ·
                refine ⟨4361472729382625761114883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11630593945020335362973021 4361472729382625761114883)
                ·
                  refine ⟨6542209094073938641672325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361472729382625761114883 6542209094073938641672325)
                  ·
                    refine ⟨1226664205138863495313561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6542209094073938641672325 1226664205138863495313561)
                    ·
                      rfl

theorem cell22_3583380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_3583380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583380 prefixEnd_3583380 := by exact prefixLift 3583380
  have htrace : WordTrace (prefixWord ++ tailWord_3583380) baseStart_3583380 baseEnd_3583380 := by
    simpa [prefixWord, tailWord_3583380, baseEnd_3583380] using wordTrace_append hprefix tailTrace_3583380
  have hstable : (prefixWord ++ tailWord_3583380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583380).length < 2 ^ (prefixWord ++ tailWord_3583380).sum := by decide
  have hdescent : baseEnd_3583380 < baseStart_3583380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583421 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_3583421 : Nat := 118140960795 + 3583421 * 2 ^ 59
def prefixEnd_3583421 : Nat := 4983230072969 + 3 ^ 40 * 3583421 * 2
def baseEnd_3583421 : Nat := 1226678240276753055038435

theorem tailTrace_3583421 : CollatzResearch.WordTrace tailWord_3583421 prefixEnd_3583421 1226678240276753055038435 := by
  unfold tailWord_3583421
  simp only [CollatzResearch.WordTrace]
  refine ⟨130698101150885191428134117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87132067433923460952089411 130698101150885191428134117)
  ·
    refine ⟨24505893965790973392775147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130698101150885191428134117 24505893965790973392775147)
    ·
      refine ⟨36758840948686460089162721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24505893965790973392775147 36758840948686460089162721)
      ·
        refine ⟨27569130711514845066872041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36758840948686460089162721 27569130711514845066872041)
        ·
          refine ⟨20676848033636133800154031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27569130711514845066872041 20676848033636133800154031)
          ·
            refine ⟨31015272050454200700231047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20676848033636133800154031 31015272050454200700231047)
            ·
              refine ⟨46522908075681301050346571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31015272050454200700231047 46522908075681301050346571)
              ·
                refine ⟨69784362113521951575519857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46522908075681301050346571 69784362113521951575519857)
                ·
                  refine ⟨52338271585141463681639893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69784362113521951575519857 52338271585141463681639893)
                  ·
                    refine ⟨1226678240276753055038435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52338271585141463681639893 1226678240276753055038435)
                    ·
                      rfl

theorem cell22_3583421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_3583421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583421 prefixEnd_3583421 := by exact prefixLift 3583421
  have htrace : WordTrace (prefixWord ++ tailWord_3583421) baseStart_3583421 baseEnd_3583421 := by
    simpa [prefixWord, tailWord_3583421, baseEnd_3583421] using wordTrace_append hprefix tailTrace_3583421
  have hstable : (prefixWord ++ tailWord_3583421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583421).length < 2 ^ (prefixWord ++ tailWord_3583421).sum := by decide
  have hdescent : baseEnd_3583421 < baseStart_3583421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583438 : List Nat := [4, 1, 1, 1, 2, 1, 2, 2, 5, 3]
def baseStart_3583438 : Nat := 118140960795 + 3583438 * 2 ^ 59
def prefixEnd_3583438 : Nat := 4983230072969 + 3 ^ 40 * 3583438 * 2
def baseEnd_3583438 : Nat := 1226684059724170677363383

theorem tailTrace_3583438 : CollatzResearch.WordTrace tailWord_3583438 prefixEnd_3583438 1226684059724170677363383 := by
  unfold tailWord_3583438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16337340148977950416437871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87132480794549068887668645 16337340148977950416437871)
  ·
    refine ⟨24506010223466925624656807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16337340148977950416437871 24506010223466925624656807)
    ·
      refine ⟨36759015335200388436985211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24506010223466925624656807 36759015335200388436985211)
      ·
        refine ⟨55138523002800582655477817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36759015335200388436985211 55138523002800582655477817)
        ·
          refine ⟨41353892252100436991608363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55138523002800582655477817 41353892252100436991608363)
          ·
            refine ⟨62030838378150655487412545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41353892252100436991608363 62030838378150655487412545)
            ·
              refine ⟨46523128783612991615559409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62030838378150655487412545 46523128783612991615559409)
              ·
                refine ⟨34892346587709743711669557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46523128783612991615559409 34892346587709743711669557)
                ·
                  refine ⟨3271157492597788472969021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34892346587709743711669557 3271157492597788472969021)
                  ·
                    refine ⟨1226684059724170677363383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3271157492597788472969021 1226684059724170677363383)
                    ·
                      rfl

theorem cell22_3583438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_3583438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583438 prefixEnd_3583438 := by exact prefixLift 3583438
  have htrace : WordTrace (prefixWord ++ tailWord_3583438) baseStart_3583438 baseEnd_3583438 := by
    simpa [prefixWord, tailWord_3583438, baseEnd_3583438] using wordTrace_append hprefix tailTrace_3583438
  have hstable : (prefixWord ++ tailWord_3583438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583438).length < 2 ^ (prefixWord ++ tailWord_3583438).sum := by decide
  have hdescent : baseEnd_3583438 < baseStart_3583438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583543 : List Nat := [1, 1, 3, 1, 2, 5, 1, 1, 1, 6]
def baseStart_3583543 : Nat := 118140960795 + 3583543 * 2 ^ 59
def prefixEnd_3583543 : Nat := 4983230072969 + 3 ^ 40 * 3583543 * 2
def baseEnd_3583543 : Nat := 1226720003369985403488061

theorem tailTrace_3583543 : CollatzResearch.WordTrace tailWord_3583543 prefixEnd_3583543 1226720003369985403488061 := by
  unfold tailWord_3583543
  simp only [CollatzResearch.WordTrace]
  refine ⟨130702550856443206264075283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87135033904295470842716855 130702550856443206264075283)
  ·
    refine ⟨196053826284664809396112925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130702550856443206264075283 196053826284664809396112925)
    ·
      refine ⟨73520184856749303523542347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196053826284664809396112925 73520184856749303523542347)
      ·
        refine ⟨110280277285123955285313521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73520184856749303523542347 110280277285123955285313521)
        ·
          refine ⟨82710207963842966463985141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110280277285123955285313521 82710207963842966463985141)
          ·
            refine ⟨7754081996610278105998607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82710207963842966463985141 7754081996610278105998607)
            ·
              refine ⟨11631122994915417158997911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7754081996610278105998607 11631122994915417158997911)
              ·
                refine ⟨17446684492373125738496867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11631122994915417158997911 17446684492373125738496867)
                ·
                  refine ⟨26170026738559688607745301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17446684492373125738496867 26170026738559688607745301)
                  ·
                    refine ⟨1226720003369985403488061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26170026738559688607745301 1226720003369985403488061)
                    ·
                      rfl

theorem cell22_3583543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 1, 1, 6].length) (baseStart_3583543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583543 prefixEnd_3583543 := by exact prefixLift 3583543
  have htrace : WordTrace (prefixWord ++ tailWord_3583543) baseStart_3583543 baseEnd_3583543 := by
    simpa [prefixWord, tailWord_3583543, baseEnd_3583543] using wordTrace_append hprefix tailTrace_3583543
  have hstable : (prefixWord ++ tailWord_3583543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583543).length < 2 ^ (prefixWord ++ tailWord_3583543).sum := by decide
  have hdescent : baseEnd_3583543 < baseStart_3583543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583549 : List Nat := [1, 4, 1, 3, 3, 2, 2, 1, 1, 4]
def baseStart_3583549 : Nat := 118140960795 + 3583549 * 2 ^ 59
def prefixEnd_3583549 : Nat := 4983230072969 + 3 ^ 40 * 3583549 * 2
def baseEnd_3583549 : Nat := 1226722057292603387838043

theorem tailTrace_3583549 : CollatzResearch.WordTrace tailWord_3583549 prefixEnd_3583549 1226722057292603387838043 := by
  unfold tailWord_3583549
  simp only [CollatzResearch.WordTrace]
  refine ⟨130702769694421469288793701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87135179796280979525862467 130702769694421469288793701)
  ·
    refine ⟨24506769317704025491648819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130702769694421469288793701 24506769317704025491648819)
    ·
      refine ⟨36760153976556038237473229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24506769317704025491648819 36760153976556038237473229)
      ·
        refine ⟨13785057741208514339052461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36760153976556038237473229 13785057741208514339052461)
        ·
          refine ⟨5169396652953192877144673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13785057741208514339052461 5169396652953192877144673)
          ·
            refine ⟨3877047489714894657858505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5169396652953192877144673 3877047489714894657858505)
            ·
              refine ⟨2907785617286170993393879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3877047489714894657858505 2907785617286170993393879)
              ·
                refine ⟨4361678425929256490090819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907785617286170993393879 4361678425929256490090819)
                ·
                  refine ⟨6542517638893884735136229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361678425929256490090819 6542517638893884735136229)
                  ·
                    refine ⟨1226722057292603387838043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6542517638893884735136229 1226722057292603387838043)
                    ·
                      rfl

theorem cell22_3583549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_3583549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583549 prefixEnd_3583549 := by exact prefixLift 3583549
  have htrace : WordTrace (prefixWord ++ tailWord_3583549) baseStart_3583549 baseEnd_3583549 := by
    simpa [prefixWord, tailWord_3583549, baseEnd_3583549] using wordTrace_append hprefix tailTrace_3583549
  have hstable : (prefixWord ++ tailWord_3583549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583549).length < 2 ^ (prefixWord ++ tailWord_3583549).sum := by decide
  have hdescent : baseEnd_3583549 < baseStart_3583549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583592 : List Nat := [2, 1, 4, 3, 1, 3, 2, 6]
def baseStart_3583592 : Nat := 118140960795 + 3583592 * 2 ^ 59
def prefixEnd_3583592 : Nat := 4983230072969 + 3 ^ 40 * 3583592 * 2
def baseEnd_3583592 : Nat := 136304086341262845445879

theorem tailTrace_3583592 : CollatzResearch.WordTrace tailWord_3583592 prefixEnd_3583592 136304086341262845445879 := by
  unfold tailWord_3583592
  simp only [CollatzResearch.WordTrace]
  refine ⟨65352169016632843816304515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87136225355510458421739353 65352169016632843816304515)
  ·
    refine ⟨98028253524949265724456773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65352169016632843816304515 98028253524949265724456773)
    ·
      refine ⟨18380297535927987323335645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98028253524949265724456773 18380297535927987323335645)
      ·
        refine ⟨6892611575972995246250867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18380297535927987323335645 6892611575972995246250867)
        ·
          refine ⟨10338917363959492869376301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6892611575972995246250867 10338917363959492869376301)
          ·
            refine ⟨3877094011484809826016113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10338917363959492869376301 3877094011484809826016113)
            ·
              refine ⟨2907820508613607369512085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3877094011484809826016113 2907820508613607369512085)
              ·
                refine ⟨136304086341262845445879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2907820508613607369512085 136304086341262845445879)
                ·
                  rfl

theorem cell22_3583592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 3, 2, 6].length) (baseStart_3583592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583592 prefixEnd_3583592 := by exact prefixLift 3583592
  have htrace : WordTrace (prefixWord ++ tailWord_3583592) baseStart_3583592 baseEnd_3583592 := by
    simpa [prefixWord, tailWord_3583592, baseEnd_3583592] using wordTrace_append hprefix tailTrace_3583592
  have hstable : (prefixWord ++ tailWord_3583592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583592).length < 2 ^ (prefixWord ++ tailWord_3583592).sum := by decide
  have hdescent : baseEnd_3583592 < baseStart_3583592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583667 : List Nat := [1, 1, 1, 2, 3, 3, 5, 1, 1, 4]
def baseStart_3583667 : Nat := 118140960795 + 3583667 * 2 ^ 59
def prefixEnd_3583667 : Nat := 4983230072969 + 3 ^ 40 * 3583667 * 2
def baseEnd_3583667 : Nat := 1226762451104090413387681

theorem tailTrace_3583667 : CollatzResearch.WordTrace tailWord_3583667 prefixEnd_3583667 1226762451104090413387681 := by
  unfold tailWord_3583667
  simp only [CollatzResearch.WordTrace]
  refine ⟨130707073507993975441589255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87138049005329316961059503 130707073507993975441589255)
  ·
    refine ⟨196060610261990963162383883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130707073507993975441589255 196060610261990963162383883)
    ·
      refine ⟨294090915392986444743575825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196060610261990963162383883 294090915392986444743575825)
      ·
        refine ⟨220568186544739833557681869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294090915392986444743575825 220568186544739833557681869)
        ·
          refine ⟨82713069954277437584130701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220568186544739833557681869 82713069954277437584130701)
          ·
            refine ⟨31017401232854039094049013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82713069954277437584130701 31017401232854039094049013)
            ·
              refine ⟨2907881365580066165067095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 31017401232854039094049013 2907881365580066165067095)
              ·
                refine ⟨4361822048370099247600643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907881365580066165067095 4361822048370099247600643)
                ·
                  refine ⟨6542733072555148871400965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4361822048370099247600643 6542733072555148871400965)
                  ·
                    refine ⟨1226762451104090413387681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6542733072555148871400965 1226762451104090413387681)
                    ·
                      rfl

theorem cell22_3583667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 5, 1, 1, 4].length) (baseStart_3583667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583667 prefixEnd_3583667 := by exact prefixLift 3583667
  have htrace : WordTrace (prefixWord ++ tailWord_3583667) baseStart_3583667 baseEnd_3583667 := by
    simpa [prefixWord, tailWord_3583667, baseEnd_3583667] using wordTrace_append hprefix tailTrace_3583667
  have hstable : (prefixWord ++ tailWord_3583667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583667).length < 2 ^ (prefixWord ++ tailWord_3583667).sum := by decide
  have hdescent : baseEnd_3583667 < baseStart_3583667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583697 : List Nat := [1, 2, 2, 1, 2, 4, 2, 3, 2, 3]
def baseStart_3583697 : Nat := 118140960795 + 3583697 * 2 ^ 59
def prefixEnd_3583697 : Nat := 4983230072969 + 3 ^ 40 * 3583697 * 2
def baseEnd_3583697 : Nat := 1226772720717180335137589

theorem tailTrace_3583697 : CollatzResearch.WordTrace tailWord_3583697 prefixEnd_3583697 1226772720717180335137589 := by
  unfold tailWord_3583697
  simp only [CollatzResearch.WordTrace]
  refine ⟨130708167697885290565181345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87138778465256860376787563 130708167697885290565181345)
  ·
    refine ⟨98031125773413967923886009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130708167697885290565181345 98031125773413967923886009)
    ·
      refine ⟨73523344330060475942914507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98031125773413967923886009 73523344330060475942914507)
      ·
        refine ⟨110285016495090713914371761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73523344330060475942914507 110285016495090713914371761)
        ·
          refine ⟨82713762371318035435778821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110285016495090713914371761 82713762371318035435778821)
          ·
            refine ⟨15508830444622131644208529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82713762371318035435778821 15508830444622131644208529)
            ·
              refine ⟨11631622833466598733156397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15508830444622131644208529 11631622833466598733156397)
              ·
                refine ⟨4361858562549974524933649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11631622833466598733156397 4361858562549974524933649)
                ·
                  refine ⟨3271393921912480893700237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4361858562549974524933649 3271393921912480893700237)
                  ·
                    refine ⟨1226772720717180335137589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3271393921912480893700237 1226772720717180335137589)
                    ·
                      rfl

theorem cell22_3583697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 3, 2, 3].length) (baseStart_3583697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583697 prefixEnd_3583697 := by exact prefixLift 3583697
  have htrace : WordTrace (prefixWord ++ tailWord_3583697) baseStart_3583697 baseEnd_3583697 := by
    simpa [prefixWord, tailWord_3583697, baseEnd_3583697] using wordTrace_append hprefix tailTrace_3583697
  have hstable : (prefixWord ++ tailWord_3583697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583697).length < 2 ^ (prefixWord ++ tailWord_3583697).sum := by decide
  have hdescent : baseEnd_3583697 < baseStart_3583697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583755 : List Nat := [1, 1, 1, 1, 5, 1, 2, 5, 5]
def baseStart_3583755 : Nat := 118140960795 + 3583755 * 2 ^ 59
def prefixEnd_3583755 : Nat := 4983230072969 + 3 ^ 40 * 3583755 * 2
def baseEnd_3583755 : Nat := 408930858434162505729137

theorem tailTrace_3583755 : CollatzResearch.WordTrace tailWord_3583755 prefixEnd_3583755 408930858434162505729137 := by
  unfold tailWord_3583755
  simp only [CollatzResearch.WordTrace]
  refine ⟨130710283131675166470792719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87140188754450110980528479 130710283131675166470792719)
  ·
    refine ⟨196065424697512749706189079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130710283131675166470792719 196065424697512749706189079)
    ·
      refine ⟨294098137046269124559283619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196065424697512749706189079 294098137046269124559283619)
      ·
        refine ⟨441147205569403686838925429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294098137046269124559283619 441147205569403686838925429)
        ·
          refine ⟨41357550522131595641149259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 441147205569403686838925429 41357550522131595641149259)
          ·
            refine ⟨62036325783197393461723889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41357550522131595641149259 62036325783197393461723889)
            ·
              refine ⟨46527244337398045096292917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62036325783197393461723889 46527244337398045096292917)
              ·
                refine ⟨4361929156631066727777461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46527244337398045096292917 4361929156631066727777461)
                ·
                  refine ⟨408930858434162505729137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4361929156631066727777461 408930858434162505729137)
                  ·
                    rfl

theorem cell22_3583755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 5, 5].length) (baseStart_3583755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583755 prefixEnd_3583755 := by exact prefixLift 3583755
  have htrace : WordTrace (prefixWord ++ tailWord_3583755) baseStart_3583755 baseEnd_3583755 := by
    simpa [prefixWord, tailWord_3583755, baseEnd_3583755] using wordTrace_append hprefix tailTrace_3583755
  have hstable : (prefixWord ++ tailWord_3583755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583755).length < 2 ^ (prefixWord ++ tailWord_3583755).sum := by decide
  have hdescent : baseEnd_3583755 < baseStart_3583755 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583806 : List Nat := [4, 2, 1, 2, 2, 3, 2, 1, 5]
def baseStart_3583806 : Nat := 118140960795 + 3583806 * 2 ^ 59
def prefixEnd_3583806 : Nat := 4983230072969 + 3 ^ 40 * 3583806 * 2
def baseEnd_3583806 : Nat := 408936677881580128054085

theorem tailTrace_3583806 : CollatzResearch.WordTrace tailWord_3583806 prefixEnd_3583806 408936677881580128054085 := by
  unfold tailWord_3583806
  simp only [CollatzResearch.WordTrace]
  refine ⟨16339017906811300272612409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87141428836326934787266181 16339017906811300272612409)
  ·
    refine ⟨12254263430108475204459307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16339017906811300272612409 12254263430108475204459307)
    ·
      refine ⟨18381395145162712806688961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12254263430108475204459307 18381395145162712806688961)
      ·
        refine ⟨13786046358872034605016721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18381395145162712806688961 13786046358872034605016721)
        ·
          refine ⟨10339534769154025953762541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13786046358872034605016721 10339534769154025953762541)
          ·
            refine ⟨3877325538432759732660953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10339534769154025953762541 3877325538432759732660953)
            ·
              refine ⟨2907994153824569799495715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3877325538432759732660953 2907994153824569799495715)
              ·
                refine ⟨4361991230736854699243573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2907994153824569799495715 4361991230736854699243573)
                ·
                  refine ⟨408936677881580128054085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4361991230736854699243573 408936677881580128054085)
                  ·
                    rfl

theorem cell22_3583806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_3583806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583806 prefixEnd_3583806 := by exact prefixLift 3583806
  have htrace : WordTrace (prefixWord ++ tailWord_3583806) baseStart_3583806 baseEnd_3583806 := by
    simpa [prefixWord, tailWord_3583806, baseEnd_3583806] using wordTrace_append hprefix tailTrace_3583806
  have hstable : (prefixWord ++ tailWord_3583806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583806).length < 2 ^ (prefixWord ++ tailWord_3583806).sum := by decide
  have hdescent : baseEnd_3583806 < baseStart_3583806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583847 : List Nat := [1, 1, 5, 1, 2, 1, 1, 4, 2, 4]
def baseStart_3583847 : Nat := 118140960795 + 3583847 * 2 ^ 59
def prefixEnd_3583847 : Nat := 4983230072969 + 3 ^ 40 * 3583847 * 2
def baseEnd_3583847 : Nat := 1226824068782629943887129

theorem tailTrace_3583847 : CollatzResearch.WordTrace tailWord_3583847 prefixEnd_3583847 1226824068782629943887129 := by
  unfold tailWord_3583847
  simp only [CollatzResearch.WordTrace]
  refine ⟨130713638647341866183141795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87142425764894577455427863 130713638647341866183141795)
  ·
    refine ⟨196070457971012799274712693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130713638647341866183141795 196070457971012799274712693)
    ·
      refine ⟨18381605434782449932004315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196070457971012799274712693 18381605434782449932004315)
      ·
        refine ⟨27572408152173674898006473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18381605434782449932004315 27572408152173674898006473)
        ·
          refine ⟨20679306114130256173504855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27572408152173674898006473 20679306114130256173504855)
          ·
            refine ⟨31018959171195384260257283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20679306114130256173504855 31018959171195384260257283)
            ·
              refine ⟨46528438756793076390385925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31018959171195384260257283 46528438756793076390385925)
              ·
                refine ⟨8724082266898701823197361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46528438756793076390385925 8724082266898701823197361)
                ·
                  refine ⟨6543061700174026367398021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8724082266898701823197361 6543061700174026367398021)
                  ·
                    refine ⟨1226824068782629943887129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6543061700174026367398021 1226824068782629943887129)
                    ·
                      rfl

theorem cell22_3583847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_3583847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583847 prefixEnd_3583847 := by exact prefixLift 3583847
  have htrace : WordTrace (prefixWord ++ tailWord_3583847) baseStart_3583847 baseEnd_3583847 := by
    simpa [prefixWord, tailWord_3583847, baseEnd_3583847] using wordTrace_append hprefix tailTrace_3583847
  have hstable : (prefixWord ++ tailWord_3583847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583847).length < 2 ^ (prefixWord ++ tailWord_3583847).sum := by decide
  have hdescent : baseEnd_3583847 < baseStart_3583847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583879 : List Nat := [1, 1, 4, 2, 4, 1, 3, 6]
def baseStart_3583879 : Nat := 118140960795 + 3583879 * 2 ^ 59
def prefixEnd_3583879 : Nat := 4983230072969 + 3 ^ 40 * 3583879 * 2
def baseEnd_3583879 : Nat := 136315002559621391898559

theorem tailTrace_3583879 : CollatzResearch.WordTrace tailWord_3583879 prefixEnd_3583879 136315002559621391898559 := by
  unfold tailWord_3583879
  simp only [CollatzResearch.WordTrace]
  refine ⟨130714805783225935648306691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87143203855483957098871127 130714805783225935648306691)
  ·
    refine ⟨196072208674838903472460037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130714805783225935648306691 196072208674838903472460037)
    ·
      refine ⟨36763539126532294401086257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196072208674838903472460037 36763539126532294401086257)
      ·
        refine ⟨27572654344899220800814693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36763539126532294401086257 27572654344899220800814693)
        ·
          refine ⟨5169872689668603900152755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 27572654344899220800814693 5169872689668603900152755)
          ·
            refine ⟨7754809034502905850229133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5169872689668603900152755 7754809034502905850229133)
            ·
              refine ⟨2908053387938589693835925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7754809034502905850229133 2908053387938589693835925)
              ·
                refine ⟨136315002559621391898559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2908053387938589693835925 136315002559621391898559)
                ·
                  rfl

theorem cell22_3583879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 4, 1, 3, 6].length) (baseStart_3583879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583879 prefixEnd_3583879 := by exact prefixLift 3583879
  have htrace : WordTrace (prefixWord ++ tailWord_3583879) baseStart_3583879 baseEnd_3583879 := by
    simpa [prefixWord, tailWord_3583879, baseEnd_3583879] using wordTrace_append hprefix tailTrace_3583879
  have hstable : (prefixWord ++ tailWord_3583879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583879).length < 2 ^ (prefixWord ++ tailWord_3583879).sum := by decide
  have hdescent : baseEnd_3583879 < baseStart_3583879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583911 : List Nat := [1, 1, 6, 1, 2, 2, 2, 1, 3, 3]
def baseStart_3583911 : Nat := 118140960795 + 3583911 * 2 ^ 59
def prefixEnd_3583911 : Nat := 4983230072969 + 3 ^ 40 * 3583911 * 2
def baseEnd_3583911 : Nat := 1226845977290555110286933

theorem tailTrace_3583911 : CollatzResearch.WordTrace tailWord_3583911 prefixEnd_3583911 1226845977290555110286933 := by
  unfold tailWord_3583911
  simp only [CollatzResearch.WordTrace]
  refine ⟨130715972919110005113471587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87143981946073336742314391 130715972919110005113471587)
  ·
    refine ⟨196073959378665007670207381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130715972919110005113471587 196073959378665007670207381)
    ·
      refine ⟨9190966845874922234540971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 196073959378665007670207381 9190966845874922234540971)
      ·
        refine ⟨13786450268812383351811457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9190966845874922234540971 13786450268812383351811457)
        ·
          refine ⟨10339837701609287513858593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13786450268812383351811457 10339837701609287513858593)
          ·
            refine ⟨7754878276206965635393945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10339837701609287513858593 7754878276206965635393945)
            ·
              refine ⟨5816158707155224226545459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7754878276206965635393945 5816158707155224226545459)
              ·
                refine ⟨8724238060732836339818189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5816158707155224226545459 8724238060732836339818189)
                ·
                  refine ⟨3271589272774813627431821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8724238060732836339818189 3271589272774813627431821)
                  ·
                    refine ⟨1226845977290555110286933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3271589272774813627431821 1226845977290555110286933)
                    ·
                      rfl

theorem cell22_3583911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_3583911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583911 prefixEnd_3583911 := by exact prefixLift 3583911
  have htrace : WordTrace (prefixWord ++ tailWord_3583911) baseStart_3583911 baseEnd_3583911 := by
    simpa [prefixWord, tailWord_3583911, baseEnd_3583911] using wordTrace_append hprefix tailTrace_3583911
  have hstable : (prefixWord ++ tailWord_3583911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583911).length < 2 ^ (prefixWord ++ tailWord_3583911).sum := by decide
  have hdescent : baseEnd_3583911 < baseStart_3583911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583969 : List Nat := [1, 2, 3, 1, 2, 1, 2, 6, 4]
def baseStart_3583969 : Nat := 118140960795 + 3583969 * 2 ^ 59
def prefixEnd_3583969 : Nat := 4983230072969 + 3 ^ 40 * 3583969 * 2
def baseEnd_3583969 : Nat := 408955277291954097445585

theorem tailTrace_3583969 : CollatzResearch.WordTrace tailWord_3583969 prefixEnd_3583969 408955277291954097445585 := by
  unfold tailWord_3583969
  simp only [CollatzResearch.WordTrace]
  refine ⟨130718088352899881019082961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87145392235266587346055307 130718088352899881019082961)
  ·
    refine ⟨98038566264674910764312221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130718088352899881019082961 98038566264674910764312221)
    ·
      refine ⟨36764462349253091536617083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98038566264674910764312221 36764462349253091536617083)
      ·
        refine ⟨55146693523879637304925625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36764462349253091536617083 55146693523879637304925625)
        ·
          refine ⟨41360020142909727978694219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55146693523879637304925625 41360020142909727978694219)
          ·
            refine ⟨62040030214364591968041329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41360020142909727978694219 62040030214364591968041329)
            ·
              refine ⟨46530022660773443976030997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62040030214364591968041329 46530022660773443976030997)
              ·
                refine ⟨2181094812223755186376453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 46530022660773443976030997 2181094812223755186376453)
                ·
                  refine ⟨408955277291954097445585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181094812223755186376453 408955277291954097445585)
                  ·
                    rfl

theorem cell22_3583969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 6, 4].length) (baseStart_3583969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583969 prefixEnd_3583969 := by exact prefixLift 3583969
  have htrace : WordTrace (prefixWord ++ tailWord_3583969) baseStart_3583969 baseEnd_3583969 := by
    simpa [prefixWord, tailWord_3583969, baseEnd_3583969] using wordTrace_append hprefix tailTrace_3583969
  have hstable : (prefixWord ++ tailWord_3583969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583969).length < 2 ^ (prefixWord ++ tailWord_3583969).sum := by decide
  have hdescent : baseEnd_3583969 < baseStart_3583969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3583997 : List Nat := [1, 4, 1, 1, 1, 2, 4, 8]
def baseStart_3583997 : Nat := 118140960795 + 3583997 * 2 ^ 59
def prefixEnd_3583997 : Nat := 4983230072969 + 3 ^ 40 * 3583997 * 2
def baseEnd_3583997 : Nat := 136319490760897728070741

theorem tailTrace_3583997 : CollatzResearch.WordTrace tailWord_3583997 prefixEnd_3583997 136319490760897728070741 := by
  unfold tailWord_3583997
  simp only [CollatzResearch.WordTrace]
  refine ⟨130719109596798441801102245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87146073064532294534068163 130719109596798441801102245)
  ·
    refine ⟨24509833049399707837706671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130719109596798441801102245 24509833049399707837706671)
    ·
      refine ⟨36764749574099561756560007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24509833049399707837706671 36764749574099561756560007)
      ·
        refine ⟨55147124361149342634840011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36764749574099561756560007 55147124361149342634840011)
        ·
          refine ⟨82720686541724013952260017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55147124361149342634840011 82720686541724013952260017)
          ·
            refine ⟨62040514906293010464195013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82720686541724013952260017 62040514906293010464195013)
            ·
              refine ⟨11632596544929939462036565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62040514906293010464195013 11632596544929939462036565)
              ·
                refine ⟨136319490760897728070741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11632596544929939462036565 136319490760897728070741)
                ·
                  rfl

theorem cell22_3583997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 8].length) (baseStart_3583997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3583997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3583997 prefixEnd_3583997 := by exact prefixLift 3583997
  have htrace : WordTrace (prefixWord ++ tailWord_3583997) baseStart_3583997 baseEnd_3583997 := by
    simpa [prefixWord, tailWord_3583997, baseEnd_3583997] using wordTrace_append hprefix tailTrace_3583997
  have hstable : (prefixWord ++ tailWord_3583997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3583997).length < 2 ^ (prefixWord ++ tailWord_3583997).sum := by decide
  have hdescent : baseEnd_3583997 < baseStart_3583997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3583997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584020 : List Nat := [2, 4, 3, 2, 1, 1, 1, 4, 4]
def baseStart_3584020 : Nat := 118140960795 + 3584020 * 2 ^ 59
def prefixEnd_3584020 : Nat := 4983230072969 + 3 ^ 40 * 3584020 * 2
def baseEnd_3584020 : Nat := 408961096739371719770533

theorem tailTrace_3584020 : CollatzResearch.WordTrace tailWord_3584020 prefixEnd_3584020 408961096739371719770533 := by
  unfold tailWord_3584020
  simp only [CollatzResearch.WordTrace]
  refine ⟨65359974237857558364594757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87146632317143411152793009 65359974237857558364594757)
  ·
    refine ⟨12254995169598292193361517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65359974237857558364594757 12254995169598292193361517)
    ·
      refine ⟨4595623188599359572510569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12254995169598292193361517 4595623188599359572510569)
      ·
        refine ⟨3446717391449519679382927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4595623188599359572510569 3446717391449519679382927)
        ·
          refine ⟨5170076087174279519074391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3446717391449519679382927 5170076087174279519074391)
          ·
            refine ⟨7755114130761419278611587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5170076087174279519074391 7755114130761419278611587)
            ·
              refine ⟨11632671196142128917917381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7755114130761419278611587 11632671196142128917917381)
              ·
                refine ⟨2181125849276649172109509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11632671196142128917917381 2181125849276649172109509)
                ·
                  refine ⟨408961096739371719770533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181125849276649172109509 408961096739371719770533)
                  ·
                    rfl

theorem cell22_3584020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 4, 4].length) (baseStart_3584020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584020 prefixEnd_3584020 := by exact prefixLift 3584020
  have htrace : WordTrace (prefixWord ++ tailWord_3584020) baseStart_3584020 baseEnd_3584020 := by
    simpa [prefixWord, tailWord_3584020, baseEnd_3584020] using wordTrace_append hprefix tailTrace_3584020
  have hstable : (prefixWord ++ tailWord_3584020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584020).length < 2 ^ (prefixWord ++ tailWord_3584020).sum := by decide
  have hdescent : baseEnd_3584020 < baseStart_3584020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584046 : List Nat := [4, 1, 3, 1, 1, 2, 1, 1, 5, 3]
def baseStart_3584046 : Nat := 118140960795 + 3584046 * 2 ^ 59
def prefixEnd_3584046 : Nat := 4983230072969 + 3 ^ 40 * 3584046 * 2
def baseEnd_3584046 : Nat := 1226892190549459758161519

theorem tailTrace_3584046 : CollatzResearch.WordTrace tailWord_3584046 prefixEnd_3584046 1226892190549459758161519 := by
  unfold tailWord_3584046
  simp only [CollatzResearch.WordTrace]
  refine ⟨16340112096702615396204499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87147264515747282113090661 16340112096702615396204499)
  ·
    refine ⟨24510168145053923094306749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16340112096702615396204499 24510168145053923094306749)
    ·
      refine ⟨9191313054395221160365031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24510168145053923094306749 9191313054395221160365031)
      ·
        refine ⟨13786969581592831740547547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9191313054395221160365031 13786969581592831740547547)
        ·
          refine ⟨20680454372389247610821321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13786969581592831740547547 20680454372389247610821321)
          ·
            refine ⟨15510340779291935708115991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20680454372389247610821321 15510340779291935708115991)
            ·
              refine ⟨23265511168937903562173987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15510340779291935708115991 23265511168937903562173987)
              ·
                refine ⟨34898266753406855343260981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23265511168937903562173987 34898266753406855343260981)
                ·
                  refine ⟨3271712508131892688430717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 34898266753406855343260981 3271712508131892688430717)
                  ·
                    refine ⟨1226892190549459758161519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3271712508131892688430717 1226892190549459758161519)
                    ·
                      rfl

theorem cell22_3584046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_3584046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584046 prefixEnd_3584046 := by exact prefixLift 3584046
  have htrace : WordTrace (prefixWord ++ tailWord_3584046) baseStart_3584046 baseEnd_3584046 := by
    simpa [prefixWord, tailWord_3584046, baseEnd_3584046] using wordTrace_append hprefix tailTrace_3584046
  have hstable : (prefixWord ++ tailWord_3584046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584046).length < 2 ^ (prefixWord ++ tailWord_3584046).sum := by decide
  have hdescent : baseEnd_3584046 < baseStart_3584046 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584149 : List Nat := [1, 3, 2, 1, 1, 1, 6, 7]
def baseStart_3584149 : Nat := 118140960795 + 3584149 * 2 ^ 59
def prefixEnd_3584149 : Nat := 4983230072969 + 3 ^ 40 * 3584149 * 2
def baseEnd_3584149 : Nat := 136325272172711313648467

theorem tailTrace_3584149 : CollatzResearch.WordTrace tailWord_3584149 prefixEnd_3584149 136325272172711313648467 := by
  unfold tailWord_3584149
  simp only [CollatzResearch.WordTrace]
  refine ⟨130724653492247771760635501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87149768994831847840423667 130724653492247771760635501)
  ·
    refine ⟨49021745059592914410238313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130724653492247771760635501 49021745059592914410238313)
    ·
      refine ⟨36766308794694685807678735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49021745059592914410238313 36766308794694685807678735)
      ·
        refine ⟨55149463192042028711518103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36766308794694685807678735 55149463192042028711518103)
        ·
          refine ⟨82724194788063043067277155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55149463192042028711518103 82724194788063043067277155)
          ·
            refine ⟨124086292182094564600915733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82724194788063043067277155 124086292182094564600915733)
            ·
              refine ⟨5816544946035682715667925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 124086292182094564600915733 5816544946035682715667925)
              ·
                refine ⟨136325272172711313648467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5816544946035682715667925 136325272172711313648467)
                ·
                  rfl

theorem cell22_3584149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 6, 7].length) (baseStart_3584149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584149 prefixEnd_3584149 := by exact prefixLift 3584149
  have htrace : WordTrace (prefixWord ++ tailWord_3584149) baseStart_3584149 baseEnd_3584149 := by
    simpa [prefixWord, tailWord_3584149, baseEnd_3584149] using wordTrace_append hprefix tailTrace_3584149
  have hstable : (prefixWord ++ tailWord_3584149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584149).length < 2 ^ (prefixWord ++ tailWord_3584149).sum := by decide
  have hdescent : baseEnd_3584149 < baseStart_3584149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584196 : List Nat := [2, 3, 3, 1, 2, 1, 1, 1, 2, 6]
def baseStart_3584196 : Nat := 118140960795 + 3584196 * 2 ^ 59
def prefixEnd_3584196 : Nat := 4983230072969 + 3 ^ 40 * 3584196 * 2
def baseEnd_3584196 : Nat := 1226943538614909366911059

theorem tailTrace_3584196 : CollatzResearch.WordTrace tailWord_3584196 prefixEnd_3584196 1226943538614909366911059 := by
  unfold tailWord_3584196
  simp only [CollatzResearch.WordTrace]
  refine ⟨65363183861538749393798221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87150911815384999191730961 65363183861538749393798221)
  ·
    refine ⟨24511193948077031022674333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65363183861538749393798221 24511193948077031022674333)
    ·
      refine ⟨9191697730528886633502875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24511193948077031022674333 9191697730528886633502875)
      ·
        refine ⟨13787546595793329950254313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9191697730528886633502875 13787546595793329950254313)
        ·
          refine ⟨10340659946844997462690735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13787546595793329950254313 10340659946844997462690735)
          ·
            refine ⟨15510989920267496194036103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10340659946844997462690735 15510989920267496194036103)
            ·
              refine ⟨23266484880401244291054155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15510989920267496194036103 23266484880401244291054155)
              ·
                refine ⟨34899727320601866436581233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23266484880401244291054155 34899727320601866436581233)
                ·
                  refine ⟨26174795490451399827435925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34899727320601866436581233 26174795490451399827435925)
                  ·
                    refine ⟨1226943538614909366911059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26174795490451399827435925 1226943538614909366911059)
                    ·
                      rfl

theorem cell22_3584196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_3584196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584196 prefixEnd_3584196 := by exact prefixLift 3584196
  have htrace : WordTrace (prefixWord ++ tailWord_3584196) baseStart_3584196 baseEnd_3584196 := by
    simpa [prefixWord, tailWord_3584196, baseEnd_3584196] using wordTrace_append hprefix tailTrace_3584196
  have hstable : (prefixWord ++ tailWord_3584196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584196).length < 2 ^ (prefixWord ++ tailWord_3584196).sum := by decide
  have hdescent : baseEnd_3584196 < baseStart_3584196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584209 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 1, 7]
def baseStart_3584209 : Nat := 118140960795 + 3584209 * 2 ^ 59
def prefixEnd_3584209 : Nat := 4983230072969 + 3 ^ 40 * 3584209 * 2
def baseEnd_3584209 : Nat := 1226947988780581666336019

theorem tailTrace_3584209 : CollatzResearch.WordTrace tailWord_3584209 prefixEnd_3584209 1226947988780581666336019 := by
  unfold tailWord_3584209
  simp only [CollatzResearch.WordTrace]
  refine ⟨130726841872030402007819681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87151227914686934671879787 130726841872030402007819681)
  ·
    refine ⟨98045131404022801505864761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130726841872030402007819681 98045131404022801505864761)
    ·
      refine ⟨73533848553017101129398571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98045131404022801505864761 73533848553017101129398571)
      ·
        refine ⟨110300772829525651694097857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73533848553017101129398571 110300772829525651694097857)
        ·
          refine ⟨82725579622144238770573393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110300772829525651694097857 82725579622144238770573393)
          ·
            refine ⟨62044184716608179077930045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82725579622144238770573393 62044184716608179077930045)
            ·
              refine ⟨23266569268728067154223767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62044184716608179077930045 23266569268728067154223767)
              ·
                refine ⟨34899853903092100731335651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23266569268728067154223767 34899853903092100731335651)
                ·
                  refine ⟨52349780854638151097003477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34899853903092100731335651 52349780854638151097003477)
                  ·
                    refine ⟨1226947988780581666336019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52349780854638151097003477 1226947988780581666336019)
                    ·
                      rfl

theorem cell22_3584209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_3584209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584209 prefixEnd_3584209 := by exact prefixLift 3584209
  have htrace : WordTrace (prefixWord ++ tailWord_3584209) baseStart_3584209 baseEnd_3584209 := by
    simpa [prefixWord, tailWord_3584209, baseEnd_3584209] using wordTrace_append hprefix tailTrace_3584209
  have hstable : (prefixWord ++ tailWord_3584209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584209).length < 2 ^ (prefixWord ++ tailWord_3584209).sum := by decide
  have hdescent : baseEnd_3584209 < baseStart_3584209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584288 : List Nat := [2, 1, 1, 5, 2, 1, 1, 2, 4, 3]
def baseStart_3584288 : Nat := 118140960795 + 3584288 * 2 ^ 59
def prefixEnd_3584288 : Nat := 4983230072969 + 3 ^ 40 * 3584288 * 2
def baseEnd_3584288 : Nat := 1226975032095051793610777

theorem tailTrace_3584288 : CollatzResearch.WordTrace tailWord_3584288 prefixEnd_3584288 1226975032095051793610777 := by
  unfold tailWord_3584288
  simp only [CollatzResearch.WordTrace]
  refine ⟨65364861619372099249972759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87153148825829465666630345 65364861619372099249972759)
  ·
    refine ⟨98047292429058148874959139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65364861619372099249972759 98047292429058148874959139)
    ·
      refine ⟨147070938643587223312438709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98047292429058148874959139 147070938643587223312438709)
      ·
        refine ⟨13787900497836302185541129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147070938643587223312438709 13787900497836302185541129)
        ·
          refine ⟨10340925373377226639155847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13787900497836302185541129 10340925373377226639155847)
          ·
            refine ⟨15511388060065839958733771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10340925373377226639155847 15511388060065839958733771)
            ·
              refine ⟨23267082090098759938100657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15511388060065839958733771 23267082090098759938100657)
              ·
                refine ⟨17450311567574069953575493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23267082090098759938100657 17450311567574069953575493)
                ·
                  refine ⟨3271933418920138116295405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17450311567574069953575493 3271933418920138116295405)
                  ·
                    refine ⟨1226975032095051793610777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3271933418920138116295405 1226975032095051793610777)
                    ·
                      rfl

theorem cell22_3584288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 2, 4, 3].length) (baseStart_3584288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584288 prefixEnd_3584288 := by exact prefixLift 3584288
  have htrace : WordTrace (prefixWord ++ tailWord_3584288) baseStart_3584288 baseEnd_3584288 := by
    simpa [prefixWord, tailWord_3584288, baseEnd_3584288] using wordTrace_append hprefix tailTrace_3584288
  have hstable : (prefixWord ++ tailWord_3584288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584288).length < 2 ^ (prefixWord ++ tailWord_3584288).sum := by decide
  have hdescent : baseEnd_3584288 < baseStart_3584288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584290 : List Nat := [3, 3, 1, 1, 3, 1, 3, 3, 4]
def baseStart_3584290 : Nat := 118140960795 + 3584290 * 2 ^ 59
def prefixEnd_3584290 : Nat := 4983230072969 + 3 ^ 40 * 3584290 * 2
def baseEnd_3584290 : Nat := 408991905578641485020257

theorem tailTrace_3584290 : CollatzResearch.WordTrace tailWord_3584290 prefixEnd_3584290 408991905578641485020257 := by
  unfold tailWord_3584290
  simp only [CollatzResearch.WordTrace]
  refine ⟨32682449046184238210379581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87153197456491301894345549 32682449046184238210379581)
  ·
    refine ⟨12255918392319089328892343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32682449046184238210379581 12255918392319089328892343)
    ·
      refine ⟨18383877588478633993338515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12255918392319089328892343 18383877588478633993338515)
      ·
        refine ⟨27575816382717950990007773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18383877588478633993338515 27575816382717950990007773)
        ·
          refine ⟨10340931143519231621252915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27575816382717950990007773 10340931143519231621252915)
          ·
            refine ⟨15511396715278847431879373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10340931143519231621252915 15511396715278847431879373)
            ·
              refine ⟨5816773768229567786954765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15511396715278847431879373 5816773768229567786954765)
              ·
                refine ⟨2181290163086087920108037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5816773768229567786954765 2181290163086087920108037)
                ·
                  refine ⟨408991905578641485020257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181290163086087920108037 408991905578641485020257)
                  ·
                    rfl

theorem cell22_3584290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 3, 4].length) (baseStart_3584290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584290 prefixEnd_3584290 := by exact prefixLift 3584290
  have htrace : WordTrace (prefixWord ++ tailWord_3584290) baseStart_3584290 baseEnd_3584290 := by
    simpa [prefixWord, tailWord_3584290, baseEnd_3584290] using wordTrace_append hprefix tailTrace_3584290
  have hstable : (prefixWord ++ tailWord_3584290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584290).length < 2 ^ (prefixWord ++ tailWord_3584290).sum := by decide
  have hdescent : baseEnd_3584290 < baseStart_3584290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584318 : List Nat := [4, 2, 1, 2, 1, 3, 2, 7]
def baseStart_3584318 : Nat := 118140960795 + 3584318 * 2 ^ 59
def prefixEnd_3584318 : Nat := 4983230072969 + 3 ^ 40 * 3584318 * 2
def baseEnd_3584318 : Nat := 136331700189793523928965

theorem tailTrace_3584318 : CollatzResearch.WordTrace tailWord_3584318 prefixEnd_3584318 136331700189793523928965 := by
  unfold tailWord_3584318
  simp only [CollatzResearch.WordTrace]
  refine ⟨16341352178579439202942201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87153878285757009082358405 16341352178579439202942201)
  ·
    refine ⟨12256014133934579402206651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16341352178579439202942201 12256014133934579402206651)
    ·
      refine ⟨18384021200901869103309977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12256014133934579402206651 18384021200901869103309977)
      ·
        refine ⟨13788015900676401827482483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18384021200901869103309977 13788015900676401827482483)
        ·
          refine ⟨20682023851014602741223725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13788015900676401827482483 20682023851014602741223725)
          ·
            refine ⟨7755758944130476027958897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20682023851014602741223725 7755758944130476027958897)
            ·
              refine ⟨5816819208097857020969173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7755758944130476027958897 5816819208097857020969173)
              ·
                refine ⟨136331700189793523928965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5816819208097857020969173 136331700189793523928965)
                ·
                  rfl

theorem cell22_3584318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_3584318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584318 prefixEnd_3584318 := by exact prefixLift 3584318
  have htrace : WordTrace (prefixWord ++ tailWord_3584318) baseStart_3584318 baseEnd_3584318 := by
    simpa [prefixWord, tailWord_3584318, baseEnd_3584318] using wordTrace_append hprefix tailTrace_3584318
  have hstable : (prefixWord ++ tailWord_3584318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584318).length < 2 ^ (prefixWord ++ tailWord_3584318).sum := by decide
  have hdescent : baseEnd_3584318 < baseStart_3584318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584361 : List Nat := [1, 2, 1, 1, 1, 3, 4, 2, 2, 5]
def baseStart_3584361 : Nat := 118140960795 + 3584361 * 2 ^ 59
def prefixEnd_3584361 : Nat := 4983230072969 + 3 ^ 40 * 3584361 * 2
def baseEnd_3584361 : Nat := 1227000021486903936535553

theorem tailTrace_3584361 : CollatzResearch.WordTrace tailWord_3584361 prefixEnd_3584361 1227000021486903936535553 := by
  unfold tailWord_3584361
  simp only [CollatzResearch.WordTrace]
  refine ⟨130732385767479731967352937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87154923844986487978235291 130732385767479731967352937)
  ·
    refine ⟨98049289325609798975514703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130732385767479731967352937 98049289325609798975514703)
    ·
      refine ⟨147073933988414698463272055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98049289325609798975514703 147073933988414698463272055)
      ·
        refine ⟨220610900982622047694908083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147073933988414698463272055 220610900982622047694908083)
        ·
          refine ⟨330916351473933071542362125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220610900982622047694908083 330916351473933071542362125)
          ·
            refine ⟨124093631802724901828385797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 330916351473933071542362125 124093631802724901828385797)
            ·
              refine ⟨23267555963010919092822337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124093631802724901828385797 23267555963010919092822337)
              ·
                refine ⟨17450666972258189319616753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23267555963010919092822337 17450666972258189319616753)
                ·
                  refine ⟨13088000229193641989712565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17450666972258189319616753 13088000229193641989712565)
                  ·
                    refine ⟨1227000021486903936535553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13088000229193641989712565 1227000021486903936535553)
                    ·
                      rfl

theorem cell22_3584361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 2, 2, 5].length) (baseStart_3584361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584361 prefixEnd_3584361 := by exact prefixLift 3584361
  have htrace : WordTrace (prefixWord ++ tailWord_3584361) baseStart_3584361 baseEnd_3584361 := by
    simpa [prefixWord, tailWord_3584361, baseEnd_3584361] using wordTrace_append hprefix tailTrace_3584361
  have hstable : (prefixWord ++ tailWord_3584361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584361).length < 2 ^ (prefixWord ++ tailWord_3584361).sum := by decide
  have hdescent : baseEnd_3584361 < baseStart_3584361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584393 : List Nat := [1, 2, 1, 1, 6, 1, 2, 1, 3, 4]
def baseStart_3584393 : Nat := 118140960795 + 3584393 * 2 ^ 59
def prefixEnd_3584393 : Nat := 4983230072969 + 3 ^ 40 * 3584393 * 2
def baseEnd_3584393 : Nat := 1227010975740866519735455

theorem tailTrace_3584393 : CollatzResearch.WordTrace tailWord_3584393 prefixEnd_3584393 1227010975740866519735455 := by
  unfold tailWord_3584393
  simp only [CollatzResearch.WordTrace]
  refine ⟨130733552903363801432517833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87155701935575867621678555 130733552903363801432517833)
  ·
    refine ⟨98050164677522851074388375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130733552903363801432517833 98050164677522851074388375)
    ·
      refine ⟨147075247016284276611582563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98050164677522851074388375 147075247016284276611582563)
      ·
        refine ⟨220612870524426414917373845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147075247016284276611582563 220612870524426414917373845)
        ·
          refine ⟨10341228305832488199251899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 220612870524426414917373845 10341228305832488199251899)
          ·
            refine ⟨15511842458748732298877849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10341228305832488199251899 15511842458748732298877849)
            ·
              refine ⟨11633881844061549224158387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15511842458748732298877849 11633881844061549224158387)
              ·
                refine ⟨17450822766092323836237581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11633881844061549224158387 17450822766092323836237581)
                ·
                  refine ⟨6544058537284621438589093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17450822766092323836237581 6544058537284621438589093)
                  ·
                    refine ⟨1227010975740866519735455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6544058537284621438589093 1227010975740866519735455)
                    ·
                      rfl

theorem cell22_3584393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 4].length) (baseStart_3584393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584393 prefixEnd_3584393 := by exact prefixLift 3584393
  have htrace : WordTrace (prefixWord ++ tailWord_3584393) baseStart_3584393 baseEnd_3584393 := by
    simpa [prefixWord, tailWord_3584393, baseEnd_3584393] using wordTrace_append hprefix tailTrace_3584393
  have hstable : (prefixWord ++ tailWord_3584393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584393).length < 2 ^ (prefixWord ++ tailWord_3584393).sum := by decide
  have hdescent : baseEnd_3584393 < baseStart_3584393 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584410 : List Nat := [3, 1, 1, 4, 1, 3, 1, 3, 1, 4]
def baseStart_3584410 : Nat := 118140960795 + 3584410 * 2 ^ 59
def prefixEnd_3584410 : Nat := 4983230072969 + 3 ^ 40 * 3584410 * 2
def baseEnd_3584410 : Nat := 1227016795188284142060403

theorem tailTrace_3584410 : CollatzResearch.WordTrace tailWord_3584410 prefixEnd_3584410 1227016795188284142060403 := by
  unfold tailWord_3584410
  simp only [CollatzResearch.WordTrace]
  refine ⟨32683543236075553333971671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87156115296201475557257789 32683543236075553333971671)
  ·
    refine ⟨49025314854113330000957507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32683543236075553333971671 49025314854113330000957507)
    ·
      refine ⟨73537972281169995001436261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49025314854113330000957507 73537972281169995001436261)
      ·
        refine ⟨13788369802719374062769299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73537972281169995001436261 13788369802719374062769299)
        ·
          refine ⟨20682554704079061094153949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13788369802719374062769299 20682554704079061094153949)
          ·
            refine ⟨7755958014029647910307731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20682554704079061094153949 7755958014029647910307731)
            ·
              refine ⟨11633937021044471865461597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7755958014029647910307731 11633937021044471865461597)
              ·
                refine ⟨4362726382891676949548099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11633937021044471865461597 4362726382891676949548099)
                ·
                  refine ⟨6544089574337515424322149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4362726382891676949548099 6544089574337515424322149)
                  ·
                    refine ⟨1227016795188284142060403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6544089574337515424322149 1227016795188284142060403)
                    ·
                      rfl

theorem cell22_3584410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 1, 3, 1, 4].length) (baseStart_3584410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584410 prefixEnd_3584410 := by exact prefixLift 3584410
  have htrace : WordTrace (prefixWord ++ tailWord_3584410) baseStart_3584410 baseEnd_3584410 := by
    simpa [prefixWord, tailWord_3584410, baseEnd_3584410] using wordTrace_append hprefix tailTrace_3584410
  have hstable : (prefixWord ++ tailWord_3584410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584410).length < 2 ^ (prefixWord ++ tailWord_3584410).sum := by decide
  have hdescent : baseEnd_3584410 < baseStart_3584410 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584451 : List Nat := [1, 1, 1, 3, 1, 1, 3, 1, 1, 9]
def baseStart_3584451 : Nat := 118140960795 + 3584451 * 2 ^ 59
def prefixEnd_3584451 : Nat := 4983230072969 + 3 ^ 40 * 3584451 * 2
def baseEnd_3584451 : Nat := 1227030830326173701785277

theorem tailTrace_3584451 : CollatzResearch.WordTrace tailWord_3584451 prefixEnd_3584451 1227030830326173701785277 := by
  unfold tailWord_3584451
  simp only [CollatzResearch.WordTrace]
  refine ⟨130735668337153677338129207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87157112224769118225419471 130735668337153677338129207)
  ·
    refine ⟨196103502505730516007193811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130735668337153677338129207 196103502505730516007193811)
    ·
      refine ⟨294155253758595774010790717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196103502505730516007193811 294155253758595774010790717)
      ·
        refine ⟨110308220159473415254046519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294155253758595774010790717 110308220159473415254046519)
        ·
          refine ⟨165462330239210122881069779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110308220159473415254046519 165462330239210122881069779)
          ·
            refine ⟨248193495358815184321604669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165462330239210122881069779 248193495358815184321604669)
            ·
              refine ⟨93072560759555694120601751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248193495358815184321604669 93072560759555694120601751)
              ·
                refine ⟨139608841139333541180902627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93072560759555694120601751 139608841139333541180902627)
                ·
                  refine ⟨209413261709000311771353941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139608841139333541180902627 209413261709000311771353941)
                  ·
                    refine ⟨1227030830326173701785277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 209413261709000311771353941 1227030830326173701785277)
                    ·
                      rfl

theorem cell22_3584451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 1, 1, 9].length) (baseStart_3584451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584451 prefixEnd_3584451 := by exact prefixLift 3584451
  have htrace : WordTrace (prefixWord ++ tailWord_3584451) baseStart_3584451 baseEnd_3584451 := by
    simpa [prefixWord, tailWord_3584451, baseEnd_3584451] using wordTrace_append hprefix tailTrace_3584451
  have hstable : (prefixWord ++ tailWord_3584451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584451).length < 2 ^ (prefixWord ++ tailWord_3584451).sum := by decide
  have hdescent : baseEnd_3584451 < baseStart_3584451 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584532 : List Nat := [2, 4, 3, 1, 1, 1, 1, 4, 5]
def baseStart_3584532 : Nat := 118140960795 + 3584532 * 2 ^ 59
def prefixEnd_3584532 : Nat := 4983230072969 + 3 ^ 40 * 3584532 * 2
def baseEnd_3584532 : Nat := 409019519427172163503343

theorem tailTrace_3584532 : CollatzResearch.WordTrace tailWord_3584532 prefixEnd_3584532 409019519427172163503343 := by
  unfold tailWord_3584532
  simp only [CollatzResearch.WordTrace]
  refine ⟨65369311324930114085913925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87159081766573485447885233 65369311324930114085913925)
  ·
    refine ⟨12256745873424396391108861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65369311324930114085913925 12256745873424396391108861)
    ·
      refine ⟨4596279702534148646665823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12256745873424396391108861 4596279702534148646665823)
      ·
        refine ⟨6894419553801222969998735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4596279702534148646665823 6894419553801222969998735)
        ·
          refine ⟨10341629330701834454998103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6894419553801222969998735 10341629330701834454998103)
          ·
            refine ⟨15512443996052751682497155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10341629330701834454998103 15512443996052751682497155)
            ·
              refine ⟨23268665994079127523745733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15512443996052751682497155 23268665994079127523745733)
              ·
                refine ⟨4362874873889836410702325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23268665994079127523745733 4362874873889836410702325)
                ·
                  refine ⟨409019519427172163503343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4362874873889836410702325 409019519427172163503343)
                  ·
                    rfl

theorem cell22_3584532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 4, 5].length) (baseStart_3584532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584532 prefixEnd_3584532 := by exact prefixLift 3584532
  have htrace : WordTrace (prefixWord ++ tailWord_3584532) baseStart_3584532 baseEnd_3584532 := by
    simpa [prefixWord, tailWord_3584532, baseEnd_3584532] using wordTrace_append hprefix tailTrace_3584532
  have hstable : (prefixWord ++ tailWord_3584532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584532).length < 2 ^ (prefixWord ++ tailWord_3584532).sum := by decide
  have hdescent : baseEnd_3584532 < baseStart_3584532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584536 : List Nat := [2, 1, 2, 3, 3, 3, 2, 2, 1, 3]
def baseStart_3584536 : Nat := 118140960795 + 3584536 * 2 ^ 59
def prefixEnd_3584536 : Nat := 4983230072969 + 3 ^ 40 * 3584536 * 2
def baseEnd_3584536 : Nat := 1227059927563261813410017

theorem tailTrace_3584536 : CollatzResearch.WordTrace tailWord_3584536 prefixEnd_3584536 1227059927563261813410017 := by
  unfold tailWord_3584536
  simp only [CollatzResearch.WordTrace]
  refine ⟨65369384270922868427486731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87159179027897157903315641 65369384270922868427486731)
  ·
    refine ⟨98054076406384302641230097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65369384270922868427486731 98054076406384302641230097)
    ·
      refine ⟨73540557304788226980922573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98054076406384302641230097 73540557304788226980922573)
      ·
        refine ⟨27577708989295585117845965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73540557304788226980922573 27577708989295585117845965)
        ·
          refine ⟨10341640870985844419192237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27577708989295585117845965 10341640870985844419192237)
          ·
            refine ⟨3878115326619691657197089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10341640870985844419192237 3878115326619691657197089)
            ·
              refine ⟨2908586494964768742897817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3878115326619691657197089 2908586494964768742897817)
              ·
                refine ⟨2181439871223576557173363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908586494964768742897817 2181439871223576557173363)
                ·
                  refine ⟨3272159806835364835760045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181439871223576557173363 3272159806835364835760045)
                  ·
                    refine ⟨1227059927563261813410017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3272159806835364835760045 1227059927563261813410017)
                    ·
                      rfl

theorem cell22_3584536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_3584536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584536 prefixEnd_3584536 := by exact prefixLift 3584536
  have htrace : WordTrace (prefixWord ++ tailWord_3584536) baseStart_3584536 baseEnd_3584536 := by
    simpa [prefixWord, tailWord_3584536, baseEnd_3584536] using wordTrace_append hprefix tailTrace_3584536
  have hstable : (prefixWord ++ tailWord_3584536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584536).length < 2 ^ (prefixWord ++ tailWord_3584536).sum := by decide
  have hdescent : baseEnd_3584536 < baseStart_3584536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584543 : List Nat := [1, 1, 2, 4, 1, 1, 1, 5, 6]
def baseStart_3584543 : Nat := 118140960795 + 3584543 * 2 ^ 59
def prefixEnd_3584543 : Nat := 4983230072969 + 3 ^ 40 * 3584543 * 2
def baseEnd_3584543 : Nat := 409020774602105376161665

theorem tailTrace_3584543 : CollatzResearch.WordTrace tailWord_3584543 prefixEnd_3584543 409020774602105376161665 := by
  unfold tailWord_3584543
  simp only [CollatzResearch.WordTrace]
  refine ⟨130739023852820377050478283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87159349235213584700318855 130739023852820377050478283)
  ·
    refine ⟨196108535779230565575717425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130739023852820377050478283 196108535779230565575717425)
    ·
      refine ⟨147081401834422924181788069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196108535779230565575717425 147081401834422924181788069)
      ·
        refine ⟨27577762843954298284085263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147081401834422924181788069 27577762843954298284085263)
        ·
          refine ⟨41366644265931447426127895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27577762843954298284085263 41366644265931447426127895)
          ·
            refine ⟨62049966398897171139191843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41366644265931447426127895 62049966398897171139191843)
            ·
              refine ⟨93074949598345756708787765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62049966398897171139191843 93074949598345756708787765)
              ·
                refine ⟨8725776524844914691448853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93074949598345756708787765 8725776524844914691448853)
                ·
                  refine ⟨409020774602105376161665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8725776524844914691448853 409020774602105376161665)
                  ·
                    rfl

theorem cell22_3584543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 5, 6].length) (baseStart_3584543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584543 prefixEnd_3584543 := by exact prefixLift 3584543
  have htrace : WordTrace (prefixWord ++ tailWord_3584543) baseStart_3584543 baseEnd_3584543 := by
    simpa [prefixWord, tailWord_3584543, baseEnd_3584543] using wordTrace_append hprefix tailTrace_3584543
  have hstable : (prefixWord ++ tailWord_3584543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584543).length < 2 ^ (prefixWord ++ tailWord_3584543).sum := by decide
  have hdescent : baseEnd_3584543 < baseStart_3584543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584575 : List Nat := [1, 1, 2, 2, 3, 2, 2, 2, 4, 3]
def baseStart_3584575 : Nat := 118140960795 + 3584575 * 2 ^ 59
def prefixEnd_3584575 : Nat := 4983230072969 + 3 ^ 40 * 3584575 * 2
def baseEnd_3584575 : Nat := 1227073278060278711684897

theorem tailTrace_3584575 : CollatzResearch.WordTrace tailWord_3584575 prefixEnd_3584575 1227073278060278711684897 := by
  unfold tailWord_3584575
  simp only [CollatzResearch.WordTrace]
  refine ⟨130740190988704446515643179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87160127325802964343762119 130740190988704446515643179)
  ·
    refine ⟨196110286483056669773464769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130740190988704446515643179 196110286483056669773464769)
    ·
      refine ⟨147082714862292502330098577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196110286483056669773464769 147082714862292502330098577)
      ·
        refine ⟨110312036146719376747573933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147082714862292502330098577 110312036146719376747573933)
        ·
          refine ⟨41367013555019766280340225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110312036146719376747573933 41367013555019766280340225)
          ·
            refine ⟨31025260166264824710255169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41367013555019766280340225 31025260166264824710255169)
            ·
              refine ⟨23268945124698618532691377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31025260166264824710255169 23268945124698618532691377)
              ·
                refine ⟨17451708843523963899518533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23268945124698618532691377 17451708843523963899518533)
                ·
                  refine ⟨3272195408160743231159725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 17451708843523963899518533 3272195408160743231159725)
                  ·
                    refine ⟨1227073278060278711684897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3272195408160743231159725 1227073278060278711684897)
                    ·
                      rfl

theorem cell22_3584575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 2, 4, 3].length) (baseStart_3584575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584575 prefixEnd_3584575 := by exact prefixLift 3584575
  have htrace : WordTrace (prefixWord ++ tailWord_3584575) baseStart_3584575 baseEnd_3584575 := by
    simpa [prefixWord, tailWord_3584575, baseEnd_3584575] using wordTrace_append hprefix tailTrace_3584575
  have hstable : (prefixWord ++ tailWord_3584575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584575).length < 2 ^ (prefixWord ++ tailWord_3584575).sum := by decide
  have hdescent : baseEnd_3584575 < baseStart_3584575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584577 : List Nat := [1, 2, 5, 1, 1, 2, 1, 5, 4]
def baseStart_3584577 : Nat := 118140960795 + 3584577 * 2 ^ 59
def prefixEnd_3584577 : Nat := 4983230072969 + 3 ^ 40 * 3584577 * 2
def baseEnd_3584577 : Nat := 409024654233717124378297

theorem tailTrace_3584577 : CollatzResearch.WordTrace tailWord_3584577 prefixEnd_3584577 409024654233717124378297 := by
  unfold tailWord_3584577
  simp only [CollatzResearch.WordTrace]
  refine ⟨130740263934697200857215985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87160175956464800571477323 130740263934697200857215985)
  ·
    refine ⟨98055197951022900642911989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130740263934697200857215985 98055197951022900642911989)
    ·
      refine ⟨9192674807908396935272999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98055197951022900642911989 9192674807908396935272999)
      ·
        refine ⟨13789012211862595402909499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9192674807908396935272999 13789012211862595402909499)
        ·
          refine ⟨20683518317793893104364249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13789012211862595402909499 20683518317793893104364249)
          ·
            refine ⟨15512638738345419828273187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20683518317793893104364249 15512638738345419828273187)
            ·
              refine ⟨23268958107518129742409781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15512638738345419828273187 23268958107518129742409781)
              ·
                refine ⟨2181464822579824663350917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23268958107518129742409781 2181464822579824663350917)
                ·
                  refine ⟨409024654233717124378297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181464822579824663350917 409024654233717124378297)
                  ·
                    rfl

theorem cell22_3584577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 5, 4].length) (baseStart_3584577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584577 prefixEnd_3584577 := by exact prefixLift 3584577
  have htrace : WordTrace (prefixWord ++ tailWord_3584577) baseStart_3584577 baseEnd_3584577 := by
    simpa [prefixWord, tailWord_3584577, baseEnd_3584577] using wordTrace_append hprefix tailTrace_3584577
  have hstable : (prefixWord ++ tailWord_3584577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584577).length < 2 ^ (prefixWord ++ tailWord_3584577).sum := by decide
  have hdescent : baseEnd_3584577 < baseStart_3584577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584588 : List Nat := [2, 2, 1, 3, 1, 2, 11]
def baseStart_3584588 : Nat := 118140960795 + 3584588 * 2 ^ 59
def prefixEnd_3584588 : Nat := 4983230072969 + 3 ^ 40 * 3584588 * 2
def baseEnd_3584588 : Nat := 45447323267627815226291

theorem tailTrace_3584588 : CollatzResearch.WordTrace tailWord_3584588 prefixEnd_3584588 45447323267627815226291 := by
  unfold tailWord_3584588
  simp only [CollatzResearch.WordTrace]
  refine ⟨65370332568828674867933209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87160443425104899823910945 65370332568828674867933209)
  ·
    refine ⟨49027749426621506150949907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65370332568828674867933209 49027749426621506150949907)
    ·
      refine ⟨73541624139932259226424861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49027749426621506150949907 73541624139932259226424861)
      ·
        refine ⟨27578109052474597209909323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73541624139932259226424861 27578109052474597209909323)
        ·
          refine ⟨41367163578711895814863985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27578109052474597209909323 41367163578711895814863985)
          ·
            refine ⟨31025372684033921861147989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41367163578711895814863985 31025372684033921861147989)
            ·
              refine ⟨45447323267627815226291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 31025372684033921861147989 45447323267627815226291)
              ·
                rfl

theorem cell22_3584588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 11].length) (baseStart_3584588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584588 prefixEnd_3584588 := by exact prefixLift 3584588
  have htrace : WordTrace (prefixWord ++ tailWord_3584588) baseStart_3584588 baseEnd_3584588 := by
    simpa [prefixWord, tailWord_3584588, baseEnd_3584588] using wordTrace_append hprefix tailTrace_3584588
  have hstable : (prefixWord ++ tailWord_3584588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584588).length < 2 ^ (prefixWord ++ tailWord_3584588).sum := by decide
  have hdescent : baseEnd_3584588 < baseStart_3584588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584590 : List Nat := [4, 1, 1, 1, 1, 2, 2, 4, 2, 4]
def baseStart_3584590 : Nat := 118140960795 + 3584590 * 2 ^ 59
def prefixEnd_3584590 : Nat := 4983230072969 + 3 ^ 40 * 3584590 * 2
def baseEnd_3584590 : Nat := 1227078412866823672559851

theorem tailTrace_3584590 : CollatzResearch.WordTrace tailWord_3584590 prefixEnd_3584590 1227078412866823672559851 := by
  unfold tailWord_3584590
  simp only [CollatzResearch.WordTrace]
  refine ⟨16342592260456263009679903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87160492055766736051626149 16342592260456263009679903)
  ·
    refine ⟨24513888390684394514519855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16342592260456263009679903 24513888390684394514519855)
    ·
      refine ⟨36770832586026591771779783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24513888390684394514519855 36770832586026591771779783)
      ·
        refine ⟨55156248879039887657669675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36770832586026591771779783 55156248879039887657669675)
        ·
          refine ⟨82734373318559831486504513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55156248879039887657669675 82734373318559831486504513)
          ·
            refine ⟨62050779988919873614878385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82734373318559831486504513 62050779988919873614878385)
            ·
              refine ⟨46538084991689905211158789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62050779988919873614878385 46538084991689905211158789)
              ·
                refine ⟨8725890935941857227092273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46538084991689905211158789 8725890935941857227092273)
                ·
                  refine ⟨6544418201956392920319205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8725890935941857227092273 6544418201956392920319205)
                  ·
                    refine ⟨1227078412866823672559851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6544418201956392920319205 1227078412866823672559851)
                    ·
                      rfl

theorem cell22_3584590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_3584590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584590 prefixEnd_3584590 := by exact prefixLift 3584590
  have htrace : WordTrace (prefixWord ++ tailWord_3584590) baseStart_3584590 baseEnd_3584590 := by
    simpa [prefixWord, tailWord_3584590, baseEnd_3584590] using wordTrace_append hprefix tailTrace_3584590
  have hstable : (prefixWord ++ tailWord_3584590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584590).length < 2 ^ (prefixWord ++ tailWord_3584590).sum := by decide
  have hdescent : baseEnd_3584590 < baseStart_3584590 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584609 : List Nat := [1, 2, 3, 1, 1, 5, 3, 1, 2, 3]
def baseStart_3584609 : Nat := 118140960795 + 3584609 * 2 ^ 59
def prefixEnd_3584609 : Nat := 4983230072969 + 3 ^ 40 * 3584609 * 2
def baseEnd_3584609 : Nat := 1227084916955113956334793

theorem tailTrace_3584609 : CollatzResearch.WordTrace tailWord_3584609 prefixEnd_3584609 1227084916955113956334793 := by
  unfold tailWord_3584609
  simp only [CollatzResearch.WordTrace]
  refine ⟨130741431070581270322380881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87160954047054180214920587 130741431070581270322380881)
  ·
    refine ⟨98056073302935952741785661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130741431070581270322380881 98056073302935952741785661)
    ·
      refine ⟨36771027488600982278169623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98056073302935952741785661 36771027488600982278169623)
      ·
        refine ⟨55156541232901473417254435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36771027488600982278169623 55156541232901473417254435)
        ·
          refine ⟨82734811849352210125881653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55156541232901473417254435 82734811849352210125881653)
          ·
            refine ⟨7756388610876769699301405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82734811849352210125881653 7756388610876769699301405)
            ·
              refine ⟨2908645729078788637238027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7756388610876769699301405 2908645729078788637238027)
              ·
                refine ⟨4362968593618182955857041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2908645729078788637238027 4362968593618182955857041)
                ·
                  refine ⟨3272226445213637216892781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4362968593618182955857041 3272226445213637216892781)
                  ·
                    refine ⟨1227084916955113956334793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3272226445213637216892781 1227084916955113956334793)
                    ·
                      rfl

theorem cell22_3584609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 3, 1, 2, 3].length) (baseStart_3584609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584609 prefixEnd_3584609 := by exact prefixLift 3584609
  have htrace : WordTrace (prefixWord ++ tailWord_3584609) baseStart_3584609 baseEnd_3584609 := by
    simpa [prefixWord, tailWord_3584609, baseEnd_3584609] using wordTrace_append hprefix tailTrace_3584609
  have hstable : (prefixWord ++ tailWord_3584609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584609).length < 2 ^ (prefixWord ++ tailWord_3584609).sum := by decide
  have hdescent : baseEnd_3584609 < baseStart_3584609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584622 : List Nat := [4, 1, 2, 2, 2, 1, 4, 6]
def baseStart_3584622 : Nat := 118140960795 + 3584622 * 2 ^ 59
def prefixEnd_3584622 : Nat := 4983230072969 + 3 ^ 40 * 3584622 * 2
def baseEnd_3584622 : Nat := 136343263013420695084417

theorem tailTrace_3584622 : CollatzResearch.WordTrace tailWord_3584622 prefixEnd_3584622 136343263013420695084417 := by
  unfold tailWord_3584622
  simp only [CollatzResearch.WordTrace]
  refine ⟨16342738152441771692825515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87161270146356115695069413 16342738152441771692825515)
  ·
    refine ⟨24514107228662657539238273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16342738152441771692825515 24514107228662657539238273)
    ·
      refine ⟨18385580421496993154428705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24514107228662657539238273 18385580421496993154428705)
      ·
        refine ⟨13789185316122744865821529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18385580421496993154428705 13789185316122744865821529)
        ·
          refine ⟨10341888987092058649366147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13789185316122744865821529 10341888987092058649366147)
          ·
            refine ⟨15512833480638087974049221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10341888987092058649366147 15512833480638087974049221)
            ·
              refine ⟨2908656277619641495134229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15512833480638087974049221 2908656277619641495134229)
              ·
                refine ⟨136343263013420695084417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2908656277619641495134229 136343263013420695084417)
                ·
                  rfl

theorem cell22_3584622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 4, 6].length) (baseStart_3584622 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584622 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584622 prefixEnd_3584622 := by exact prefixLift 3584622
  have htrace : WordTrace (prefixWord ++ tailWord_3584622) baseStart_3584622 baseEnd_3584622 := by
    simpa [prefixWord, tailWord_3584622, baseEnd_3584622] using wordTrace_append hprefix tailTrace_3584622
  have hstable : (prefixWord ++ tailWord_3584622).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584622).length < 2 ^ (prefixWord ++ tailWord_3584622).sum := by decide
  have hdescent : baseEnd_3584622 < baseStart_3584622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584727 : List Nat := [1, 1, 3, 2, 1, 5, 2, 1, 1, 5]
def baseStart_3584727 : Nat := 118140960795 + 3584727 * 2 ^ 59
def prefixEnd_3584727 : Nat := 4983230072969 + 3 ^ 40 * 3584727 * 2
def baseEnd_3584727 : Nat := 1227125310766600981884431

theorem tailTrace_3584727 : CollatzResearch.WordTrace tailWord_3584727 prefixEnd_3584727 1227125310766600981884431 := by
  unfold tailWord_3584727
  simp only [CollatzResearch.WordTrace]
  refine ⟨130745734884153776475176435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87163823256102517650117623 130745734884153776475176435)
  ·
    refine ⟨196118602326230664712764653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130745734884153776475176435 196118602326230664712764653)
    ·
      refine ⟨73544475872336499267286745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196118602326230664712764653 73544475872336499267286745)
      ·
        refine ⟨55158356904252374450465059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73544475872336499267286745 55158356904252374450465059)
        ·
          refine ⟨82737535356378561675697589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55158356904252374450465059 82737535356378561675697589)
          ·
            refine ⟨7756643939660490157096649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82737535356378561675697589 7756643939660490157096649)
            ·
              refine ⟨5817482954745367617822487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7756643939660490157096649 5817482954745367617822487)
              ·
                refine ⟨8726224432118051426733731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5817482954745367617822487 8726224432118051426733731)
                ·
                  refine ⟨13089336648177077140100597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8726224432118051426733731 13089336648177077140100597)
                  ·
                    refine ⟨1227125310766600981884431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13089336648177077140100597 1227125310766600981884431)
                    ·
                      rfl

theorem cell22_3584727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 5].length) (baseStart_3584727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584727 prefixEnd_3584727 := by exact prefixLift 3584727
  have htrace : WordTrace (prefixWord ++ tailWord_3584727) baseStart_3584727 baseEnd_3584727 := by
    simpa [prefixWord, tailWord_3584727, baseEnd_3584727] using wordTrace_append hprefix tailTrace_3584727
  have hstable : (prefixWord ++ tailWord_3584727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584727).length < 2 ^ (prefixWord ++ tailWord_3584727).sum := by decide
  have hdescent : baseEnd_3584727 < baseStart_3584727 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584791 : List Nat := [1, 1, 3, 4, 4, 1, 2, 6]
def baseStart_3584791 : Nat := 118140960795 + 3584791 * 2 ^ 59
def prefixEnd_3584791 : Nat := 4983230072969 + 3 ^ 40 * 3584791 * 2
def baseEnd_3584791 : Nat := 136349691030502905364915

theorem tailTrace_3584791 : CollatzResearch.WordTrace tailWord_3584791 prefixEnd_3584791 136349691030502905364915 := by
  unfold tailWord_3584791
  simp only [CollatzResearch.WordTrace]
  refine ⟨130748069155921915405506227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87165379437281276937004151 130748069155921915405506227)
  ·
    refine ⟨196122103733882873108259341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130748069155921915405506227 196122103733882873108259341)
    ·
      refine ⟨73545788900206077415597253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196122103733882873108259341 73545788900206077415597253)
      ·
        refine ⟨13789835418788639515424485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73545788900206077415597253 13789835418788639515424485)
        ·
          refine ⟨2585594141022869909142091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13789835418788639515424485 2585594141022869909142091)
          ·
            refine ⟨3878391211534304863713137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585594141022869909142091 3878391211534304863713137)
            ·
              refine ⟨2908793408650728647784853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3878391211534304863713137 2908793408650728647784853)
              ·
                refine ⟨136349691030502905364915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2908793408650728647784853 136349691030502905364915)
                ·
                  rfl

theorem cell22_3584791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 2, 6].length) (baseStart_3584791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584791 prefixEnd_3584791 := by exact prefixLift 3584791
  have htrace : WordTrace (prefixWord ++ tailWord_3584791) baseStart_3584791 baseEnd_3584791 := by
    simpa [prefixWord, tailWord_3584791, baseEnd_3584791] using wordTrace_append hprefix tailTrace_3584791
  have hstable : (prefixWord ++ tailWord_3584791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584791).length < 2 ^ (prefixWord ++ tailWord_3584791).sum := by decide
  have hdescent : baseEnd_3584791 < baseStart_3584791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584802 : List Nat := [3, 3, 1, 1, 2, 2, 1, 2, 7]
def baseStart_3584802 : Nat := 118140960795 + 3584802 * 2 ^ 59
def prefixEnd_3584802 : Nat := 4983230072969 + 3 ^ 40 * 3584802 * 2
def baseEnd_3584802 : Nat := 409050328266441928753067

theorem tailTrace_3584802 : CollatzResearch.WordTrace tailWord_3584802 prefixEnd_3584802 409050328266441928753067 := by
  unfold tailWord_3584802
  simp only [CollatzResearch.WordTrace]
  refine ⟨32687117589720516071039165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87165646905921376189437773 32687117589720516071039165)
  ·
    refine ⟨12257669096145193526639687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32687117589720516071039165 12257669096145193526639687)
    ·
      refine ⟨18386503644217790289959531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12257669096145193526639687 18386503644217790289959531)
      ·
        refine ⟨27579755466326685434939297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18386503644217790289959531 27579755466326685434939297)
        ·
          refine ⟨20684816599745014076204473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27579755466326685434939297 20684816599745014076204473)
          ·
            refine ⟨15513612449808760557153355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20684816599745014076204473 15513612449808760557153355)
            ·
              refine ⟨23270418674713140835730033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15513612449808760557153355 23270418674713140835730033)
              ·
                refine ⟨17452814006034855626797525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23270418674713140835730033 17452814006034855626797525)
                ·
                  refine ⟨409050328266441928753067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17452814006034855626797525 409050328266441928753067)
                  ·
                    rfl

theorem cell22_3584802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 2, 7].length) (baseStart_3584802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584802 prefixEnd_3584802 := by exact prefixLift 3584802
  have htrace : WordTrace (prefixWord ++ tailWord_3584802) baseStart_3584802 baseEnd_3584802 := by
    simpa [prefixWord, tailWord_3584802, baseEnd_3584802] using wordTrace_append hprefix tailTrace_3584802
  have hstable : (prefixWord ++ tailWord_3584802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584802).length < 2 ^ (prefixWord ++ tailWord_3584802).sum := by decide
  have hdescent : baseEnd_3584802 < baseStart_3584802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584849 : List Nat := [1, 2, 2, 1, 6, 1, 1, 1, 3, 4]
def baseStart_3584849 : Nat := 118140960795 + 3584849 * 2 ^ 59
def prefixEnd_3584849 : Nat := 4983230072969 + 3 ^ 40 * 3584849 * 2
def baseEnd_3584849 : Nat := 1227167073859833330334057

theorem tailTrace_3584849 : CollatzResearch.WordTrace tailWord_3584849 prefixEnd_3584849 1227167073859833330334057 := by
  unfold tailWord_3584849
  simp only [CollatzResearch.WordTrace]
  refine ⟨130750184589711791311117601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87166789726474527540745067 130750184589711791311117601)
  ·
    refine ⟨98062638442283843483338201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130750184589711791311117601 98062638442283843483338201)
    ·
      refine ⟨73546978831712882612503651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98062638442283843483338201 73546978831712882612503651)
      ·
        refine ⟨110320468247569323918755477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73546978831712882612503651 110320468247569323918755477)
        ·
          refine ⟨5171271949104812058691663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110320468247569323918755477 5171271949104812058691663)
          ·
            refine ⟨7756907923657218088037495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5171271949104812058691663 7756907923657218088037495)
            ·
              refine ⟨11635361885485827132056243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7756907923657218088037495 11635361885485827132056243)
              ·
                refine ⟨17453042828228740698084365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11635361885485827132056243 17453042828228740698084365)
                ·
                  refine ⟨6544891060585777761781637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17453042828228740698084365 6544891060585777761781637)
                  ·
                    refine ⟨1227167073859833330334057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6544891060585777761781637 1227167073859833330334057)
                    ·
                      rfl

theorem cell22_3584849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_3584849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584849 prefixEnd_3584849 := by exact prefixLift 3584849
  have htrace : WordTrace (prefixWord ++ tailWord_3584849) baseStart_3584849 baseEnd_3584849 := by
    simpa [prefixWord, tailWord_3584849, baseEnd_3584849] using wordTrace_append hprefix tailTrace_3584849
  have hstable : (prefixWord ++ tailWord_3584849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584849).length < 2 ^ (prefixWord ++ tailWord_3584849).sum := by decide
  have hdescent : baseEnd_3584849 < baseStart_3584849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584864 : List Nat := [2, 1, 1, 3, 3, 1, 2, 5, 4]
def baseStart_3584864 : Nat := 118140960795 + 3584864 * 2 ^ 59
def prefixEnd_3584864 : Nat := 4983230072969 + 3 ^ 40 * 3584864 * 2
def baseEnd_3584864 : Nat := 409057402888792763736337

theorem tailTrace_3584864 : CollatzResearch.WordTrace tailWord_3584864 prefixEnd_3584864 409057402888792763736337 := by
  unfold tailWord_3584864
  simp only [CollatzResearch.WordTrace]
  refine ⟨65375365842328724436456823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87167154456438299248609097 65375365842328724436456823)
  ·
    refine ⟨98063048763493086654685235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65375365842328724436456823 98063048763493086654685235)
    ·
      refine ⟨147094573145239629982027853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98063048763493086654685235 147094573145239629982027853)
      ·
        refine ⟨55160464929464861243260445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147094573145239629982027853 55160464929464861243260445)
        ·
          refine ⟨20685174348549322966222667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55160464929464861243260445 20685174348549322966222667)
          ·
            refine ⟨31027761522823984449334001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20685174348549322966222667 31027761522823984449334001)
            ·
              refine ⟨23270821142117988337000501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31027761522823984449334001 23270821142117988337000501)
              ·
                refine ⟨2181639482073561406593797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23270821142117988337000501 2181639482073561406593797)
                ·
                  refine ⟨409057402888792763736337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181639482073561406593797 409057402888792763736337)
                  ·
                    rfl

theorem cell22_3584864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 5, 4].length) (baseStart_3584864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584864 prefixEnd_3584864 := by exact prefixLift 3584864
  have htrace : WordTrace (prefixWord ++ tailWord_3584864) baseStart_3584864 baseEnd_3584864 := by
    simpa [prefixWord, tailWord_3584864, baseEnd_3584864] using wordTrace_append hprefix tailTrace_3584864
  have hstable : (prefixWord ++ tailWord_3584864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584864).length < 2 ^ (prefixWord ++ tailWord_3584864).sum := by decide
  have hdescent : baseEnd_3584864 < baseStart_3584864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584877 : List Nat := [1, 5, 1, 1, 1, 1, 1, 2, 3, 6]
def baseStart_3584877 : Nat := 118140960795 + 3584877 * 2 ^ 59
def prefixEnd_3584877 : Nat := 4983230072969 + 3 ^ 40 * 3584877 * 2
def baseEnd_3584877 : Nat := 1227176658832050590633971

theorem tailTrace_3584877 : CollatzResearch.WordTrace tailWord_3584877 prefixEnd_3584877 1227176658832050590633971 := by
  unfold tailWord_3584877
  simp only [CollatzResearch.WordTrace]
  refine ⟨130751205833610352093136885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87167470555740234728757923 130751205833610352093136885)
  ·
    refine ⟨12257925546900970508731583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130751205833610352093136885 12257925546900970508731583)
    ·
      refine ⟨18386888320351455763097375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12257925546900970508731583 18386888320351455763097375)
      ·
        refine ⟨27580332480527183644646063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18386888320351455763097375 27580332480527183644646063)
        ·
          refine ⟨41370498720790775466969095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27580332480527183644646063 41370498720790775466969095)
          ·
            refine ⟨62055748081186163200453643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41370498720790775466969095 62055748081186163200453643)
            ·
              refine ⟨93083622121779244800680465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62055748081186163200453643 93083622121779244800680465)
              ·
                refine ⟨69812716591334433600510349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93083622121779244800680465 69812716591334433600510349)
                ·
                  refine ⟨26179768721750412600191381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69812716591334433600510349 26179768721750412600191381)
                  ·
                    refine ⟨1227176658832050590633971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26179768721750412600191381 1227176658832050590633971)
                    ·
                      rfl

theorem cell22_3584877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_3584877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584877 prefixEnd_3584877 := by exact prefixLift 3584877
  have htrace : WordTrace (prefixWord ++ tailWord_3584877) baseStart_3584877 baseEnd_3584877 := by
    simpa [prefixWord, tailWord_3584877, baseEnd_3584877] using wordTrace_append hprefix tailTrace_3584877
  have hstable : (prefixWord ++ tailWord_3584877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584877).length < 2 ^ (prefixWord ++ tailWord_3584877).sum := by decide
  have hdescent : baseEnd_3584877 < baseStart_3584877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584881 : List Nat := [1, 2, 2, 2, 1, 4, 4, 2, 4]
def baseStart_3584881 : Nat := 118140960795 + 3584881 * 2 ^ 59
def prefixEnd_3584881 : Nat := 4983230072969 + 3 ^ 40 * 3584881 * 2
def baseEnd_3584881 : Nat := 409059342704598637844653

theorem tailTrace_3584881 : CollatzResearch.WordTrace tailWord_3584881 prefixEnd_3584881 409059342704598637844653 := by
  unfold tailWord_3584881
  simp only [CollatzResearch.WordTrace]
  refine ⟨130751351725595860776282497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87167567817063907184188331 130751351725595860776282497)
  ·
    refine ⟨98063513794196895582211873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130751351725595860776282497 98063513794196895582211873)
    ·
      refine ⟨73547635345647671686658905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98063513794196895582211873 73547635345647671686658905)
      ·
        refine ⟨55160726509235753764994179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73547635345647671686658905 55160726509235753764994179)
        ·
          refine ⟨82741089763853630647491269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55160726509235753764994179 82741089763853630647491269)
          ·
            refine ⟨15513954330722555746404613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82741089763853630647491269 15513954330722555746404613)
            ·
              refine ⟨2908866437010479202450865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 15513954330722555746404613 2908866437010479202450865)
              ·
                refine ⟨2181649827757859401838149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2908866437010479202450865 2181649827757859401838149)
                ·
                  refine ⟨409059342704598637844653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181649827757859401838149 409059342704598637844653)
                  ·
                    rfl

theorem cell22_3584881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 2, 4].length) (baseStart_3584881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584881 prefixEnd_3584881 := by exact prefixLift 3584881
  have htrace : WordTrace (prefixWord ++ tailWord_3584881) baseStart_3584881 baseEnd_3584881 := by
    simpa [prefixWord, tailWord_3584881, baseEnd_3584881] using wordTrace_append hprefix tailTrace_3584881
  have hstable : (prefixWord ++ tailWord_3584881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584881).length < 2 ^ (prefixWord ++ tailWord_3584881).sum := by decide
  have hdescent : baseEnd_3584881 < baseStart_3584881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584898 : List Nat := [3, 4, 2, 2, 1, 1, 1, 2, 6]
def baseStart_3584898 : Nat := 118140960795 + 3584898 * 2 ^ 59
def prefixEnd_3584898 : Nat := 4983230072969 + 3 ^ 40 * 3584898 * 2
def baseEnd_3584898 : Nat := 409061282520404511952969

theorem tailTrace_3584898 : CollatzResearch.WordTrace tailWord_3584898 prefixEnd_3584898 409061282520404511952969 := by
  unfold tailWord_3584898
  simp only [CollatzResearch.WordTrace]
  refine ⟨32687992941633568169912837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87167981177689515119767565 32687992941633568169912837)
  ·
    refine ⟨6128998676556294031858657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 32687992941633568169912837 6128998676556294031858657)
    ·
      refine ⟨4596749007417220523893993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6128998676556294031858657 4596749007417220523893993)
      ·
        refine ⟨3447561755562915392920495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4596749007417220523893993 3447561755562915392920495)
        ·
          refine ⟨5171342633344373089380743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3447561755562915392920495 5171342633344373089380743)
          ·
            refine ⟨7757013950016559634071115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5171342633344373089380743 7757013950016559634071115)
            ·
              refine ⟨11635520925024839451106673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7757013950016559634071115 11635520925024839451106673)
              ·
                refine ⟨8726640693768629588330005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11635520925024839451106673 8726640693768629588330005)
                ·
                  refine ⟨409061282520404511952969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8726640693768629588330005 409061282520404511952969)
                  ·
                    rfl

theorem cell22_3584898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_3584898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584898 prefixEnd_3584898 := by exact prefixLift 3584898
  have htrace : WordTrace (prefixWord ++ tailWord_3584898) baseStart_3584898 baseEnd_3584898 := by
    simpa [prefixWord, tailWord_3584898, baseEnd_3584898] using wordTrace_append hprefix tailTrace_3584898
  have hstable : (prefixWord ++ tailWord_3584898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584898).length < 2 ^ (prefixWord ++ tailWord_3584898).sum := by decide
  have hdescent : baseEnd_3584898 < baseStart_3584898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584937 : List Nat := [1, 2, 1, 1, 1, 1, 7, 1, 7]
def baseStart_3584937 : Nat := 118140960795 + 3584937 * 2 ^ 59
def prefixEnd_3584937 : Nat := 4983230072969 + 3 ^ 40 * 3584937 * 2
def baseEnd_3584937 : Nat := 409065732686076811377929

theorem tailTrace_3584937 : CollatzResearch.WordTrace tailWord_3584937 prefixEnd_3584937 409065732686076811377929 := by
  unfold tailWord_3584937
  simp only [CollatzResearch.WordTrace]
  refine ⟨130753394213392982340321065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87168929475595321560214043 130753394213392982340321065)
  ·
    refine ⟨98065045660044736755240799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130753394213392982340321065 98065045660044736755240799)
    ·
      refine ⟨147097568490067105132861199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98065045660044736755240799 147097568490067105132861199)
      ·
        refine ⟨220646352735100657699291799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147097568490067105132861199 220646352735100657699291799)
        ·
          refine ⟨330969529102650986548937699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220646352735100657699291799 330969529102650986548937699)
          ·
            refine ⟨496454293653976479823406549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 330969529102650986548937699 496454293653976479823406549)
            ·
              refine ⟨11635647507515073745861091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 496454293653976479823406549 11635647507515073745861091)
              ·
                refine ⟨17453471261272610618791637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11635647507515073745861091 17453471261272610618791637)
                ·
                  refine ⟨409065732686076811377929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17453471261272610618791637 409065732686076811377929)
                  ·
                    rfl

theorem cell22_3584937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 1, 7].length) (baseStart_3584937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584937 prefixEnd_3584937 := by exact prefixLift 3584937
  have htrace : WordTrace (prefixWord ++ tailWord_3584937) baseStart_3584937 baseEnd_3584937 := by
    simpa [prefixWord, tailWord_3584937, baseEnd_3584937] using wordTrace_append hprefix tailTrace_3584937
  have hstable : (prefixWord ++ tailWord_3584937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584937).length < 2 ^ (prefixWord ++ tailWord_3584937).sum := by decide
  have hdescent : baseEnd_3584937 < baseStart_3584937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3584966 : List Nat := [6, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_3584966 : Nat := 118140960795 + 3584966 * 2 ^ 59
def prefixEnd_3584966 : Nat := 4983230072969 + 3 ^ 40 * 3584966 * 2
def baseEnd_3584966 : Nat := 409069041783628008386233

theorem tailTrace_3584966 : CollatzResearch.WordTrace tailWord_3584966 prefixEnd_3584966 409069041783628008386233 := by
  unfold tailWord_3584966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4086076622821497509160211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 87169634620191946862084501 4086076622821497509160211)
  ·
    refine ⟨6129114934232246263740317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4086076622821497509160211 6129114934232246263740317)
    ·
      refine ⟨2298418100337092348902619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6129114934232246263740317 2298418100337092348902619)
      ·
        refine ⟨3447627150505638523353929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2298418100337092348902619 3447627150505638523353929)
        ·
          refine ⟨2585720362879228892515447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3447627150505638523353929 2585720362879228892515447)
          ·
            refine ⟨3878580544318843338773171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585720362879228892515447 3878580544318843338773171)
            ·
              refine ⟨5817870816478265008159757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878580544318843338773171 5817870816478265008159757)
              ·
                refine ⟨2181701556179349378059909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5817870816478265008159757 2181701556179349378059909)
                ·
                  refine ⟨409069041783628008386233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2181701556179349378059909 409069041783628008386233)
                  ·
                    rfl

theorem cell22_3584966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_3584966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3584966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3584966 prefixEnd_3584966 := by exact prefixLift 3584966
  have htrace : WordTrace (prefixWord ++ tailWord_3584966) baseStart_3584966 baseEnd_3584966 := by
    simpa [prefixWord, tailWord_3584966, baseEnd_3584966] using wordTrace_append hprefix tailTrace_3584966
  have hstable : (prefixWord ++ tailWord_3584966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3584966).length < 2 ^ (prefixWord ++ tailWord_3584966).sum := by decide
  have hdescent : baseEnd_3584966 < baseStart_3584966 := by decide
  rcases family_descends (prefixWord ++ tailWord_3584966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585044 : List Nat := [2, 4, 3, 13]
def baseStart_3585044 : Nat := 118140960795 + 3585044 * 2 ^ 59
def prefixEnd_3585044 : Nat := 4983230072969 + 3 ^ 40 * 3585044 * 2
def baseEnd_3585044 : Nat := 1683448321460792622371

theorem tailTrace_3585044 : CollatzResearch.WordTrace tailWord_3585044 prefixEnd_3585044 1683448321460792622371 := by
  unfold tailWord_3585044
  simp only [CollatzResearch.WordTrace]
  refine ⟨65378648412002669807233093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87171531216003559742977457 65378648412002669807233093)
  ·
    refine ⟨12258496577250500588856205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65378648412002669807233093 12258496577250500588856205)
    ·
      refine ⟨4596936216468937720821077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12258496577250500588856205 4596936216468937720821077)
      ·
        refine ⟨1683448321460792622371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 4596936216468937720821077 1683448321460792622371)
        ·
          rfl

theorem cell22_3585044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 13].length) (baseStart_3585044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585044 prefixEnd_3585044 := by exact prefixLift 3585044
  have htrace : WordTrace (prefixWord ++ tailWord_3585044) baseStart_3585044 baseEnd_3585044 := by
    simpa [prefixWord, tailWord_3585044, baseEnd_3585044] using wordTrace_append hprefix tailTrace_3585044
  have hstable : (prefixWord ++ tailWord_3585044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585044).length < 2 ^ (prefixWord ++ tailWord_3585044).sum := by decide
  have hdescent : baseEnd_3585044 < baseStart_3585044 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585048 : List Nat := [2, 1, 2, 3, 2, 3, 2, 2, 2, 3]
def baseStart_3585048 : Nat := 118140960795 + 3585048 * 2 ^ 59
def prefixEnd_3585048 : Nat := 4983230072969 + 3 ^ 40 * 3585048 * 2
def baseEnd_3585048 : Nat := 1227235195626663144608447

theorem tailTrace_3585048 : CollatzResearch.WordTrace tailWord_3585048 prefixEnd_3585048 1227235195626663144608447 := by
  unfold tailWord_3585048
  simp only [CollatzResearch.WordTrace]
  refine ⟨65378721357995424148805899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87171628477327232198407865 65378721357995424148805899)
  ·
    refine ⟨98068082036993136223208849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65378721357995424148805899 98068082036993136223208849)
    ·
      refine ⟨73551061527744852167406637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98068082036993136223208849 73551061527744852167406637)
      ·
        refine ⟨27581648072904319562777489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73551061527744852167406637 27581648072904319562777489)
        ·
          refine ⟨20686236054678239672083117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27581648072904319562777489 20686236054678239672083117)
          ·
            refine ⟨7757338520504339877031169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20686236054678239672083117 7757338520504339877031169)
            ·
              refine ⟨5818003890378254907773377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7757338520504339877031169 5818003890378254907773377)
              ·
                refine ⟨4363502917783691180830033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5818003890378254907773377 4363502917783691180830033)
                ·
                  refine ⟨3272627188337768385622525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4363502917783691180830033 3272627188337768385622525)
                  ·
                    refine ⟨1227235195626663144608447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3272627188337768385622525 1227235195626663144608447)
                    ·
                      rfl

theorem cell22_3585048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_3585048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585048 prefixEnd_3585048 := by exact prefixLift 3585048
  have htrace : WordTrace (prefixWord ++ tailWord_3585048) baseStart_3585048 baseEnd_3585048 := by
    simpa [prefixWord, tailWord_3585048, baseEnd_3585048] using wordTrace_append hprefix tailTrace_3585048
  have hstable : (prefixWord ++ tailWord_3585048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585048).length < 2 ^ (prefixWord ++ tailWord_3585048).sum := by decide
  have hdescent : baseEnd_3585048 < baseStart_3585048 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585074 : List Nat := [3, 2, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_3585074 : Nat := 118140960795 + 3585074 * 2 ^ 59
def prefixEnd_3585074 : Nat := 4983230072969 + 3 ^ 40 * 3585074 * 2
def baseEnd_3585074 : Nat := 1227244095958007743458367

theorem tailTrace_3585074 : CollatzResearch.WordTrace tailWord_3585074 prefixEnd_3585074 1227244095958007743458367 := by
  unfold tailWord_3585074
  simp only [CollatzResearch.WordTrace]
  refine ⟨32689597753474163684514569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87172260675931103158705517 32689597753474163684514569)
  ·
    refine ⟨24517198315105622763385927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32689597753474163684514569 24517198315105622763385927)
    ·
      refine ⟨36775797472658434145078891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24517198315105622763385927 36775797472658434145078891)
      ·
        refine ⟨55163696208987651217618337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36775797472658434145078891 55163696208987651217618337)
        ·
          refine ⟨41372772156740738413213753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55163696208987651217618337 41372772156740738413213753)
          ·
            refine ⟨31029579117555553809910315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41372772156740738413213753 31029579117555553809910315)
            ·
              refine ⟨46544368676333330714865473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31029579117555553809910315 46544368676333330714865473)
              ·
                refine ⟨34908276507249998036149105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46544368676333330714865473 34908276507249998036149105)
                ·
                  refine ⟨26181207380437498527111829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34908276507249998036149105 26181207380437498527111829)
                  ·
                    refine ⟨1227244095958007743458367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26181207380437498527111829 1227244095958007743458367)
                    ·
                      rfl

theorem cell22_3585074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_3585074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585074 prefixEnd_3585074 := by exact prefixLift 3585074
  have htrace : WordTrace (prefixWord ++ tailWord_3585074) baseStart_3585074 baseEnd_3585074 := by
    simpa [prefixWord, tailWord_3585074, baseEnd_3585074] using wordTrace_append hprefix tailTrace_3585074
  have hstable : (prefixWord ++ tailWord_3585074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585074).length < 2 ^ (prefixWord ++ tailWord_3585074).sum := by decide
  have hdescent : baseEnd_3585074 < baseStart_3585074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585078 : List Nat := [5, 1, 2, 1, 1, 3, 3, 6]
def baseStart_3585078 : Nat := 118140960795 + 3585078 * 2 ^ 59
def prefixEnd_3585078 : Nat := 4983230072969 + 3 ^ 40 * 3585078 * 2
def baseEnd_3585078 : Nat := 136360607248861451817595

theorem tailTrace_3585078 : CollatzResearch.WordTrace tailWord_3585078 prefixEnd_3585078 136360607248861451817595 := by
  unfold tailWord_3585078
  simp only [CollatzResearch.WordTrace]
  refine ⟨8172408556617635213825243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 87172357937254775614135925 8172408556617635213825243)
  ·
    refine ⟨12258612834926452820737865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8172408556617635213825243 12258612834926452820737865)
    ·
      refine ⟨9193959626194839615553399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12258612834926452820737865 9193959626194839615553399)
      ·
        refine ⟨13790939439292259423330099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9193959626194839615553399 13790939439292259423330099)
        ·
          refine ⟨20686409158938389134995149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13790939439292259423330099 20686409158938389134995149)
          ·
            refine ⟨7757403434601895925623181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20686409158938389134995149 7757403434601895925623181)
            ·
              refine ⟨2909026287975710972108693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7757403434601895925623181 2909026287975710972108693)
              ·
                refine ⟨136360607248861451817595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2909026287975710972108693 136360607248861451817595)
                ·
                  rfl

theorem cell22_3585078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 3, 6].length) (baseStart_3585078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585078 prefixEnd_3585078 := by exact prefixLift 3585078
  have htrace : WordTrace (prefixWord ++ tailWord_3585078) baseStart_3585078 baseEnd_3585078 := by
    simpa [prefixWord, tailWord_3585078, baseEnd_3585078] using wordTrace_append hprefix tailTrace_3585078
  have hstable : (prefixWord ++ tailWord_3585078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585078).length < 2 ^ (prefixWord ++ tailWord_3585078).sum := by decide
  have hdescent : baseEnd_3585078 < baseStart_3585078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585093 : List Nat := [1, 3, 1, 1, 1, 3, 3, 5, 1, 3]
def baseStart_3585093 : Nat := 118140960795 + 3585093 * 2 ^ 59
def prefixEnd_3585093 : Nat := 4983230072969 + 3 ^ 40 * 3585093 * 2
def baseEnd_3585093 : Nat := 1227250600046298027233309

theorem tailTrace_3585093 : CollatzResearch.WordTrace tailWord_3585093 prefixEnd_3585093 1227250600046298027233309 := by
  unfold tailWord_3585093
  simp only [CollatzResearch.WordTrace]
  refine ⟨130759084000827820982999933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87172722667218547321999955 130759084000827820982999933)
  ·
    refine ⟨49034656500310432868624975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130759084000827820982999933 49034656500310432868624975)
    ·
      refine ⟨73551984750465649302937463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49034656500310432868624975 73551984750465649302937463)
      ·
        refine ⟨110327977125698473954406195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73551984750465649302937463 110327977125698473954406195)
        ·
          refine ⟨165491965688547710931609293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110327977125698473954406195 165491965688547710931609293)
          ·
            refine ⟨62059487133205391599353485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165491965688547710931609293 62059487133205391599353485)
            ·
              refine ⟨23272307674952021849757557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62059487133205391599353485 23272307674952021849757557)
              ·
                refine ⟨2181778844526752048414771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 23272307674952021849757557 2181778844526752048414771)
                ·
                  refine ⟨3272668266790128072622157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2181778844526752048414771 3272668266790128072622157)
                  ·
                    refine ⟨1227250600046298027233309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3272668266790128072622157 1227250600046298027233309)
                    ·
                      rfl

theorem cell22_3585093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 5, 1, 3].length) (baseStart_3585093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585093 prefixEnd_3585093 := by exact prefixLift 3585093
  have htrace : WordTrace (prefixWord ++ tailWord_3585093) baseStart_3585093 baseEnd_3585093 := by
    simpa [prefixWord, tailWord_3585093, baseEnd_3585093] using wordTrace_append hprefix tailTrace_3585093
  have hstable : (prefixWord ++ tailWord_3585093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585093).length < 2 ^ (prefixWord ++ tailWord_3585093).sum := by decide
  have hdescent : baseEnd_3585093 < baseStart_3585093 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585106 : List Nat := [3, 2, 2, 1, 3, 2, 1, 1, 7]
def baseStart_3585106 : Nat := 118140960795 + 3585106 * 2 ^ 59
def prefixEnd_3585106 : Nat := 4983230072969 + 3 ^ 40 * 3585106 * 2
def baseEnd_3585106 : Nat := 409085016737323442219423

theorem tailTrace_3585106 : CollatzResearch.WordTrace tailWord_3585106 prefixEnd_3585106 409085016737323442219423 := by
  unfold tailWord_3585106
  simp only [CollatzResearch.WordTrace]
  refine ⟨32689889537445181050805793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87173038766520482802148781 32689889537445181050805793)
  ·
    refine ⟨24517417153083885788104345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32689889537445181050805793 24517417153083885788104345)
    ·
      refine ⟨18388062864812914341078259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24517417153083885788104345 18388062864812914341078259)
      ·
        refine ⟨27582094297219371511617389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18388062864812914341078259 27582094297219371511617389)
        ·
          refine ⟨10343285361457264316856521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27582094297219371511617389 10343285361457264316856521)
          ·
            refine ⟨7757464021092948237642391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10343285361457264316856521 7757464021092948237642391)
            ·
              refine ⟨11636196031639422356463587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7757464021092948237642391 11636196031639422356463587)
              ·
                refine ⟨17454294047459133534695381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11636196031639422356463587 17454294047459133534695381)
                ·
                  refine ⟨409085016737323442219423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17454294047459133534695381 409085016737323442219423)
                  ·
                    rfl

theorem cell22_3585106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 1, 7].length) (baseStart_3585106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585106 prefixEnd_3585106 := by exact prefixLift 3585106
  have htrace : WordTrace (prefixWord ++ tailWord_3585106) baseStart_3585106 baseEnd_3585106 := by
    simpa [prefixWord, tailWord_3585106, baseEnd_3585106] using wordTrace_append hprefix tailTrace_3585106
  have hstable : (prefixWord ++ tailWord_3585106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585106).length < 2 ^ (prefixWord ++ tailWord_3585106).sum := by decide
  have hdescent : baseEnd_3585106 < baseStart_3585106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585153 : List Nat := [1, 2, 4, 2, 2, 1, 2, 3, 1, 4]
def baseStart_3585153 : Nat := 118140960795 + 3585153 * 2 ^ 59
def prefixEnd_3585153 : Nat := 4983230072969 + 3 ^ 40 * 3585153 * 2
def baseEnd_3585153 : Nat := 1227271139272477870733125

theorem tailTrace_3585153 : CollatzResearch.WordTrace tailWord_3585153 prefixEnd_3585153 1227271139272477870733125 := by
  unfold tailWord_3585153
  simp only [CollatzResearch.WordTrace]
  refine ⟨130761272380610451230184113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87174181587073634153456075 130761272380610451230184113)
  ·
    refine ⟨98070954285457838422638085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130761272380610451230184113 98070954285457838422638085)
    ·
      refine ⟨18388303928523344704244641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98070954285457838422638085 18388303928523344704244641)
      ·
        refine ⟨13791227946392508528183481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18388303928523344704244641 13791227946392508528183481)
        ·
          refine ⟨10343420959794381396137611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13791227946392508528183481 10343420959794381396137611)
          ·
            refine ⟨15515131439691572094206417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10343420959794381396137611 15515131439691572094206417)
            ·
              refine ⟨11636348579768679070654813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15515131439691572094206417 11636348579768679070654813)
              ·
                refine ⟨4363630717413254651495555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11636348579768679070654813 4363630717413254651495555)
                ·
                  refine ⟨6545446076119881977243333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4363630717413254651495555 6545446076119881977243333)
                  ·
                    refine ⟨1227271139272477870733125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6545446076119881977243333 1227271139272477870733125)
                    ·
                      rfl

theorem cell22_3585153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_3585153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585153 prefixEnd_3585153 := by exact prefixLift 3585153
  have htrace : WordTrace (prefixWord ++ tailWord_3585153) baseStart_3585153 baseEnd_3585153 := by
    simpa [prefixWord, tailWord_3585153, baseEnd_3585153] using wordTrace_append hprefix tailTrace_3585153
  have hstable : (prefixWord ++ tailWord_3585153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585153).length < 2 ^ (prefixWord ++ tailWord_3585153).sum := by decide
  have hdescent : baseEnd_3585153 < baseStart_3585153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585181 : List Nat := [1, 4, 2, 1, 1, 2, 1, 2, 4, 4]
def baseStart_3585181 : Nat := 118140960795 + 3585181 * 2 ^ 59
def prefixEnd_3585181 : Nat := 4983230072969 + 3 ^ 40 * 3585181 * 2
def baseEnd_3585181 : Nat := 1227280724244695131033039

theorem tailTrace_3585181 : CollatzResearch.WordTrace tailWord_3585181 prefixEnd_3585181 1227280724244695131033039 := by
  unfold tailWord_3585181
  simp only [CollatzResearch.WordTrace]
  refine ⟨130762293624509012012203397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87174862416339341341468931 130762293624509012012203397)
  ·
    refine ⟨24517930054595439752288137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130762293624509012012203397 24517930054595439752288137)
    ·
      refine ⟨18388447540946579814216103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24517930054595439752288137 18388447540946579814216103)
      ·
        refine ⟨27582671311419869721324155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18388447540946579814216103 27582671311419869721324155)
        ·
          refine ⟨41374006967129804581986233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27582671311419869721324155 41374006967129804581986233)
          ·
            refine ⟨31030505225347353436489675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41374006967129804581986233 31030505225347353436489675)
            ·
              refine ⟨46545757838021030154734513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31030505225347353436489675 46545757838021030154734513)
              ·
                refine ⟨34909318378515772616050885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46545757838021030154734513 34909318378515772616050885)
                ·
                  refine ⟨6545497195971707365509541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34909318378515772616050885 6545497195971707365509541)
                  ·
                    refine ⟨1227280724244695131033039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6545497195971707365509541 1227280724244695131033039)
                    ·
                      rfl

theorem cell22_3585181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_3585181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585181 prefixEnd_3585181 := by exact prefixLift 3585181
  have htrace : WordTrace (prefixWord ++ tailWord_3585181) baseStart_3585181 baseEnd_3585181 := by
    simpa [prefixWord, tailWord_3585181, baseEnd_3585181] using wordTrace_append hprefix tailTrace_3585181
  have hstable : (prefixWord ++ tailWord_3585181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585181).length < 2 ^ (prefixWord ++ tailWord_3585181).sum := by decide
  have hdescent : baseEnd_3585181 < baseStart_3585181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585211 : List Nat := [1, 1, 1, 1, 1, 2, 4, 1, 7, 3]
def baseStart_3585211 : Nat := 118140960795 + 3585211 * 2 ^ 59
def prefixEnd_3585211 : Nat := 4983230072969 + 3 ^ 40 * 3585211 * 2
def baseEnd_3585211 : Nat := 1227290993857785052782947

theorem tailTrace_3585211 : CollatzResearch.WordTrace tailWord_3585211 prefixEnd_3585211 1227290993857785052782947 := by
  unfold tailWord_3585211
  simp only [CollatzResearch.WordTrace]
  refine ⟨130763387814400327135795487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87175591876266884757196991 130763387814400327135795487)
  ·
    refine ⟨196145081721600490703693231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130763387814400327135795487 196145081721600490703693231)
    ·
      refine ⟨294217622582400736055539847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196145081721600490703693231 294217622582400736055539847)
      ·
        refine ⟨441326433873601104083309771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294217622582400736055539847 441326433873601104083309771)
        ·
          refine ⟨661989650810401656124964657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 441326433873601104083309771 661989650810401656124964657)
          ·
            refine ⟨496492238107801242093723493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 661989650810401656124964657 496492238107801242093723493)
            ·
              refine ⟨93092294645212732892573155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 496492238107801242093723493 93092294645212732892573155)
              ·
                refine ⟨139638441967819099338859733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93092294645212732892573155 139638441967819099338859733)
                ·
                  refine ⟨3272775983620760140754525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 139638441967819099338859733 3272775983620760140754525)
                  ·
                    refine ⟨1227290993857785052782947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3272775983620760140754525 1227290993857785052782947)
                    ·
                      rfl

theorem cell22_3585211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 1, 7, 3].length) (baseStart_3585211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585211 prefixEnd_3585211 := by exact prefixLift 3585211
  have htrace : WordTrace (prefixWord ++ tailWord_3585211) baseStart_3585211 baseEnd_3585211 := by
    simpa [prefixWord, tailWord_3585211, baseEnd_3585211] using wordTrace_append hprefix tailTrace_3585211
  have hstable : (prefixWord ++ tailWord_3585211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585211).length < 2 ^ (prefixWord ++ tailWord_3585211).sum := by decide
  have hdescent : baseEnd_3585211 < baseStart_3585211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585217 : List Nat := [1, 2, 6, 1, 1, 2, 2, 2, 2, 3]
def baseStart_3585217 : Nat := 118140960795 + 3585217 * 2 ^ 59
def prefixEnd_3585217 : Nat := 4983230072969 + 3 ^ 40 * 3585217 * 2
def baseEnd_3585217 : Nat := 1227293047780403037132929

theorem tailTrace_3585217 : CollatzResearch.WordTrace tailWord_3585217 prefixEnd_3585217 1227293047780403037132929 := by
  unfold tailWord_3585217
  simp only [CollatzResearch.WordTrace]
  refine ⟨130763606652378590160513905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87175737768252393440342603 130763606652378590160513905)
  ·
    refine ⟨98072704989283942620385429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130763606652378590160513905 98072704989283942620385429)
    ·
      refine ⟨4597158046372684810330567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98072704989283942620385429 4597158046372684810330567)
      ·
        refine ⟨6895737069559027215495851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4597158046372684810330567 6895737069559027215495851)
        ·
          refine ⟨10343605604338540823243777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6895737069559027215495851 10343605604338540823243777)
          ·
            refine ⟨7757704203253905617432833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10343605604338540823243777 7757704203253905617432833)
            ·
              refine ⟨5818278152440429213074625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7757704203253905617432833 5818278152440429213074625)
              ·
                refine ⟨4363708614330321909805969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5818278152440429213074625 4363708614330321909805969)
                ·
                  refine ⟨3272781460747741432354477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4363708614330321909805969 3272781460747741432354477)
                  ·
                    refine ⟨1227293047780403037132929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3272781460747741432354477 1227293047780403037132929)
                    ·
                      rfl

theorem cell22_3585217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_3585217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585217 prefixEnd_3585217 := by exact prefixLift 3585217
  have htrace : WordTrace (prefixWord ++ tailWord_3585217) baseStart_3585217 baseEnd_3585217 := by
    simpa [prefixWord, tailWord_3585217, baseEnd_3585217] using wordTrace_append hprefix tailTrace_3585217
  have hstable : (prefixWord ++ tailWord_3585217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585217).length < 2 ^ (prefixWord ++ tailWord_3585217).sum := by decide
  have hdescent : baseEnd_3585217 < baseStart_3585217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585226 : List Nat := [3, 1, 2, 1, 3, 2, 1, 1, 2, 6]
def baseStart_3585226 : Nat := 118140960795 + 3585226 * 2 ^ 59
def prefixEnd_3585226 : Nat := 4983230072969 + 3 ^ 40 * 3585226 * 2
def baseEnd_3585226 : Nat := 1227296128664330013657901

theorem tailTrace_3585226 : CollatzResearch.WordTrace tailWord_3585226 prefixEnd_3585226 1227296128664330013657901 := by
  unfold tailWord_3585226
  simp only [CollatzResearch.WordTrace]
  refine ⟨32690983727336496174397883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 87175956606230656465061021 32690983727336496174397883)
  ·
    refine ⟨49036475591004744261596825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32690983727336496174397883 49036475591004744261596825)
    ·
      refine ⟨36777356693253558196197619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49036475591004744261596825 36777356693253558196197619)
      ·
        refine ⟨55166035039880337294296429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36777356693253558196197619 55166035039880337294296429)
        ·
          refine ⟨20687263139955126485361161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55166035039880337294296429 20687263139955126485361161)
          ·
            refine ⟨15515447354966344864020871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20687263139955126485361161 15515447354966344864020871)
            ·
              refine ⟨23273171032449517296031307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15515447354966344864020871 23273171032449517296031307)
              ·
                refine ⟨34909756548674275944046961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23273171032449517296031307 34909756548674275944046961)
                ·
                  refine ⟨26182317411505706958035221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34909756548674275944046961 26182317411505706958035221)
                  ·
                    refine ⟨1227296128664330013657901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26182317411505706958035221 1227296128664330013657901)
                    ·
                      rfl

theorem cell22_3585226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 1, 2, 6].length) (baseStart_3585226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585226 prefixEnd_3585226 := by exact prefixLift 3585226
  have htrace : WordTrace (prefixWord ++ tailWord_3585226) baseStart_3585226 baseEnd_3585226 := by
    simpa [prefixWord, tailWord_3585226, baseEnd_3585226] using wordTrace_append hprefix tailTrace_3585226
  have hstable : (prefixWord ++ tailWord_3585226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585226).length < 2 ^ (prefixWord ++ tailWord_3585226).sum := by decide
  have hdescent : baseEnd_3585226 < baseStart_3585226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585230 : List Nat := [4, 1, 1, 1, 6, 1, 1, 7]
def baseStart_3585230 : Nat := 118140960795 + 3585230 * 2 ^ 59
def prefixEnd_3585230 : Nat := 4983230072969 + 3 ^ 40 * 3585230 * 2
def baseEnd_3585230 : Nat := 136366388660675037395321

theorem tailTrace_3585230 : CollatzResearch.WordTrace tailWord_3585230 prefixEnd_3585230 136366388660675037395321 := by
  unfold tailWord_3585230
  simp only [CollatzResearch.WordTrace]
  refine ⟨16345510100166436672592143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 87176053867554328920491429 16345510100166436672592143)
  ·
    refine ⟨24518265150249655008888215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16345510100166436672592143 24518265150249655008888215)
    ·
      refine ⟨36777397725374482513332323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24518265150249655008888215 36777397725374482513332323)
      ·
        refine ⟨55166096588061723769998485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36777397725374482513332323 55166096588061723769998485)
        ·
          refine ⟨2585910777565393301718679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 55166096588061723769998485 2585910777565393301718679)
          ·
            refine ⟨3878866166348089952578019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585910777565393301718679 3878866166348089952578019)
            ·
              refine ⟨5818299249522134928867029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878866166348089952578019 5818299249522134928867029)
              ·
                refine ⟨136366388660675037395321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5818299249522134928867029 136366388660675037395321)
                ·
                  rfl

theorem cell22_3585230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 1, 1, 7].length) (baseStart_3585230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585230 prefixEnd_3585230 := by exact prefixLift 3585230
  have htrace : WordTrace (prefixWord ++ tailWord_3585230) baseStart_3585230 baseEnd_3585230 := by
    simpa [prefixWord, tailWord_3585230, baseEnd_3585230] using wordTrace_append hprefix tailTrace_3585230
  have hstable : (prefixWord ++ tailWord_3585230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585230).length < 2 ^ (prefixWord ++ tailWord_3585230).sum := by decide
  have hdescent : baseEnd_3585230 < baseStart_3585230 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585256 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 1, 7]
def baseStart_3585256 : Nat := 118140960795 + 3585256 * 2 ^ 59
def prefixEnd_3585256 : Nat := 4983230072969 + 3 ^ 40 * 3585256 * 2
def baseEnd_3585256 : Nat := 1227306398277419935407809

theorem tailTrace_3585256 : CollatzResearch.WordTrace tailWord_3585256 prefixEnd_3585256 1227306398277419935407809 := by
  unfold tailWord_3585256
  simp only [CollatzResearch.WordTrace]
  refine ⟨65382514549618649910591811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87176686066158199880789081 65382514549618649910591811)
  ·
    refine ⟨98073771824427974865887717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65382514549618649910591811 98073771824427974865887717)
    ·
      refine ⟨18388832217080245287353947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98073771824427974865887717 18388832217080245287353947)
      ·
        refine ⟨27583248325620367931030921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18388832217080245287353947 27583248325620367931030921)
        ·
          refine ⟨20687436244215275948273191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27583248325620367931030921 20687436244215275948273191)
          ·
            refine ⟨31031154366322913922409787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20687436244215275948273191 31031154366322913922409787)
            ·
              refine ⟨46546731549484370883614681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31031154366322913922409787 46546731549484370883614681)
              ·
                refine ⟨34910048662113278162711011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46546731549484370883614681 34910048662113278162711011)
                ·
                  refine ⟨52365072993169917244066517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34910048662113278162711011 52365072993169917244066517)
                  ·
                    refine ⟨1227306398277419935407809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52365072993169917244066517 1227306398277419935407809)
                    ·
                      rfl

theorem cell22_3585256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_3585256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585256 prefixEnd_3585256 := by exact prefixLift 3585256
  have htrace : WordTrace (prefixWord ++ tailWord_3585256) baseStart_3585256 baseEnd_3585256 := by
    simpa [prefixWord, tailWord_3585256, baseEnd_3585256] using wordTrace_append hprefix tailTrace_3585256
  have hstable : (prefixWord ++ tailWord_3585256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585256).length < 2 ^ (prefixWord ++ tailWord_3585256).sum := by decide
  have hdescent : baseEnd_3585256 < baseStart_3585256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585268 : List Nat := [2, 6, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3585268 : Nat := 118140960795 + 3585268 * 2 ^ 59
def prefixEnd_3585268 : Nat := 4983230072969 + 3 ^ 40 * 3585268 * 2
def baseEnd_3585268 : Nat := 1227310506122655904107773

theorem tailTrace_3585268 : CollatzResearch.WordTrace tailWord_3585268 prefixEnd_3585268 1227310506122655904107773 := by
  unfold tailWord_3585268
  simp only [CollatzResearch.WordTrace]
  refine ⟨65382733387596912935310229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 87176977850129217247080305 65382733387596912935310229)
  ·
    refine ⟨3064815627543605293842667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 65382733387596912935310229 3064815627543605293842667)
    ·
      refine ⟨4597223441315407940764001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3064815627543605293842667 4597223441315407940764001)
      ·
        refine ⟨3447917580986555955573001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4597223441315407940764001 3447917580986555955573001)
        ·
          refine ⟨2585938185739916966679751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3447917580986555955573001 2585938185739916966679751)
          ·
            refine ⟨3878907278609875450019627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2585938185739916966679751 3878907278609875450019627)
            ·
              refine ⟨5818360917914813175029441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3878907278609875450019627 5818360917914813175029441)
              ·
                refine ⟨4363770688436109881272081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5818360917914813175029441 4363770688436109881272081)
                ·
                  refine ⟨3272828016327082410954061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4363770688436109881272081 3272828016327082410954061)
                  ·
                    refine ⟨1227310506122655904107773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3272828016327082410954061 1227310506122655904107773)
                    ·
                      rfl

theorem cell22_3585268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3585268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585268 prefixEnd_3585268 := by exact prefixLift 3585268
  have htrace : WordTrace (prefixWord ++ tailWord_3585268) baseStart_3585268 baseEnd_3585268 := by
    simpa [prefixWord, tailWord_3585268, baseEnd_3585268] using wordTrace_append hprefix tailTrace_3585268
  have hstable : (prefixWord ++ tailWord_3585268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585268).length < 2 ^ (prefixWord ++ tailWord_3585268).sum := by decide
  have hdescent : baseEnd_3585268 < baseStart_3585268 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585331 : List Nat := [1, 1, 1, 2, 5, 2, 10]
def baseStart_3585331 : Nat := 118140960795 + 3585331 * 2 ^ 59
def prefixEnd_3585331 : Nat := 4983230072969 + 3 ^ 40 * 3585331 * 2
def baseEnd_3585331 : Nat := 45456743418894249621577

theorem tailTrace_3585331 : CollatzResearch.WordTrace tailWord_3585331 prefixEnd_3585331 45456743418894249621577 := by
  unfold tailWord_3585331
  simp only [CollatzResearch.WordTrace]
  refine ⟨130767764573965587630163847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87178509715977058420109231 130767764573965587630163847)
  ·
    refine ⟨196151646860948381445245771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130767764573965587630163847 196151646860948381445245771)
    ·
      refine ⟨294227470291422572167868657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196151646860948381445245771 294227470291422572167868657)
      ·
        refine ⟨220670602718566929125901493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294227470291422572167868657 220670602718566929125901493)
        ·
          refine ⟨20687869004865649605553265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 220670602718566929125901493 20687869004865649605553265)
          ·
            refine ⟨15515901753649237204164949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20687869004865649605553265 15515901753649237204164949)
            ·
              refine ⟨45456743418894249621577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 15515901753649237204164949 45456743418894249621577)
              ·
                rfl

theorem cell22_3585331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 10].length) (baseStart_3585331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585331 prefixEnd_3585331 := by exact prefixLift 3585331
  have htrace : WordTrace (prefixWord ++ tailWord_3585331) baseStart_3585331 baseEnd_3585331 := by
    simpa [prefixWord, tailWord_3585331, baseEnd_3585331] using wordTrace_append hprefix tailTrace_3585331
  have hstable : (prefixWord ++ tailWord_3585331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585331).length < 2 ^ (prefixWord ++ tailWord_3585331).sum := by decide
  have hdescent : baseEnd_3585331 < baseStart_3585331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3585333 : List Nat := [1, 3, 3, 1, 2, 2, 1, 1, 4, 4]
def baseStart_3585333 : Nat := 118140960795 + 3585333 * 2 ^ 59
def prefixEnd_3585333 : Nat := 4983230072969 + 3 ^ 40 * 3585333 * 2
def baseEnd_3585333 : Nat := 1227332756951017401232573

theorem tailTrace_3585333 : CollatzResearch.WordTrace tailWord_3585333 prefixEnd_3585333 1227332756951017401232573 := by
  unfold tailWord_3585333
  simp only [CollatzResearch.WordTrace]
  refine ⟨130767837519958341971736653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 87178558346638894647824435 130767837519958341971736653)
  ·
    refine ⟨49037939069984378239401245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130767837519958341971736653 49037939069984378239401245)
    ·
      refine ⟨18389227151244141839775467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49037939069984378239401245 18389227151244141839775467)
      ·
        refine ⟨27583840726866212759663201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18389227151244141839775467 27583840726866212759663201)
        ·
          refine ⟨20687880545149659569747401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27583840726866212759663201 20687880545149659569747401)
          ·
            refine ⟨15515910408862244677310551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20687880545149659569747401 15515910408862244677310551)
            ·
              refine ⟨23273865613293367015965827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15515910408862244677310551 23273865613293367015965827)
              ·
                refine ⟨34910798419940050523948741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23273865613293367015965827 34910798419940050523948741)
                ·
                  refine ⟨6545774703738759473240389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34910798419940050523948741 6545774703738759473240389)
                  ·
                    refine ⟨1227332756951017401232573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6545774703738759473240389 1227332756951017401232573)
                    ·
                      rfl

theorem cell22_3585333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_3585333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3585333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3585333 prefixEnd_3585333 := by exact prefixLift 3585333
  have htrace : WordTrace (prefixWord ++ tailWord_3585333) baseStart_3585333 baseEnd_3585333 := by
    simpa [prefixWord, tailWord_3585333, baseEnd_3585333] using wordTrace_append hprefix tailTrace_3585333
  have hstable : (prefixWord ++ tailWord_3585333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3585333).length < 2 ^ (prefixWord ++ tailWord_3585333).sum := by decide
  have hdescent : baseEnd_3585333 < baseStart_3585333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3585333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
