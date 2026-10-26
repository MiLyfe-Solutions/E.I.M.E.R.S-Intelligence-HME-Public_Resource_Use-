import V185TrunkScan22Chunk144

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1296116 : List Nat := [2, 6, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1296116 : Nat := 118140960795 + 1296116 * 2 ^ 59
def prefixEnd_1296116 : Nat := 4983230072969 + 3 ^ 40 * 1296116 * 2
def baseEnd_1296116 : Nat := 147895664885101371975395

theorem tailTrace_1296116 : CollatzResearch.WordTrace tailWord_1296116 prefixEnd_1296116 147895664885101371975395 := by
  unfold tailWord_1296116
  simp only [CollatzResearch.WordTrace]
  refine ⟨23636617086200282917310101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31515489448267043889746801 23636617086200282917310101)
  ·
    refine ⟨1107966425915638261748911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23636617086200282917310101 1107966425915638261748911)
    ·
      refine ⟨1661949638873457392623367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1107966425915638261748911 1661949638873457392623367)
      ·
        refine ⟨2492924458310186088935051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1661949638873457392623367 2492924458310186088935051)
        ·
          refine ⟨3739386687465279133402577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2492924458310186088935051 3739386687465279133402577)
          ·
            refine ⟨2804540015598959350051933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3739386687465279133402577 2804540015598959350051933)
            ·
              refine ⟨1051702505849609756269475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2804540015598959350051933 1051702505849609756269475)
              ·
                refine ⟨1577553758774414634404213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1051702505849609756269475 1577553758774414634404213)
                ·
                  refine ⟨147895664885101371975395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1577553758774414634404213 147895664885101371975395)
                  ·
                    rfl

theorem cell22_1296116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1296116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296116 prefixEnd_1296116 := by exact prefixLift 1296116
  have htrace : WordTrace (prefixWord ++ tailWord_1296116) baseStart_1296116 baseEnd_1296116 := by
    simpa [prefixWord, tailWord_1296116, baseEnd_1296116] using wordTrace_append hprefix tailTrace_1296116
  have hstable : (prefixWord ++ tailWord_1296116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296116).length < 2 ^ (prefixWord ++ tailWord_1296116).sum := by decide
  have hdescent : baseEnd_1296116 < baseStart_1296116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296123 : List Nat := [1, 1, 1, 1, 1, 3, 1, 3, 6, 4]
def baseStart_1296123 : Nat := 118140960795 + 1296123 * 2 ^ 59
def prefixEnd_1296123 : Nat := 4983230072969 + 3 ^ 40 * 1296123 * 2
def baseEnd_1296123 : Nat := 443689390898358431001163

theorem tailTrace_1296123 : CollatzResearch.WordTrace tailWord_1296123 prefixEnd_1296123 443689390898358431001163 := by
  unfold tailWord_1296123
  simp only [CollatzResearch.WordTrace]
  refine ⟨47273489483375206030125023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31515659655583470686750015 47273489483375206030125023)
  ·
    refine ⟨70910234225062809045187535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47273489483375206030125023 70910234225062809045187535)
    ·
      refine ⟨106365351337594213567781303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70910234225062809045187535 106365351337594213567781303)
      ·
        refine ⟨159548027006391320351671955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106365351337594213567781303 159548027006391320351671955)
        ·
          refine ⟨239322040509586980527507933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159548027006391320351671955 239322040509586980527507933)
          ·
            refine ⟨89745765191095117697815475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239322040509586980527507933 89745765191095117697815475)
            ·
              refine ⟨134618647786642676546723213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89745765191095117697815475 134618647786642676546723213)
              ·
                refine ⟨50481992919991003705021205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134618647786642676546723213 50481992919991003705021205)
                ·
                  refine ⟨2366343418124578298672869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 50481992919991003705021205 2366343418124578298672869)
                  ·
                    refine ⟨443689390898358431001163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2366343418124578298672869 443689390898358431001163)
                    ·
                      rfl

theorem cell22_1296123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 3, 6, 4].length) (baseStart_1296123 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296123 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296123 prefixEnd_1296123 := by exact prefixLift 1296123
  have htrace : WordTrace (prefixWord ++ tailWord_1296123) baseStart_1296123 baseEnd_1296123 := by
    simpa [prefixWord, tailWord_1296123, baseEnd_1296123] using wordTrace_append hprefix tailTrace_1296123
  have hstable : (prefixWord ++ tailWord_1296123).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296123).length < 2 ^ (prefixWord ++ tailWord_1296123).sum := by decide
  have hdescent : baseEnd_1296123 < baseStart_1296123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296183 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 9]
def baseStart_1296183 : Nat := 118140960795 + 1296183 * 2 ^ 59
def prefixEnd_1296183 : Nat := 4983230072969 + 3 ^ 40 * 1296183 * 2
def baseEnd_1296183 : Nat := 147903310041512758166993

theorem tailTrace_1296183 : CollatzResearch.WordTrace tailWord_1296183 prefixEnd_1296183 147903310041512758166993 := by
  unfold tailWord_1296183
  simp only [CollatzResearch.WordTrace]
  refine ⟨47275677863157836277309203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31517118575438557518206135 47275677863157836277309203)
  ·
    refine ⟨70913516794736754415963805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47275677863157836277309203 70913516794736754415963805)
    ·
      refine ⟨26592568798026282905986427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 70913516794736754415963805 26592568798026282905986427)
      ·
        refine ⟨39888853197039424358979641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26592568798026282905986427 39888853197039424358979641)
        ·
          refine ⟨29916639897779568269234731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39888853197039424358979641 29916639897779568269234731)
          ·
            refine ⟨44874959846669352403852097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29916639897779568269234731 44874959846669352403852097)
            ·
              refine ⟨33656219885002014302889073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44874959846669352403852097 33656219885002014302889073)
              ·
                refine ⟨25242164913751510727166805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33656219885002014302889073 25242164913751510727166805)
                ·
                  refine ⟨147903310041512758166993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25242164913751510727166805 147903310041512758166993)
                  ·
                    rfl

theorem cell22_1296183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 9].length) (baseStart_1296183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296183 prefixEnd_1296183 := by exact prefixLift 1296183
  have htrace : WordTrace (prefixWord ++ tailWord_1296183) baseStart_1296183 baseEnd_1296183 := by
    simpa [prefixWord, tailWord_1296183, baseEnd_1296183] using wordTrace_append hprefix tailTrace_1296183
  have hstable : (prefixWord ++ tailWord_1296183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296183).length < 2 ^ (prefixWord ++ tailWord_1296183).sum := by decide
  have hdescent : baseEnd_1296183 < baseStart_1296183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296264 : List Nat := [2, 1, 3, 3, 3, 1, 1, 3, 1, 4]
def baseStart_1296264 : Nat := 118140960795 + 1296264 * 2 ^ 59
def prefixEnd_1296264 : Nat := 4983230072969 + 3 ^ 40 * 1296264 * 2
def baseEnd_1296264 : Nat := 443737658079881063225731

theorem tailTrace_1296264 : CollatzResearch.WordTrace tailWord_1296264 prefixEnd_1296264 443737658079881063225731 := by
  unfold tailWord_1296264
  simp only [CollatzResearch.WordTrace]
  refine ⟨23639316087932193555503923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31519088117242924740671897 23639316087932193555503923)
  ·
    refine ⟨35458974131898290333255885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23639316087932193555503923 35458974131898290333255885)
    ·
      refine ⟨13297115299461858874970957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35458974131898290333255885 13297115299461858874970957)
      ·
        refine ⟨4986418237298197078114109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13297115299461858874970957 4986418237298197078114109)
        ·
          refine ⟨1869906838986823904292791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4986418237298197078114109 1869906838986823904292791)
          ·
            refine ⟨2804860258480235856439187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869906838986823904292791 2804860258480235856439187)
            ·
              refine ⟨4207290387720353784658781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2804860258480235856439187 4207290387720353784658781)
              ·
                refine ⟨1577733895395132669247043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4207290387720353784658781 1577733895395132669247043)
                ·
                  refine ⟨2366600843092699003870565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1577733895395132669247043 2366600843092699003870565)
                  ·
                    refine ⟨443737658079881063225731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2366600843092699003870565 443737658079881063225731)
                    ·
                      rfl

theorem cell22_1296264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_1296264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296264 prefixEnd_1296264 := by exact prefixLift 1296264
  have htrace : WordTrace (prefixWord ++ tailWord_1296264) baseStart_1296264 baseEnd_1296264 := by
    simpa [prefixWord, tailWord_1296264, baseEnd_1296264] using wordTrace_append hprefix tailTrace_1296264
  have hstable : (prefixWord ++ tailWord_1296264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296264).length < 2 ^ (prefixWord ++ tailWord_1296264).sum := by decide
  have hdescent : baseEnd_1296264 < baseStart_1296264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296277 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 4, 3]
def baseStart_1296277 : Nat := 118140960795 + 1296277 * 2 ^ 59
def prefixEnd_1296277 : Nat := 4983230072969 + 3 ^ 40 * 1296277 * 2
def baseEnd_1296277 : Nat := 443742108245553362650691

theorem tailTrace_1296277 : CollatzResearch.WordTrace tailWord_1296277 prefixEnd_1296277 443742108245553362650691 := by
  unfold tailWord_1296277
  simp only [CollatzResearch.WordTrace]
  refine ⟨47279106324817290331231085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31519404216544860220820723 47279106324817290331231085)
  ·
    refine ⟨17729664871806483874211657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47279106324817290331231085 17729664871806483874211657)
    ·
      refine ⟨13297248653854862905658743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17729664871806483874211657 13297248653854862905658743)
      ·
        refine ⟨19945872980782294358488115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13297248653854862905658743 19945872980782294358488115)
        ·
          refine ⟨29918809471173441537732173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19945872980782294358488115 29918809471173441537732173)
          ·
            refine ⟨11219553551690040576649565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29918809471173441537732173 11219553551690040576649565)
            ·
              refine ⟨4207332581883765216243587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11219553551690040576649565 4207332581883765216243587)
              ·
                refine ⟨6310998872825647824365381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4207332581883765216243587 6310998872825647824365381)
                ·
                  refine ⟨1183312288654808967068509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6310998872825647824365381 1183312288654808967068509)
                  ·
                    refine ⟨443742108245553362650691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1183312288654808967068509 443742108245553362650691)
                    ·
                      rfl

theorem cell22_1296277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_1296277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296277 prefixEnd_1296277 := by exact prefixLift 1296277
  have htrace : WordTrace (prefixWord ++ tailWord_1296277) baseStart_1296277 baseEnd_1296277 := by
    simpa [prefixWord, tailWord_1296277, baseEnd_1296277] using wordTrace_append hprefix tailTrace_1296277
  have hstable : (prefixWord ++ tailWord_1296277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296277).length < 2 ^ (prefixWord ++ tailWord_1296277).sum := by decide
  have hdescent : baseEnd_1296277 < baseStart_1296277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296335 : List Nat := [1, 1, 2, 1, 1, 5, 1, 3, 7]
def baseStart_1296335 : Nat := 118140960795 + 1296335 * 2 ^ 59
def prefixEnd_1296335 : Nat := 4983230072969 + 3 ^ 40 * 1296335 * 2
def baseEnd_1296335 : Nat := 147920654276953514900171

theorem tailTrace_1296335 : CollatzResearch.WordTrace tailWord_1296335 prefixEnd_1296335 147920654276953514900171 := by
  unfold tailWord_1296335
  simp only [CollatzResearch.WordTrace]
  refine ⟨47281221758607166236842459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31520814505738110824561639 47281221758607166236842459)
  ·
    refine ⟨70921832637910749355263689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47281221758607166236842459 70921832637910749355263689)
    ·
      refine ⟨53191374478433062016447767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70921832637910749355263689 53191374478433062016447767)
      ·
        refine ⟨79787061717649593024671651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53191374478433062016447767 79787061717649593024671651)
        ·
          refine ⟨119680592576474389537007477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79787061717649593024671651 119680592576474389537007477)
          ·
            refine ⟨11220055554044474019094451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 119680592576474389537007477 11220055554044474019094451)
            ·
              refine ⟨16830083331066711028641677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11220055554044474019094451 16830083331066711028641677)
              ·
                refine ⟨6311281249150016635740629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16830083331066711028641677 6311281249150016635740629)
                ·
                  refine ⟨147920654276953514900171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6311281249150016635740629 147920654276953514900171)
                  ·
                    rfl

theorem cell22_1296335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 3, 7].length) (baseStart_1296335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296335 prefixEnd_1296335 := by exact prefixLift 1296335
  have htrace : WordTrace (prefixWord ++ tailWord_1296335) baseStart_1296335 baseEnd_1296335 := by
    simpa [prefixWord, tailWord_1296335, baseEnd_1296335] using wordTrace_append hprefix tailTrace_1296335
  have hstable : (prefixWord ++ tailWord_1296335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296335).length < 2 ^ (prefixWord ++ tailWord_1296335).sum := by decide
  have hdescent : baseEnd_1296335 < baseStart_1296335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296427 : List Nat := [1, 1, 1, 1, 2, 1, 4, 5, 2, 4]
def baseStart_1296427 : Nat := 118140960795 + 1296427 * 2 ^ 59
def prefixEnd_1296427 : Nat := 4983230072969 + 3 ^ 40 * 1296427 * 2
def baseEnd_1296427 : Nat := 443793456311002971400231

theorem tailTrace_1296427 : CollatzResearch.WordTrace tailWord_1296427 prefixEnd_1296427 443793456311002971400231 := by
  unfold tailWord_1296427
  simp only [CollatzResearch.WordTrace]
  refine ⟨47284577274273865949191535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31523051516182577299461023 47284577274273865949191535)
  ·
    refine ⟨70926865911410798923787303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47284577274273865949191535 70926865911410798923787303)
    ·
      refine ⟨106390298867116198385680955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70926865911410798923787303 106390298867116198385680955)
      ·
        refine ⟨159585448300674297578521433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106390298867116198385680955 159585448300674297578521433)
        ·
          refine ⟨119689086225505723183891075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159585448300674297578521433 119689086225505723183891075)
          ·
            refine ⟨179533629338258584775836613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119689086225505723183891075 179533629338258584775836613)
            ·
              refine ⟨33662555500923484645469365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 179533629338258584775836613 33662555500923484645469365)
              ·
                refine ⟨3155864578211576685512753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33662555500923484645469365 3155864578211576685512753)
                ·
                  refine ⟨2366898433658682514134565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3155864578211576685512753 2366898433658682514134565)
                  ·
                    refine ⟨443793456311002971400231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2366898433658682514134565 443793456311002971400231)
                    ·
                      rfl

theorem cell22_1296427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 5, 2, 4].length) (baseStart_1296427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296427 prefixEnd_1296427 := by exact prefixLift 1296427
  have htrace : WordTrace (prefixWord ++ tailWord_1296427) baseStart_1296427 baseEnd_1296427 := by
    simpa [prefixWord, tailWord_1296427, baseEnd_1296427] using wordTrace_append hprefix tailTrace_1296427
  have hstable : (prefixWord ++ tailWord_1296427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296427).length < 2 ^ (prefixWord ++ tailWord_1296427).sum := by decide
  have hdescent : baseEnd_1296427 < baseStart_1296427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296474 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 3, 3]
def baseStart_1296474 : Nat := 118140960795 + 1296474 * 2 ^ 59
def prefixEnd_1296474 : Nat := 4983230072969 + 3 ^ 40 * 1296474 * 2
def baseEnd_1296474 : Nat := 443809545371510515475087

theorem tailTrace_1296474 : CollatzResearch.WordTrace tailWord_1296474 prefixEnd_1296474 443809545371510515475087 := by
  unfold tailWord_1296474
  simp only [CollatzResearch.WordTrace]
  refine ⟨11821572876275898244038119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31524194336735728650768317 11821572876275898244038119)
  ·
    refine ⟨17732359314413847366057179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11821572876275898244038119 17732359314413847366057179)
    ·
      refine ⟨26598538971620771049085769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17732359314413847366057179 26598538971620771049085769)
      ·
        refine ⟨19948904228715578286814327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26598538971620771049085769 19948904228715578286814327)
        ·
          refine ⟨29923356343073367430221491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19948904228715578286814327 29923356343073367430221491)
          ·
            refine ⟨44885034514610051145332237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29923356343073367430221491 44885034514610051145332237)
            ·
              refine ⟨16831887942978769179499589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44885034514610051145332237 16831887942978769179499589)
              ·
                refine ⟨3155978989308519221156173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16831887942978769179499589 3155978989308519221156173)
                ·
                  refine ⟨1183492120990694707933565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3155978989308519221156173 1183492120990694707933565)
                  ·
                    refine ⟨443809545371510515475087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1183492120990694707933565 443809545371510515475087)
                    ·
                      rfl

theorem cell22_1296474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 3, 3].length) (baseStart_1296474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296474 prefixEnd_1296474 := by exact prefixLift 1296474
  have htrace : WordTrace (prefixWord ++ tailWord_1296474) baseStart_1296474 baseEnd_1296474 := by
    simpa [prefixWord, tailWord_1296474, baseEnd_1296474] using wordTrace_append hprefix tailTrace_1296474
  have hstable : (prefixWord ++ tailWord_1296474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296474).length < 2 ^ (prefixWord ++ tailWord_1296474).sum := by decide
  have hdescent : baseEnd_1296474 < baseStart_1296474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296476 : List Nat := [2, 2, 4, 1, 1, 4, 2, 6]
def baseStart_1296476 : Nat := 118140960795 + 1296476 * 2 ^ 59
def prefixEnd_1296476 : Nat := 4983230072969 + 3 ^ 40 * 1296476 * 2
def baseEnd_1296476 : Nat := 49312247779153686325009

theorem tailTrace_1296476 : CollatzResearch.WordTrace tailWord_1296476 prefixEnd_1296476 49312247779153686325009 := by
  unfold tailWord_1296476
  simp only [CollatzResearch.WordTrace]
  refine ⟨23643182225548173658862641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31524242967397564878483521 23643182225548173658862641)
  ·
    refine ⟨17732386669161130244146981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23643182225548173658862641 17732386669161130244146981)
    ·
      refine ⟨3324822500467711920777559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17732386669161130244146981 3324822500467711920777559)
      ·
        refine ⟨4987233750701567881166339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3324822500467711920777559 4987233750701567881166339)
        ·
          refine ⟨7480850626052351821749509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4987233750701567881166339 7480850626052351821749509)
          ·
            refine ⟨1402659492384815966578033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7480850626052351821749509 1402659492384815966578033)
            ·
              refine ⟨1051994619288611974933525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402659492384815966578033 1051994619288611974933525)
              ·
                refine ⟨49312247779153686325009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1051994619288611974933525 49312247779153686325009)
                ·
                  rfl

theorem cell22_1296476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 2, 6].length) (baseStart_1296476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296476 prefixEnd_1296476 := by exact prefixLift 1296476
  have htrace : WordTrace (prefixWord ++ tailWord_1296476) baseStart_1296476 baseEnd_1296476 := by
    simpa [prefixWord, tailWord_1296476, baseEnd_1296476] using wordTrace_append hprefix tailTrace_1296476
  have hstable : (prefixWord ++ tailWord_1296476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296476).length < 2 ^ (prefixWord ++ tailWord_1296476).sum := by decide
  have hdescent : baseEnd_1296476 < baseStart_1296476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296487 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 9]
def baseStart_1296487 : Nat := 118140960795 + 1296487 * 2 ^ 59
def prefixEnd_1296487 : Nat := 4983230072969 + 3 ^ 40 * 1296487 * 2
def baseEnd_1296487 : Nat := 147937998512394271633349

theorem tailTrace_1296487 : CollatzResearch.WordTrace tailWord_1296487 prefixEnd_1296487 147937998512394271633349 := by
  unfold tailWord_1296487
  simp only [CollatzResearch.WordTrace]
  refine ⟨47286765654056496196375715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31524510436037664130917143 47286765654056496196375715)
  ·
    refine ⟨70930148481084744294563573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47286765654056496196375715 70930148481084744294563573)
    ·
      refine ⟨6649701420101694777615335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70930148481084744294563573 6649701420101694777615335)
      ·
        refine ⟨9974552130152542166423003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6649701420101694777615335 9974552130152542166423003)
        ·
          refine ⟨14961828195228813249634505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9974552130152542166423003 14961828195228813249634505)
          ·
            refine ⟨11221371146421609937225879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14961828195228813249634505 11221371146421609937225879)
            ·
              refine ⟨16832056719632414905838819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11221371146421609937225879 16832056719632414905838819)
              ·
                refine ⟨25248085079448622358758229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16832056719632414905838819 25248085079448622358758229)
                ·
                  refine ⟨147937998512394271633349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25248085079448622358758229 147937998512394271633349)
                  ·
                    rfl

theorem cell22_1296487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 9].length) (baseStart_1296487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296487 prefixEnd_1296487 := by exact prefixLift 1296487
  have htrace : WordTrace (prefixWord ++ tailWord_1296487) baseStart_1296487 baseEnd_1296487 := by
    simpa [prefixWord, tailWord_1296487, baseEnd_1296487] using wordTrace_append hprefix tailTrace_1296487
  have hstable : (prefixWord ++ tailWord_1296487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296487).length < 2 ^ (prefixWord ++ tailWord_1296487).sum := by decide
  have hdescent : baseEnd_1296487 < baseStart_1296487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296581 : List Nat := [1, 3, 1, 1, 1, 1, 6, 3, 2, 3]
def baseStart_1296581 : Nat := 118140960795 + 1296581 * 2 ^ 59
def prefixEnd_1296581 : Nat := 4983230072969 + 3 ^ 40 * 1296581 * 2
def baseEnd_1296581 : Nat := 443846173658197903049759

theorem tailTrace_1296581 : CollatzResearch.WordTrace tailWord_1296581 prefixEnd_1296581 443846173658197903049759 := by
  unfold tailWord_1296581
  simp only [CollatzResearch.WordTrace]
  refine ⟨47290194115715950250297597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31526796077143966833531731 47290194115715950250297597)
  ·
    refine ⟨17733822793393481343861599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47290194115715950250297597 17733822793393481343861599)
    ·
      refine ⟨26600734190090222015792399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17733822793393481343861599 26600734190090222015792399)
      ·
        refine ⟨39901101285135333023688599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26600734190090222015792399 39901101285135333023688599)
        ·
          refine ⟨59851651927702999535532899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39901101285135333023688599 59851651927702999535532899)
          ·
            refine ⟨89777477891554499303299349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59851651927702999535532899 89777477891554499303299349)
            ·
              refine ⟨4208319276166617154842157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89777477891554499303299349 4208319276166617154842157)
              ·
                refine ⟨1578119728562481433065809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4208319276166617154842157 1578119728562481433065809)
                ·
                  refine ⟨1183589796421861074799357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1578119728562481433065809 1183589796421861074799357)
                  ·
                    refine ⟨443846173658197903049759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1183589796421861074799357 443846173658197903049759)
                    ·
                      rfl

theorem cell22_1296581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_1296581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296581 prefixEnd_1296581 := by exact prefixLift 1296581
  have htrace : WordTrace (prefixWord ++ tailWord_1296581) baseStart_1296581 baseEnd_1296581 := by
    simpa [prefixWord, tailWord_1296581, baseEnd_1296581] using wordTrace_append hprefix tailTrace_1296581
  have hstable : (prefixWord ++ tailWord_1296581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296581).length < 2 ^ (prefixWord ++ tailWord_1296581).sum := by decide
  have hdescent : baseEnd_1296581 < baseStart_1296581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296598 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 1, 5]
def baseStart_1296598 : Nat := 118140960795 + 1296598 * 2 ^ 59
def prefixEnd_1296598 : Nat := 4983230072969 + 3 ^ 40 * 1296598 * 2
def baseEnd_1296598 : Nat := 443851993105615525374707

theorem tailTrace_1296598 : CollatzResearch.WordTrace tailWord_1296598 prefixEnd_1296598 443851993105615525374707 := by
  unfold tailWord_1296598
  simp only [CollatzResearch.WordTrace]
  refine ⟨2955675884790897634604153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31527209437769574769110965 2955675884790897634604153)
  ·
    refine ⟨2216756913593173225953115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2955675884790897634604153 2216756913593173225953115)
    ·
      refine ⟨3325135370389759838929673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2216756913593173225953115 3325135370389759838929673)
      ·
        refine ⟨2493851527792319879197255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3325135370389759838929673 2493851527792319879197255)
        ·
          refine ⟨3740777291688479818795883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2493851527792319879197255 3740777291688479818795883)
          ·
            refine ⟨5611165937532719728193825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3740777291688479818795883 5611165937532719728193825)
            ·
              refine ⟨4208374453149539796145369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5611165937532719728193825 4208374453149539796145369)
              ·
                refine ⟨3156280839862154847109027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4208374453149539796145369 3156280839862154847109027)
                ·
                  refine ⟨4734421259793232270663541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156280839862154847109027 4734421259793232270663541)
                  ·
                    refine ⟨443851993105615525374707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4734421259793232270663541 443851993105615525374707)
                    ·
                      rfl

theorem cell22_1296598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_1296598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296598 prefixEnd_1296598 := by exact prefixLift 1296598
  have htrace : WordTrace (prefixWord ++ tailWord_1296598) baseStart_1296598 baseEnd_1296598 := by
    simpa [prefixWord, tailWord_1296598, baseEnd_1296598] using wordTrace_append hprefix tailTrace_1296598
  have hstable : (prefixWord ++ tailWord_1296598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296598).length < 2 ^ (prefixWord ++ tailWord_1296598).sum := by decide
  have hdescent : baseEnd_1296598 < baseStart_1296598 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296611 : List Nat := [1, 1, 1, 8, 1, 1, 9]
def baseStart_1296611 : Nat := 118140960795 + 1296611 * 2 ^ 59
def prefixEnd_1296611 : Nat := 4983230072969 + 3 ^ 40 * 1296611 * 2
def baseEnd_1296611 : Nat := 16439127528566215733321

theorem tailTrace_1296611 : CollatzResearch.WordTrace tailWord_1296611 prefixEnd_1296611 16439127528566215733321 := by
  unfold tailWord_1296611
  simp only [CollatzResearch.WordTrace]
  refine ⟨47291288305607265373889687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31527525537071510249259791 47291288305607265373889687)
  ·
    refine ⟨70936932458410898060834531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47291288305607265373889687 70936932458410898060834531)
    ·
      refine ⟨106405398687616347091251797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70936932458410898060834531 106405398687616347091251797)
      ·
        refine ⟨1246938265870504067475607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 106405398687616347091251797 1246938265870504067475607)
        ·
          refine ⟨1870407398805756101213411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1246938265870504067475607 1870407398805756101213411)
          ·
            refine ⟨2805611098208634151820117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870407398805756101213411 2805611098208634151820117)
            ·
              refine ⟨16439127528566215733321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2805611098208634151820117 16439127528566215733321)
              ·
                rfl

theorem cell22_1296611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 9].length) (baseStart_1296611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296611 prefixEnd_1296611 := by exact prefixLift 1296611
  have htrace : WordTrace (prefixWord ++ tailWord_1296611) baseStart_1296611 baseEnd_1296611 := by
    simpa [prefixWord, tailWord_1296611, baseEnd_1296611] using wordTrace_append hprefix tailTrace_1296611
  have hstable : (prefixWord ++ tailWord_1296611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296611).length < 2 ^ (prefixWord ++ tailWord_1296611).sum := by decide
  have hdescent : baseEnd_1296611 < baseStart_1296611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296615 : List Nat := [1, 1, 5, 3, 1, 3, 1, 2, 2, 3]
def baseStart_1296615 : Nat := 118140960795 + 1296615 * 2 ^ 59
def prefixEnd_1296615 : Nat := 4983230072969 + 3 ^ 40 * 1296615 * 2
def baseEnd_1296615 : Nat := 443857812553033147699655

theorem tailTrace_1296615 : CollatzResearch.WordTrace tailWord_1296615 prefixEnd_1296615 443857812553033147699655 := by
  unfold tailWord_1296615
  simp only [CollatzResearch.WordTrace]
  refine ⟨47291434197592774057035299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31527622798395182704690199 47291434197592774057035299)
  ·
    refine ⟨70937151296389161085552949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47291434197592774057035299 70937151296389161085552949)
    ·
      refine ⟨6650357934036483851770589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 70937151296389161085552949 6650357934036483851770589)
      ·
        refine ⟨2493884225263681444413971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6650357934036483851770589 2493884225263681444413971)
        ·
          refine ⟨3740826337895522166620957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2493884225263681444413971 3740826337895522166620957)
          ·
            refine ⟨1402809876710820812482859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3740826337895522166620957 1402809876710820812482859)
            ·
              refine ⟨2104214815066231218724289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1402809876710820812482859 2104214815066231218724289)
              ·
                refine ⟨1578161111299673414043217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2104214815066231218724289 1578161111299673414043217)
                ·
                  refine ⟨1183620833474755060532413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1578161111299673414043217 1183620833474755060532413)
                  ·
                    refine ⟨443857812553033147699655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1183620833474755060532413 443857812553033147699655)
                    ·
                      rfl

theorem cell22_1296615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_1296615 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296615 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296615 prefixEnd_1296615 := by exact prefixLift 1296615
  have htrace : WordTrace (prefixWord ++ tailWord_1296615) baseStart_1296615 baseEnd_1296615 := by
    simpa [prefixWord, tailWord_1296615, baseEnd_1296615] using wordTrace_append hprefix tailTrace_1296615
  have hstable : (prefixWord ++ tailWord_1296615).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296615).length < 2 ^ (prefixWord ++ tailWord_1296615).sum := by decide
  have hdescent : baseEnd_1296615 < baseStart_1296615 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296677 : List Nat := [1, 3, 1, 2, 5, 1, 3, 2, 1, 3]
def baseStart_1296677 : Nat := 118140960795 + 1296677 * 2 ^ 59
def prefixEnd_1296677 : Nat := 4983230072969 + 3 ^ 40 * 1296677 * 2
def baseEnd_1296677 : Nat := 443879036420085652649465

theorem tailTrace_1296677 : CollatzResearch.WordTrace tailWord_1296677 prefixEnd_1296677 443879036420085652649465 := by
  unfold tailWord_1296677
  simp only [CollatzResearch.WordTrace]
  refine ⟨47293695523368158645792285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31529130348912105763861523 47293695523368158645792285)
  ·
    refine ⟨17735135821263059492172107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47293695523368158645792285 17735135821263059492172107)
    ·
      refine ⟨26602703731894589238258161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17735135821263059492172107 26602703731894589238258161)
      ·
        refine ⟨19952027798920941928693621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26602703731894589238258161 19952027798920941928693621)
        ·
          refine ⟨1870502606148838305815027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19952027798920941928693621 1870502606148838305815027)
          ·
            refine ⟨2805753909223257458722541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870502606148838305815027 2805753909223257458722541)
            ·
              refine ⟨1052157715958721547020953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2805753909223257458722541 1052157715958721547020953)
              ·
                refine ⟨789118286969041160265715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052157715958721547020953 789118286969041160265715)
                ·
                  refine ⟨1183677430453561740398573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789118286969041160265715 1183677430453561740398573)
                  ·
                    refine ⟨443879036420085652649465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1183677430453561740398573 443879036420085652649465)
                    ·
                      rfl

theorem cell22_1296677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3, 2, 1, 3].length) (baseStart_1296677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296677 prefixEnd_1296677 := by exact prefixLift 1296677
  have htrace : WordTrace (prefixWord ++ tailWord_1296677) baseStart_1296677 baseEnd_1296677 := by
    simpa [prefixWord, tailWord_1296677, baseEnd_1296677] using wordTrace_append hprefix tailTrace_1296677
  have hstable : (prefixWord ++ tailWord_1296677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296677).length < 2 ^ (prefixWord ++ tailWord_1296677).sum := by decide
  have hdescent : baseEnd_1296677 < baseStart_1296677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296690 : List Nat := [3, 2, 1, 1, 5, 2, 2, 1, 5]
def baseStart_1296690 : Nat := 118140960795 + 1296690 * 2 ^ 59
def prefixEnd_1296690 : Nat := 4983230072969 + 3 ^ 40 * 1296690 * 2
def baseEnd_1296690 : Nat := 147961162195252650691475

theorem tailTrace_1296690 : CollatzResearch.WordTrace tailWord_1296690 prefixEnd_1296690 147961162195252650691475 := by
  unfold tailWord_1296690
  simp only [CollatzResearch.WordTrace]
  refine ⟨11823542418080265466503881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31529446448214041244010349 11823542418080265466503881)
  ·
    refine ⟨8867656813560199099877911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11823542418080265466503881 8867656813560199099877911)
    ·
      refine ⟨13301485220340298649816867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8867656813560199099877911 13301485220340298649816867)
      ·
        refine ⟨19952227830510447974725301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13301485220340298649816867 19952227830510447974725301)
        ·
          refine ⟨1870521359110354497630497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19952227830510447974725301 1870521359110354497630497)
          ·
            refine ⟨1402891019332765873222873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1870521359110354497630497 1402891019332765873222873)
            ·
              refine ⟨1052168264499574404917155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1402891019332765873222873 1052168264499574404917155)
              ·
                refine ⟨1578252396749361607375733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052168264499574404917155 1578252396749361607375733)
                ·
                  refine ⟨147961162195252650691475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1578252396749361607375733 147961162195252650691475)
                  ·
                    rfl

theorem cell22_1296690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_1296690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296690 prefixEnd_1296690 := by exact prefixLift 1296690
  have htrace : WordTrace (prefixWord ++ tailWord_1296690) baseStart_1296690 baseEnd_1296690 := by
    simpa [prefixWord, tailWord_1296690, baseEnd_1296690] using wordTrace_append hprefix tailTrace_1296690
  have hstable : (prefixWord ++ tailWord_1296690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296690).length < 2 ^ (prefixWord ++ tailWord_1296690).sum := by decide
  have hdescent : baseEnd_1296690 < baseStart_1296690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296716 : List Nat := [2, 2, 1, 3, 2, 1, 3, 2, 1, 5]
def baseStart_1296716 : Nat := 118140960795 + 1296716 * 2 ^ 59
def prefixEnd_1296716 : Nat := 4983230072969 + 3 ^ 40 * 1296716 * 2
def baseEnd_1296716 : Nat := 443892386917102550924345

theorem tailTrace_1296716 : CollatzResearch.WordTrace tailWord_1296716 prefixEnd_1296716 443892386917102550924345 := by
  unfold tailWord_1296716
  simp only [CollatzResearch.WordTrace]
  refine ⟨23647558985113434153231001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31530078646817912204308001 23647558985113434153231001)
  ·
    refine ⟨17735669238835075614923251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23647558985113434153231001 17735669238835075614923251)
    ·
      refine ⟨26603503858252613422384877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17735669238835075614923251 26603503858252613422384877)
      ·
        refine ⟨9976313946844730033394329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26603503858252613422384877 9976313946844730033394329)
        ·
          refine ⟨7482235460133547525045747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9976313946844730033394329 7482235460133547525045747)
          ·
            refine ⟨11223353190200321287568621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7482235460133547525045747 11223353190200321287568621)
            ·
              refine ⟨4208757446325120482838233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11223353190200321287568621 4208757446325120482838233)
              ·
                refine ⟨3156568084743840362128675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4208757446325120482838233 3156568084743840362128675)
                ·
                  refine ⟨4734852127115760543193013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3156568084743840362128675 4734852127115760543193013)
                  ·
                    refine ⟨443892386917102550924345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4734852127115760543193013 443892386917102550924345)
                    ·
                      rfl

theorem cell22_1296716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_1296716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296716 prefixEnd_1296716 := by exact prefixLift 1296716
  have htrace : WordTrace (prefixWord ++ tailWord_1296716) baseStart_1296716 baseEnd_1296716 := by
    simpa [prefixWord, tailWord_1296716, baseEnd_1296716] using wordTrace_append hprefix tailTrace_1296716
  have hstable : (prefixWord ++ tailWord_1296716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296716).length < 2 ^ (prefixWord ++ tailWord_1296716).sum := by decide
  have hdescent : baseEnd_1296716 < baseStart_1296716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296853 : List Nat := [1, 3, 2, 3, 1, 2, 3, 1, 6]
def baseStart_1296853 : Nat := 118140960795 + 1296853 * 2 ^ 59
def prefixEnd_1296853 : Nat := 4983230072969 + 3 ^ 40 * 1296853 * 2
def baseEnd_1296853 : Nat := 147979761605626620082975

theorem tailTrace_1296853 : CollatzResearch.WordTrace tailWord_1296853 prefixEnd_1296853 147979761605626620082975 := by
  unfold tailWord_1296853
  simp only [CollatzResearch.WordTrace]
  refine ⟨47300114770730540704199213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31533409847153693802799475 47300114770730540704199213)
  ·
    refine ⟨17737543039023952764074705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47300114770730540704199213 17737543039023952764074705)
    ·
      refine ⟨13303157279267964573056029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17737543039023952764074705 13303157279267964573056029)
      ·
        refine ⟨4988683979725486714896011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13303157279267964573056029 4988683979725486714896011)
        ·
          refine ⟨7483025969588230072344017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4988683979725486714896011 7483025969588230072344017)
          ·
            refine ⟨5612269477191172554258013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7483025969588230072344017 5612269477191172554258013)
            ·
              refine ⟨2104601053946689707846755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5612269477191172554258013 2104601053946689707846755)
              ·
                refine ⟨3156901580920034561770133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104601053946689707846755 3156901580920034561770133)
                ·
                  refine ⟨147979761605626620082975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3156901580920034561770133 147979761605626620082975)
                  ·
                    rfl

theorem cell22_1296853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_1296853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296853 prefixEnd_1296853 := by exact prefixLift 1296853
  have htrace : WordTrace (prefixWord ++ tailWord_1296853) baseStart_1296853 baseEnd_1296853 := by
    simpa [prefixWord, tailWord_1296853, baseEnd_1296853] using wordTrace_append hprefix tailTrace_1296853
  have hstable : (prefixWord ++ tailWord_1296853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296853).length < 2 ^ (prefixWord ++ tailWord_1296853).sum := by decide
  have hdescent : baseEnd_1296853 < baseStart_1296853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296881 : List Nat := [1, 2, 2, 2, 3, 1, 1, 10]
def baseStart_1296881 : Nat := 118140960795 + 1296881 * 2 ^ 59
def prefixEnd_1296881 : Nat := 4983230072969 + 3 ^ 40 * 1296881 * 2
def baseEnd_1296881 : Nat := 49327652198788568949871

theorem tailTrace_1296881 : CollatzResearch.WordTrace tailWord_1296881 prefixEnd_1296881 49327652198788568949871 := by
  unfold tailWord_1296881
  simp only [CollatzResearch.WordTrace]
  refine ⟨47301136014629101486218497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31534090676419400990812331 47301136014629101486218497)
  ·
    refine ⟨35475852010971826114663873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47301136014629101486218497 35475852010971826114663873)
    ·
      refine ⟨26606889008228869585997905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35475852010971826114663873 26606889008228869585997905)
      ·
        refine ⟨19955166756171652189498429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26606889008228869585997905 19955166756171652189498429)
        ·
          refine ⟨7483187533564369571061911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19955166756171652189498429 7483187533564369571061911)
          ·
            refine ⟨11224781300346554356592867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7483187533564369571061911 11224781300346554356592867)
            ·
              refine ⟨16837171950519831534889301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11224781300346554356592867 16837171950519831534889301)
              ·
                refine ⟨49327652198788568949871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16837171950519831534889301 49327652198788568949871)
                ·
                  rfl

theorem cell22_1296881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 10].length) (baseStart_1296881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296881 prefixEnd_1296881 := by exact prefixLift 1296881
  have htrace : WordTrace (prefixWord ++ tailWord_1296881) baseStart_1296881 baseEnd_1296881 := by
    simpa [prefixWord, tailWord_1296881, baseEnd_1296881] using wordTrace_append hprefix tailTrace_1296881
  have hstable : (prefixWord ++ tailWord_1296881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296881).length < 2 ^ (prefixWord ++ tailWord_1296881).sum := by decide
  have hdescent : baseEnd_1296881 < baseStart_1296881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296883 : List Nat := [1, 1, 1, 2, 2, 2, 6, 1, 2, 4]
def baseStart_1296883 : Nat := 118140960795 + 1296883 * 2 ^ 59
def prefixEnd_1296883 : Nat := 4983230072969 + 3 ^ 40 * 1296883 * 2
def baseEnd_1296883 : Nat := 443949554429969781998833

theorem tailTrace_1296883 : CollatzResearch.WordTrace tailWord_1296883 prefixEnd_1296883 443949554429969781998833 := by
  unfold tailWord_1296883
  simp only [CollatzResearch.WordTrace]
  refine ⟨47301208960621855827791303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31534139307081237218527535 47301208960621855827791303)
  ·
    refine ⟨70951813440932783741686955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47301208960621855827791303 70951813440932783741686955)
    ·
      refine ⟨106427720161399175612530433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70951813440932783741686955 106427720161399175612530433)
      ·
        refine ⟨79820790121049381709397825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106427720161399175612530433 79820790121049381709397825)
        ·
          refine ⟨59865592590787036282048369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79820790121049381709397825 59865592590787036282048369)
          ·
            refine ⟨44899194443090277211536277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 59865592590787036282048369 44899194443090277211536277)
            ·
              refine ⟨2104649739519856744290763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44899194443090277211536277 2104649739519856744290763)
              ·
                refine ⟨3156974609279785116436145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104649739519856744290763 3156974609279785116436145)
                ·
                  refine ⟨2367730956959838837327109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3156974609279785116436145 2367730956959838837327109)
                  ·
                    refine ⟨443949554429969781998833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2367730956959838837327109 443949554429969781998833)
                    ·
                      rfl

theorem cell22_1296883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 4].length) (baseStart_1296883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296883 prefixEnd_1296883 := by exact prefixLift 1296883
  have htrace : WordTrace (prefixWord ++ tailWord_1296883) baseStart_1296883 baseEnd_1296883 := by
    simpa [prefixWord, tailWord_1296883, baseEnd_1296883] using wordTrace_append hprefix tailTrace_1296883
  have hstable : (prefixWord ++ tailWord_1296883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296883).length < 2 ^ (prefixWord ++ tailWord_1296883).sum := by decide
  have hdescent : baseEnd_1296883 < baseStart_1296883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296898 : List Nat := [3, 4, 1, 2, 12]
def baseStart_1296898 : Nat := 118140960795 + 1296898 * 2 ^ 59
def prefixEnd_1296898 : Nat := 4983230072969 + 3 ^ 40 * 1296898 * 2
def baseEnd_1296898 : Nat := 1826974029779896061209

theorem tailTrace_1296898 : CollatzResearch.WordTrace tailWord_1296898 prefixEnd_1296898 1826974029779896061209 := by
  unfold tailWord_1296898
  simp only [CollatzResearch.WordTrace]
  refine ⟨11825439013891878347396837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31534504037045008926391565 11825439013891878347396837)
  ·
    refine ⟨2217269815104727190136907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11825439013891878347396837 2217269815104727190136907)
    ·
      refine ⟨3325904722657090785205361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2217269815104727190136907 3325904722657090785205361)
      ·
        refine ⟨2494428541992818088904021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3325904722657090785205361 2494428541992818088904021)
        ·
          refine ⟨1826974029779896061209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 2494428541992818088904021 1826974029779896061209)
          ·
            rfl

theorem cell22_1296898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 12].length) (baseStart_1296898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296898 prefixEnd_1296898 := by exact prefixLift 1296898
  have htrace : WordTrace (prefixWord ++ tailWord_1296898) baseStart_1296898 baseEnd_1296898 := by
    simpa [prefixWord, tailWord_1296898, baseEnd_1296898] using wordTrace_append hprefix tailTrace_1296898
  have hstable : (prefixWord ++ tailWord_1296898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296898).length < 2 ^ (prefixWord ++ tailWord_1296898).sum := by decide
  have hdescent : baseEnd_1296898 < baseStart_1296898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296900 : List Nat := [2, 3, 2, 3, 1, 1, 2, 2, 2, 4]
def baseStart_1296900 : Nat := 118140960795 + 1296900 * 2 ^ 59
def prefixEnd_1296900 : Nat := 4983230072969 + 3 ^ 40 * 1296900 * 2
def baseEnd_1296900 : Nat := 443955373877387404323781

theorem tailTrace_1296900 : CollatzResearch.WordTrace tailWord_1296900 prefixEnd_1296900 443955373877387404323781 := by
  unfold tailWord_1296900
  simp only [CollatzResearch.WordTrace]
  refine ⟨23650914500780133865580077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31534552667706845154106769 23650914500780133865580077)
  ·
    refine ⟨8869092937792550199592529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23650914500780133865580077 8869092937792550199592529)
    ·
      refine ⟨6651819703344412649694397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8869092937792550199592529 6651819703344412649694397)
      ·
        refine ⟨2494432388754154743635399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6651819703344412649694397 2494432388754154743635399)
        ·
          refine ⟨3741648583131232115453099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2494432388754154743635399 3741648583131232115453099)
          ·
            refine ⟨5612472874696848173179649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3741648583131232115453099 5612472874696848173179649)
            ·
              refine ⟨4209354656022636129884737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5612472874696848173179649 4209354656022636129884737)
              ·
                refine ⟨3157015992016977097413553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4209354656022636129884737 3157015992016977097413553)
                ·
                  refine ⟨2367761994012732823060165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3157015992016977097413553 2367761994012732823060165)
                  ·
                    refine ⟨443955373877387404323781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2367761994012732823060165 443955373877387404323781)
                    ·
                      rfl

theorem cell22_1296900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_1296900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296900 prefixEnd_1296900 := by exact prefixLift 1296900
  have htrace : WordTrace (prefixWord ++ tailWord_1296900) baseStart_1296900 baseEnd_1296900 := by
    simpa [prefixWord, tailWord_1296900, baseEnd_1296900] using wordTrace_append hprefix tailTrace_1296900
  have hstable : (prefixWord ++ tailWord_1296900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296900).length < 2 ^ (prefixWord ++ tailWord_1296900).sum := by decide
  have hdescent : baseEnd_1296900 < baseStart_1296900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296911 : List Nat := [1, 1, 2, 1, 1, 1, 2, 5, 2, 6]
def baseStart_1296911 : Nat := 118140960795 + 1296911 * 2 ^ 59
def prefixEnd_1296911 : Nat := 4983230072969 + 3 ^ 40 * 1296911 * 2
def baseEnd_1296911 : Nat := 443959139402187042298747

theorem tailTrace_1296911 : CollatzResearch.WordTrace tailWord_1296911 prefixEnd_1296911 443959139402187042298747 := by
  unfold tailWord_1296911
  simp only [CollatzResearch.WordTrace]
  refine ⟨47302230204520416609810587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31534820136346944406540391 47302230204520416609810587)
  ·
    refine ⟨70953345306780624914715881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47302230204520416609810587 70953345306780624914715881)
    ·
      refine ⟨53215008980085468686036911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70953345306780624914715881 53215008980085468686036911)
      ·
        refine ⟨79822513470128203029055367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53215008980085468686036911 79822513470128203029055367)
        ·
          refine ⟨119733770205192304543583051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79822513470128203029055367 119733770205192304543583051)
          ·
            refine ⟨179600655307788456815374577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119733770205192304543583051 179600655307788456815374577)
            ·
              refine ⟨134700491480841342611530933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179600655307788456815374577 134700491480841342611530933)
              ·
                refine ⟨12628171076328875869831025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134700491480841342611530933 12628171076328875869831025)
                ·
                  refine ⟨9471128307246656902373269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12628171076328875869831025 9471128307246656902373269)
                  ·
                    refine ⟨443959139402187042298747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9471128307246656902373269 443959139402187042298747)
                    ·
                      rfl

theorem cell22_1296911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 6].length) (baseStart_1296911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296911 prefixEnd_1296911 := by exact prefixLift 1296911
  have htrace : WordTrace (prefixWord ++ tailWord_1296911) baseStart_1296911 baseEnd_1296911 := by
    simpa [prefixWord, tailWord_1296911, baseEnd_1296911] using wordTrace_append hprefix tailTrace_1296911
  have hstable : (prefixWord ++ tailWord_1296911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296911).length < 2 ^ (prefixWord ++ tailWord_1296911).sum := by decide
  have hdescent : baseEnd_1296911 < baseStart_1296911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296932 : List Nat := [2, 3, 1, 5, 1, 1, 3, 6]
def baseStart_1296932 : Nat := 118140960795 + 1296932 * 2 ^ 59
def prefixEnd_1296932 : Nat := 4983230072969 + 3 ^ 40 * 1296932 * 2
def baseEnd_1296932 : Nat := 49329592014594443058187

theorem tailTrace_1296932 : CollatzResearch.WordTrace tailWord_1296932 prefixEnd_1296932 49329592014594443058187 := by
  unfold tailWord_1296932
  simp only [CollatzResearch.WordTrace]
  refine ⟨23651498068722168598162525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31535330758296224797550033 23651498068722168598162525)
  ·
    refine ⟨8869311775770813224310947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23651498068722168598162525 8869311775770813224310947)
    ·
      refine ⟨13303967663656219836466421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8869311775770813224310947 13303967663656219836466421)
      ·
        refine ⟨1247246968467770609668727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13303967663656219836466421 1247246968467770609668727)
        ·
          refine ⟨1870870452701655914503091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1247246968467770609668727 1870870452701655914503091)
          ·
            refine ⟨2806305679052483871754637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1870870452701655914503091 2806305679052483871754637)
            ·
              refine ⟨1052364629644681451907989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2806305679052483871754637 1052364629644681451907989)
              ·
                refine ⟨49329592014594443058187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1052364629644681451907989 49329592014594443058187)
                ·
                  rfl

theorem cell22_1296932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 3, 6].length) (baseStart_1296932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296932 prefixEnd_1296932 := by exact prefixLift 1296932
  have htrace : WordTrace (prefixWord ++ tailWord_1296932) baseStart_1296932 baseEnd_1296932 := by
    simpa [prefixWord, tailWord_1296932, baseEnd_1296932] using wordTrace_append hprefix tailTrace_1296932
  have hstable : (prefixWord ++ tailWord_1296932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296932).length < 2 ^ (prefixWord ++ tailWord_1296932).sum := by decide
  have hdescent : baseEnd_1296932 < baseStart_1296932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1296947 : List Nat := [1, 1, 1, 2, 4, 2, 4, 3, 1, 3]
def baseStart_1296947 : Nat := 118140960795 + 1296947 * 2 ^ 59
def prefixEnd_1296947 : Nat := 4983230072969 + 3 ^ 40 * 1296947 * 2
def baseEnd_1296947 : Nat := 443971462937894948398637

theorem tailTrace_1296947 : CollatzResearch.WordTrace tailWord_1296947 prefixEnd_1296947 443971462937894948398637 := by
  unfold tailWord_1296947
  simp only [CollatzResearch.WordTrace]
  refine ⟨47303543232389994758121095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31535695488259996505414063 47303543232389994758121095)
  ·
    refine ⟨70955314848584992137181643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47303543232389994758121095 70955314848584992137181643)
    ·
      refine ⟨106432972272877488205772465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70955314848584992137181643 106432972272877488205772465)
      ·
        refine ⟨79824729204658116154329349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106432972272877488205772465 79824729204658116154329349)
        ·
          refine ⟨14967136725873396778936753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79824729204658116154329349 14967136725873396778936753)
          ·
            refine ⟨11225352544405047584202565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14967136725873396778936753 11225352544405047584202565)
            ·
              refine ⟨2104753602075946422037981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11225352544405047584202565 2104753602075946422037981)
              ·
                refine ⟨789282600778479908264243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2104753602075946422037981 789282600778479908264243)
                ·
                  refine ⟨1183923901167719862396365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789282600778479908264243 1183923901167719862396365)
                  ·
                    refine ⟨443971462937894948398637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1183923901167719862396365 443971462937894948398637)
                    ·
                      rfl

theorem cell22_1296947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 3, 1, 3].length) (baseStart_1296947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1296947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1296947 prefixEnd_1296947 := by exact prefixLift 1296947
  have htrace : WordTrace (prefixWord ++ tailWord_1296947) baseStart_1296947 baseEnd_1296947 := by
    simpa [prefixWord, tailWord_1296947, baseEnd_1296947] using wordTrace_append hprefix tailTrace_1296947
  have hstable : (prefixWord ++ tailWord_1296947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1296947).length < 2 ^ (prefixWord ++ tailWord_1296947).sum := by decide
  have hdescent : baseEnd_1296947 < baseStart_1296947 := by decide
  rcases family_descends (prefixWord ++ tailWord_1296947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297020 : List Nat := [2, 2, 2, 1, 1, 2, 4, 1, 4, 3]
def baseStart_1297020 : Nat := 118140960795 + 1297020 * 2 ^ 59
def prefixEnd_1297020 : Nat := 4983230072969 + 3 ^ 40 * 1297020 * 2
def baseEnd_1297020 : Nat := 443996452329747091323413

theorem tailTrace_1297020 : CollatzResearch.WordTrace tailWord_1297020 prefixEnd_1297020 443996452329747091323413 := by
  unfold tailWord_1297020
  simp only [CollatzResearch.WordTrace]
  refine ⟨23653102880562764112764257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31537470507417018817019009 23653102880562764112764257)
  ·
    refine ⟨17739827160422073084573193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23653102880562764112764257 17739827160422073084573193)
    ·
      refine ⟨13304870370316554813429895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17739827160422073084573193 13304870370316554813429895)
      ·
        refine ⟨19957305555474832220144843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13304870370316554813429895 19957305555474832220144843)
        ·
          refine ⟨29935958333212248330217265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19957305555474832220144843 29935958333212248330217265)
          ·
            refine ⟨22451968749909186247662949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29935958333212248330217265 22451968749909186247662949)
            ·
              refine ⟨4209744140607972421436803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22451968749909186247662949 4209744140607972421436803)
              ·
                refine ⟨6314616210911958632155205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4209744140607972421436803 6314616210911958632155205)
                ·
                  refine ⟨1183990539545992243529101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6314616210911958632155205 1183990539545992243529101)
                  ·
                    refine ⟨443996452329747091323413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1183990539545992243529101 443996452329747091323413)
                    ·
                      rfl

theorem cell22_1297020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 1, 4, 3].length) (baseStart_1297020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297020 prefixEnd_1297020 := by exact prefixLift 1297020
  have htrace : WordTrace (prefixWord ++ tailWord_1297020) baseStart_1297020 baseEnd_1297020 := by
    simpa [prefixWord, tailWord_1297020, baseEnd_1297020] using wordTrace_append hprefix tailTrace_1297020
  have hstable : (prefixWord ++ tailWord_1297020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297020).length < 2 ^ (prefixWord ++ tailWord_1297020).sum := by decide
  have hdescent : baseEnd_1297020 < baseStart_1297020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297052 : List Nat := [2, 2, 3, 2, 2, 2, 2, 1, 2, 4]
def baseStart_1297052 : Nat := 118140960795 + 1297052 * 2 ^ 59
def prefixEnd_1297052 : Nat := 4983230072969 + 3 ^ 40 * 1297052 * 2
def baseEnd_1297052 : Nat := 444007406583709674523315

theorem tailTrace_1297052 : CollatzResearch.WordTrace tailWord_1297052 prefixEnd_1297052 444007406583709674523315 := by
  unfold tailWord_1297052
  simp only [CollatzResearch.WordTrace]
  refine ⟨23653686448504798845346705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31538248598006398460462273 23653686448504798845346705)
  ·
    refine ⟨17740264836378599134010029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23653686448504798845346705 17740264836378599134010029)
    ·
      refine ⟨6652599313641974675253761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17740264836378599134010029 6652599313641974675253761)
      ·
        refine ⟨4989449485231481006440321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6652599313641974675253761 4989449485231481006440321)
        ·
          refine ⟨3742087113923610754830241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4989449485231481006440321 3742087113923610754830241)
          ·
            refine ⟨2806565335442708066122681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3742087113923610754830241 2806565335442708066122681)
            ·
              refine ⟨2104924001582031049592011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2806565335442708066122681 2104924001582031049592011)
              ·
                refine ⟨3157386002373046574388017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2104924001582031049592011 3157386002373046574388017)
                ·
                  refine ⟨2368039501779784930791013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3157386002373046574388017 2368039501779784930791013)
                  ·
                    refine ⟨444007406583709674523315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2368039501779784930791013 444007406583709674523315)
                    ·
                      rfl

theorem cell22_1297052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_1297052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297052 prefixEnd_1297052 := by exact prefixLift 1297052
  have htrace : WordTrace (prefixWord ++ tailWord_1297052) baseStart_1297052 baseEnd_1297052 := by
    simpa [prefixWord, tailWord_1297052, baseEnd_1297052] using wordTrace_append hprefix tailTrace_1297052
  have hstable : (prefixWord ++ tailWord_1297052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297052).length < 2 ^ (prefixWord ++ tailWord_1297052).sum := by decide
  have hdescent : baseEnd_1297052 < baseStart_1297052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297073 : List Nat := [1, 2, 2, 6, 2, 1, 2, 2, 4]
def baseStart_1297073 : Nat := 118140960795 + 1297073 * 2 ^ 59
def prefixEnd_1297073 : Nat := 4983230072969 + 3 ^ 40 * 1297073 * 2
def baseEnd_1297073 : Nat := 148004865104290873249417

theorem tailTrace_1297073 : CollatzResearch.WordTrace tailWord_1297073 prefixEnd_1297073 148004865104290873249417 := by
  unfold tailWord_1297073
  simp only [CollatzResearch.WordTrace]
  refine ⟨47308138829933518277207873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31538759219955678851471915 47308138829933518277207873)
  ·
    refine ⟨35481104122450138707905905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47308138829933518277207873 35481104122450138707905905)
    ·
      refine ⟨26610828091837604030929429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35481104122450138707905905 26610828091837604030929429)
      ·
        refine ⟨1247382566804887688949817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26610828091837604030929429 1247382566804887688949817)
        ·
          refine ⟨935536925103665766712363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1247382566804887688949817 935536925103665766712363)
          ·
            refine ⟨1403305387655498650068545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935536925103665766712363 1403305387655498650068545)
            ·
              refine ⟨1052479040741623987551409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1403305387655498650068545 1052479040741623987551409)
              ·
                refine ⟨789359280556217990663557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052479040741623987551409 789359280556217990663557)
                ·
                  refine ⟨148004865104290873249417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 789359280556217990663557 148004865104290873249417)
                  ·
                    rfl

theorem cell22_1297073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 2, 4].length) (baseStart_1297073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297073 prefixEnd_1297073 := by exact prefixLift 1297073
  have htrace : WordTrace (prefixWord ++ tailWord_1297073) baseStart_1297073 baseEnd_1297073 := by
    simpa [prefixWord, tailWord_1297073, baseEnd_1297073] using wordTrace_append hprefix tailTrace_1297073
  have hstable : (prefixWord ++ tailWord_1297073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297073).length < 2 ^ (prefixWord ++ tailWord_1297073).sum := by decide
  have hdescent : baseEnd_1297073 < baseStart_1297073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297116 : List Nat := [2, 2, 5, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1297116 : Nat := 118140960795 + 1297116 * 2 ^ 59
def prefixEnd_1297116 : Nat := 4983230072969 + 3 ^ 40 * 1297116 * 2
def baseEnd_1297116 : Nat := 444029315091634840923119

theorem tailTrace_1297116 : CollatzResearch.WordTrace tailWord_1297116 prefixEnd_1297116 444029315091634840923119 := by
  unfold tailWord_1297116
  simp only [CollatzResearch.WordTrace]
  refine ⟨23654853584388868310511601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31539804779185157747348801 23654853584388868310511601)
  ·
    refine ⟨17741140188291651232883701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23654853584388868310511601 17741140188291651232883701)
    ·
      refine ⟨1663231892652342303082847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17741140188291651232883701 1663231892652342303082847)
      ·
        refine ⟨2494847838978513454624271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1663231892652342303082847 2494847838978513454624271)
        ·
          refine ⟨3742271758467770181936407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2494847838978513454624271 3742271758467770181936407)
          ·
            refine ⟨5613407637701655272904611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3742271758467770181936407 5613407637701655272904611)
            ·
              refine ⟨8420111456552482909356917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5613407637701655272904611 8420111456552482909356917)
              ·
                refine ⟨789385449051795272752211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8420111456552482909356917 789385449051795272752211)
                ·
                  refine ⟨1184078173577692909128317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789385449051795272752211 1184078173577692909128317)
                  ·
                    refine ⟨444029315091634840923119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1184078173577692909128317 444029315091634840923119)
                    ·
                      rfl

theorem cell22_1297116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1297116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297116 prefixEnd_1297116 := by exact prefixLift 1297116
  have htrace : WordTrace (prefixWord ++ tailWord_1297116) baseStart_1297116 baseEnd_1297116 := by
    simpa [prefixWord, tailWord_1297116, baseEnd_1297116] using wordTrace_append hprefix tailTrace_1297116
  have hstable : (prefixWord ++ tailWord_1297116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297116).length < 2 ^ (prefixWord ++ tailWord_1297116).sum := by decide
  have hdescent : baseEnd_1297116 < baseStart_1297116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297159 : List Nat := [1, 1, 4, 4, 1, 2, 2, 2, 1, 4]
def baseStart_1297159 : Nat := 118140960795 + 1297159 * 2 ^ 59
def prefixEnd_1297159 : Nat := 4983230072969 + 3 ^ 40 * 1297159 * 2
def baseEnd_1297159 : Nat := 444044034870397062097987

theorem tailTrace_1297159 : CollatzResearch.WordTrace tailWord_1297159 prefixEnd_1297159 444044034870397062097987 := by
  unfold tailWord_1297159
  simp only [CollatzResearch.WordTrace]
  refine ⟨47311275507621954964838531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31540850338414636643225687 47311275507621954964838531)
  ·
    refine ⟨70966913261432932447257797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47311275507621954964838531 70966913261432932447257797)
    ·
      refine ⟨13306296236518674833860837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 70966913261432932447257797 13306296236518674833860837)
      ·
        refine ⟨2494930544347251531348907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13306296236518674833860837 2494930544347251531348907)
        ·
          refine ⟨3742395816520877297023361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2494930544347251531348907 3742395816520877297023361)
          ·
            refine ⟨2806796862390657972767521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3742395816520877297023361 2806796862390657972767521)
            ·
              refine ⟨2105097646792993479575641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2806796862390657972767521 2105097646792993479575641)
              ·
                refine ⟨1578823235094745109681731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2105097646792993479575641 1578823235094745109681731)
                ·
                  refine ⟨2368234852642117664522597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1578823235094745109681731 2368234852642117664522597)
                  ·
                    refine ⟨444044034870397062097987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2368234852642117664522597 444044034870397062097987)
                    ·
                      rfl

theorem cell22_1297159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 4].length) (baseStart_1297159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297159 prefixEnd_1297159 := by exact prefixLift 1297159
  have htrace : WordTrace (prefixWord ++ tailWord_1297159) baseStart_1297159 baseEnd_1297159 := by
    simpa [prefixWord, tailWord_1297159, baseEnd_1297159] using wordTrace_append hprefix tailTrace_1297159
  have hstable : (prefixWord ++ tailWord_1297159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297159).length < 2 ^ (prefixWord ++ tailWord_1297159).sum := by decide
  have hdescent : baseEnd_1297159 < baseStart_1297159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297230 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 9]
def baseStart_1297230 : Nat := 118140960795 + 1297230 * 2 ^ 59
def prefixEnd_1297230 : Nat := 4983230072969 + 3 ^ 40 * 1297230 * 2
def baseEnd_1297230 : Nat := 148022779873792181190923

theorem tailTrace_1297230 : CollatzResearch.WordTrace tailWord_1297230 prefixEnd_1297230 148022779873792181190923 := by
  unfold tailWord_1297230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5914233136295591761334143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31542576726909822727115429 5914233136295591761334143)
  ·
    refine ⟨8871349704443387642001215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5914233136295591761334143 8871349704443387642001215)
    ·
      refine ⟨13307024556665081463001823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8871349704443387642001215 13307024556665081463001823)
      ·
        refine ⟨19960536834997622194502735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13307024556665081463001823 19960536834997622194502735)
        ·
          refine ⟨29940805252496433291754103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19960536834997622194502735 29940805252496433291754103)
          ·
            refine ⟨44911207878744649937631155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29940805252496433291754103 44911207878744649937631155)
            ·
              refine ⟨67366811818116974906446733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44911207878744649937631155 67366811818116974906446733)
              ·
                refine ⟨25262554431793865589917525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 67366811818116974906446733 25262554431793865589917525)
                ·
                  refine ⟨148022779873792181190923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 25262554431793865589917525 148022779873792181190923)
                  ·
                    rfl

theorem cell22_1297230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_1297230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297230 prefixEnd_1297230 := by exact prefixLift 1297230
  have htrace : WordTrace (prefixWord ++ tailWord_1297230) baseStart_1297230 baseEnd_1297230 := by
    simpa [prefixWord, tailWord_1297230, baseEnd_1297230] using wordTrace_append hprefix tailTrace_1297230
  have hstable : (prefixWord ++ tailWord_1297230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297230).length < 2 ^ (prefixWord ++ tailWord_1297230).sum := by decide
  have hdescent : baseEnd_1297230 < baseStart_1297230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297247 : List Nat := [1, 1, 2, 3, 1, 3, 4, 2, 5]
def baseStart_1297247 : Nat := 118140960795 + 1297247 * 2 ^ 59
def prefixEnd_1297247 : Nat := 4983230072969 + 3 ^ 40 * 1297247 * 2
def baseEnd_1297247 : Nat := 148024719689598055299239

theorem tailTrace_1297247 : CollatzResearch.WordTrace tailWord_1297247 prefixEnd_1297247 148024719689598055299239 := by
  unfold tailWord_1297247
  simp only [CollatzResearch.WordTrace]
  refine ⟨47314485131303145994041995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31542990087535430662694663 47314485131303145994041995)
  ·
    refine ⟨70971727696954718991062993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47314485131303145994041995 70971727696954718991062993)
    ·
      refine ⟨53228795772716039243297245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70971727696954718991062993 53228795772716039243297245)
      ·
        refine ⟨19960798414768514716236467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53228795772716039243297245 19960798414768514716236467)
        ·
          refine ⟨29941197622152772074354701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19960798414768514716236467 29941197622152772074354701)
          ·
            refine ⟨11227949108307289527883013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29941197622152772074354701 11227949108307289527883013)
            ·
              refine ⟨2105240457807616786478065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11227949108307289527883013 2105240457807616786478065)
              ·
                refine ⟨1578930343355712589858549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2105240457807616786478065 1578930343355712589858549)
                ·
                  refine ⟨148024719689598055299239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1578930343355712589858549 148024719689598055299239)
                  ·
                    rfl

theorem cell22_1297247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 4, 2, 5].length) (baseStart_1297247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297247 prefixEnd_1297247 := by exact prefixLift 1297247
  have htrace : WordTrace (prefixWord ++ tailWord_1297247) baseStart_1297247 baseEnd_1297247 := by
    simpa [prefixWord, tailWord_1297247, baseEnd_1297247] using wordTrace_append hprefix tailTrace_1297247
  have hstable : (prefixWord ++ tailWord_1297247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297247).length < 2 ^ (prefixWord ++ tailWord_1297247).sum := by decide
  have hdescent : baseEnd_1297247 < baseStart_1297247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297251 : List Nat := [1, 1, 1, 5, 3, 2, 1, 4, 1, 3]
def baseStart_1297251 : Nat := 118140960795 + 1297251 * 2 ^ 59
def prefixEnd_1297251 : Nat := 4983230072969 + 3 ^ 40 * 1297251 * 2
def baseEnd_1297251 : Nat := 444075528350539488797705

theorem tailTrace_1297251 : CollatzResearch.WordTrace tailWord_1297251 prefixEnd_1297251 444075528350539488797705 := by
  unfold tailWord_1297251
  simp only [CollatzResearch.WordTrace]
  refine ⟨47314631023288654677187607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31543087348859103118125071 47314631023288654677187607)
  ·
    refine ⟨70971946534932982015781411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47314631023288654677187607 70971946534932982015781411)
    ·
      refine ⟨106457919802399473023672117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70971946534932982015781411 106457919802399473023672117)
      ·
        refine ⟨9980429981474950595969261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 106457919802399473023672117 9980429981474950595969261)
        ·
          refine ⟨3742661243053106473488473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9980429981474950595969261 3742661243053106473488473)
          ·
            refine ⟨2806995932289829855116355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3742661243053106473488473 2806995932289829855116355)
            ·
              refine ⟨4210493898434744782674533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2806995932289829855116355 4210493898434744782674533)
              ·
                refine ⟨789467605956514646751475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4210493898434744782674533 789467605956514646751475)
                ·
                  refine ⟨1184201408934771970127213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789467605956514646751475 1184201408934771970127213)
                  ·
                    refine ⟨444075528350539488797705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1184201408934771970127213 444075528350539488797705)
                    ·
                      rfl

theorem cell22_1297251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 4, 1, 3].length) (baseStart_1297251 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297251 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297251 prefixEnd_1297251 := by exact prefixLift 1297251
  have htrace : WordTrace (prefixWord ++ tailWord_1297251) baseStart_1297251 baseEnd_1297251 := by
    simpa [prefixWord, tailWord_1297251, baseEnd_1297251] using wordTrace_append hprefix tailTrace_1297251
  have hstable : (prefixWord ++ tailWord_1297251).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297251).length < 2 ^ (prefixWord ++ tailWord_1297251).sum := by decide
  have hdescent : baseEnd_1297251 < baseStart_1297251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297275 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 8]
def baseStart_1297275 : Nat := 118140960795 + 1297275 * 2 ^ 59
def prefixEnd_1297275 : Nat := 4983230072969 + 3 ^ 40 * 1297275 * 2
def baseEnd_1297275 : Nat := 148027914680337142065877

theorem tailTrace_1297275 : CollatzResearch.WordTrace tailWord_1297275 prefixEnd_1297275 148027914680337142065877 := by
  unfold tailWord_1297275
  simp only [CollatzResearch.WordTrace]
  refine ⟨47315506375201706776061279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31543670916801137850707519 47315506375201706776061279)
  ·
    refine ⟨70973259562802560164091919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47315506375201706776061279 70973259562802560164091919)
    ·
      refine ⟨106459889344203840246137879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70973259562802560164091919 106459889344203840246137879)
      ·
        refine ⟨159689834016305760369206819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106459889344203840246137879 159689834016305760369206819)
        ·
          refine ⟨239534751024458640553810229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159689834016305760369206819 239534751024458640553810229)
          ·
            refine ⟨22456382908542997551919709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 239534751024458640553810229 22456382908542997551919709)
            ·
              refine ⟨8421143590703624081969891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22456382908542997551919709 8421143590703624081969891)
              ·
                refine ⟨12631715386055436122954837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8421143590703624081969891 12631715386055436122954837)
                ·
                  refine ⟨148027914680337142065877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12631715386055436122954837 148027914680337142065877)
                  ·
                    rfl

theorem cell22_1297275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 8].length) (baseStart_1297275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297275 prefixEnd_1297275 := by exact prefixLift 1297275
  have htrace : WordTrace (prefixWord ++ tailWord_1297275) baseStart_1297275 baseEnd_1297275 := by
    simpa [prefixWord, tailWord_1297275, baseEnd_1297275] using wordTrace_append hprefix tailTrace_1297275
  have hstable : (prefixWord ++ tailWord_1297275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297275).length < 2 ^ (prefixWord ++ tailWord_1297275).sum := by decide
  have hdescent : baseEnd_1297275 < baseStart_1297275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297277 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 3, 4]
def baseStart_1297277 : Nat := 118140960795 + 1297277 * 2 ^ 59
def prefixEnd_1297277 : Nat := 4983230072969 + 3 ^ 40 * 1297277 * 2
def baseEnd_1297277 : Nat := 444084428681884087647625

theorem tailTrace_1297277 : CollatzResearch.WordTrace tailWord_1297277 prefixEnd_1297277 444084428681884087647625 := by
  unfold tailWord_1297277
  simp only [CollatzResearch.WordTrace]
  refine ⟨47315579321194461117634085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31543719547462974078422723 47315579321194461117634085)
  ·
    refine ⟨8871671122723961459556391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47315579321194461117634085 8871671122723961459556391)
    ·
      refine ⟨13307506684085942189334587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8871671122723961459556391 13307506684085942189334587)
      ·
        refine ⟨19961260026128913284001881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13307506684085942189334587 19961260026128913284001881)
        ·
          refine ⟨14970945019596684963001411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19961260026128913284001881 14970945019596684963001411)
          ·
            refine ⟨22456417529395027444502117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14970945019596684963001411 22456417529395027444502117)
            ·
              refine ⟨4210578286761567645844147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22456417529395027444502117 4210578286761567645844147)
              ·
                refine ⟨6315867430142351468766221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4210578286761567645844147 6315867430142351468766221)
                ·
                  refine ⟨2368450286303381800787333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6315867430142351468766221 2368450286303381800787333)
                  ·
                    refine ⟨444084428681884087647625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2368450286303381800787333 444084428681884087647625)
                    ·
                      rfl

theorem cell22_1297277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 4].length) (baseStart_1297277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297277 prefixEnd_1297277 := by exact prefixLift 1297277
  have htrace : WordTrace (prefixWord ++ tailWord_1297277) baseStart_1297277 baseEnd_1297277 := by
    simpa [prefixWord, tailWord_1297277, baseEnd_1297277] using wordTrace_append hprefix tailTrace_1297277
  have hstable : (prefixWord ++ tailWord_1297277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297277).length < 2 ^ (prefixWord ++ tailWord_1297277).sum := by decide
  have hdescent : baseEnd_1297277 < baseStart_1297277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297298 : List Nat := [3, 2, 3, 2, 3, 1, 1, 2, 5]
def baseStart_1297298 : Nat := 118140960795 + 1297298 * 2 ^ 59
def prefixEnd_1297298 : Nat := 4983230072969 + 3 ^ 40 * 1297298 * 2
def baseEnd_1297298 : Nat := 148030539137015677624187

theorem tailTrace_1297298 : CollatzResearch.WordTrace tailWord_1297298 prefixEnd_1297298 148030539137015677624187 := by
  unfold tailWord_1297298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11829086313529595426037137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31544230169412254469432365 11829086313529595426037137)
  ·
    refine ⟨8871814735147196569527853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11829086313529595426037137 8871814735147196569527853)
    ·
      refine ⟨3326930525680198713572945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8871814735147196569527853 3326930525680198713572945)
      ·
        refine ⟨2495197894260149035179709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3326930525680198713572945 2495197894260149035179709)
        ·
          refine ⟨935699210347555888192391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2495197894260149035179709 935699210347555888192391)
          ·
            refine ⟨1403548815521333832288587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935699210347555888192391 1403548815521333832288587)
            ·
              refine ⟨2105323223282000748432881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1403548815521333832288587 2105323223282000748432881)
              ·
                refine ⟨1578992417461500561324661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2105323223282000748432881 1578992417461500561324661)
                ·
                  refine ⟨148030539137015677624187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1578992417461500561324661 148030539137015677624187)
                  ·
                    rfl

theorem cell22_1297298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 2, 5].length) (baseStart_1297298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297298 prefixEnd_1297298 := by exact prefixLift 1297298
  have htrace : WordTrace (prefixWord ++ tailWord_1297298) baseStart_1297298 baseEnd_1297298 := by
    simpa [prefixWord, tailWord_1297298, baseEnd_1297298] using wordTrace_append hprefix tailTrace_1297298
  have hstable : (prefixWord ++ tailWord_1297298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297298).length < 2 ^ (prefixWord ++ tailWord_1297298).sum := by decide
  have hdescent : baseEnd_1297298 < baseStart_1297298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297309 : List Nat := [1, 4, 2, 1, 2, 1, 1, 6, 4]
def baseStart_1297309 : Nat := 118140960795 + 1297309 * 2 ^ 59
def prefixEnd_1297309 : Nat := 4983230072969 + 3 ^ 40 * 1297309 * 2
def baseEnd_1297309 : Nat := 148031794311948890282509

theorem tailTrace_1297309 : CollatzResearch.WordTrace tailWord_1297309 prefixEnd_1297309 148031794311948890282509 := by
  unfold tailWord_1297309
  simp only [CollatzResearch.WordTrace]
  refine ⟨47316746457078530582798981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31544497638052353721865987 47316746457078530582798981)
  ·
    refine ⟨8871889960702224484274809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47316746457078530582798981 8871889960702224484274809)
    ·
      refine ⟨6653917470526668363206107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8871889960702224484274809 6653917470526668363206107)
      ·
        refine ⟨9980876205790002544809161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6653917470526668363206107 9980876205790002544809161)
        ·
          refine ⟨7485657154342501908606871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9980876205790002544809161 7485657154342501908606871)
          ·
            refine ⟨11228485731513752862910307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7485657154342501908606871 11228485731513752862910307)
            ·
              refine ⟨16842728597270629294365461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11228485731513752862910307 16842728597270629294365461)
              ·
                refine ⟨789502902997060748173381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16842728597270629294365461 789502902997060748173381)
                ·
                  refine ⟨148031794311948890282509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 789502902997060748173381 148031794311948890282509)
                  ·
                    rfl

theorem cell22_1297309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_1297309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297309 prefixEnd_1297309 := by exact prefixLift 1297309
  have htrace : WordTrace (prefixWord ++ tailWord_1297309) baseStart_1297309 baseEnd_1297309 := by
    simpa [prefixWord, tailWord_1297309, baseEnd_1297309] using wordTrace_append hprefix tailTrace_1297309
  have hstable : (prefixWord ++ tailWord_1297309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297309).length < 2 ^ (prefixWord ++ tailWord_1297309).sum := by decide
  have hdescent : baseEnd_1297309 < baseStart_1297309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297337 : List Nat := [1, 2, 1, 4, 2, 3, 1, 8]
def baseStart_1297337 : Nat := 118140960795 + 1297337 * 2 ^ 59
def prefixEnd_1297337 : Nat := 4983230072969 + 3 ^ 40 * 1297337 * 2
def baseEnd_1297337 : Nat := 49344996434229325683049

theorem tailTrace_1297337 : CollatzResearch.WordTrace tailWord_1297337 prefixEnd_1297337 49344996434229325683049 := by
  unfold tailWord_1297337
  simp only [CollatzResearch.WordTrace]
  refine ⟨47317767700977091364818265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31545178467318060909878843 47317767700977091364818265)
  ·
    refine ⟨35488325775732818523613699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47317767700977091364818265 35488325775732818523613699)
    ·
      refine ⟨53232488663599227785420549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35488325775732818523613699 53232488663599227785420549)
      ·
        refine ⟨9981091624424855209766353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53232488663599227785420549 9981091624424855209766353)
        ·
          refine ⟨7485818718318641407324765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9981091624424855209766353 7485818718318641407324765)
          ·
            refine ⟨2807182019369490527746787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7485818718318641407324765 2807182019369490527746787)
            ·
              refine ⟨4210773029054235791620181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2807182019369490527746787 4210773029054235791620181)
              ·
                refine ⟨49344996434229325683049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4210773029054235791620181 49344996434229325683049)
                ·
                  rfl

theorem cell22_1297337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 8].length) (baseStart_1297337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297337 prefixEnd_1297337 := by exact prefixLift 1297337
  have htrace : WordTrace (prefixWord ++ tailWord_1297337) baseStart_1297337 baseEnd_1297337 := by
    simpa [prefixWord, tailWord_1297337, baseEnd_1297337] using wordTrace_append hprefix tailTrace_1297337
  have hstable : (prefixWord ++ tailWord_1297337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297337).length < 2 ^ (prefixWord ++ tailWord_1297337).sum := by decide
  have hdescent : baseEnd_1297337 < baseStart_1297337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297375 : List Nat := [1, 1, 2, 3, 6, 1, 2, 1, 2, 3]
def baseStart_1297375 : Nat := 118140960795 + 1297375 * 2 ^ 59
def prefixEnd_1297375 : Nat := 4983230072969 + 3 ^ 40 * 1297375 * 2
def baseEnd_1297375 : Nat := 444117976084644498697325

theorem tailTrace_1297375 : CollatzResearch.WordTrace tailWord_1297375 prefixEnd_1297375 444117976084644498697325 := by
  unfold tailWord_1297375
  simp only [CollatzResearch.WordTrace]
  refine ⟨47319153674839423854701579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31546102449892949236467719 47319153674839423854701579)
  ·
    refine ⟨70978730512259135782052369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47319153674839423854701579 70978730512259135782052369)
    ·
      refine ⟨53234047884194351836539277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70978730512259135782052369 53234047884194351836539277)
      ·
        refine ⟨19962767956572881938702229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53234047884194351836539277 19962767956572881938702229)
        ·
          refine ⟨935754747964353840876667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19962767956572881938702229 935754747964353840876667)
          ·
            refine ⟨1403632121946530761315001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935754747964353840876667 1403632121946530761315001)
            ·
              refine ⟨1052724091459898070986251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1403632121946530761315001 1052724091459898070986251)
              ·
                refine ⟨1579086137189847106479377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052724091459898070986251 1579086137189847106479377)
                ·
                  refine ⟨1184314602892385329859533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1579086137189847106479377 1184314602892385329859533)
                  ·
                    refine ⟨444117976084644498697325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1184314602892385329859533 444117976084644498697325)
                    ·
                      rfl

theorem cell22_1297375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 2, 1, 2, 3].length) (baseStart_1297375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297375 prefixEnd_1297375 := by exact prefixLift 1297375
  have htrace : WordTrace (prefixWord ++ tailWord_1297375) baseStart_1297375 baseEnd_1297375 := by
    simpa [prefixWord, tailWord_1297375, baseEnd_1297375] using wordTrace_append hprefix tailTrace_1297375
  have hstable : (prefixWord ++ tailWord_1297375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297375).length < 2 ^ (prefixWord ++ tailWord_1297375).sum := by decide
  have hdescent : baseEnd_1297375 < baseStart_1297375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297420 : List Nat := [2, 2, 1, 2, 3, 4, 2, 2, 1, 3]
def baseStart_1297420 : Nat := 118140960795 + 1297420 * 2 ^ 59
def prefixEnd_1297420 : Nat := 4983230072969 + 3 ^ 40 * 1297420 * 2
def baseEnd_1297420 : Nat := 444133380504279381322187

theorem tailTrace_1297420 : CollatzResearch.WordTrace tailWord_1297420 prefixEnd_1297420 444133380504279381322187 := by
  unfold tailWord_1297420
  simp only [CollatzResearch.WordTrace]
  refine ⟨23660397479838198270044857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31547196639784264360059809 23660397479838198270044857)
  ·
    refine ⟨17745298109878648702533643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23660397479838198270044857 17745298109878648702533643)
    ·
      refine ⟨26617947164817973053800465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17745298109878648702533643 26617947164817973053800465)
      ·
        refine ⟨19963460373613479790350349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26617947164817973053800465 19963460373613479790350349)
        ·
          refine ⟨7486297640105054921381381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19963460373613479790350349 7486297640105054921381381)
          ·
            refine ⟨1403680807519697797759009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7486297640105054921381381 1403680807519697797759009)
            ·
              refine ⟨1052760605639773348319257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1403680807519697797759009 1052760605639773348319257)
              ·
                refine ⟨789570454229830011239443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1052760605639773348319257 789570454229830011239443)
                ·
                  refine ⟨1184355681344745016859165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789570454229830011239443 1184355681344745016859165)
                  ·
                    refine ⟨444133380504279381322187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1184355681344745016859165 444133380504279381322187)
                    ·
                      rfl

theorem cell22_1297420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 2, 2, 1, 3].length) (baseStart_1297420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297420 prefixEnd_1297420 := by exact prefixLift 1297420
  have htrace : WordTrace (prefixWord ++ tailWord_1297420) baseStart_1297420 baseEnd_1297420 := by
    simpa [prefixWord, tailWord_1297420, baseEnd_1297420] using wordTrace_append hprefix tailTrace_1297420
  have hstable : (prefixWord ++ tailWord_1297420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297420).length < 2 ^ (prefixWord ++ tailWord_1297420).sum := by decide
  have hdescent : baseEnd_1297420 < baseStart_1297420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297427 : List Nat := [1, 1, 1, 2, 1, 4, 1, 5, 6]
def baseStart_1297427 : Nat := 118140960795 + 1297427 * 2 ^ 59
def prefixEnd_1297427 : Nat := 4983230072969 + 3 ^ 40 * 1297427 * 2
def baseEnd_1297427 : Nat := 148045258915777898799055

theorem tailTrace_1297427 : CollatzResearch.WordTrace tailWord_1297427 prefixEnd_1297427 148045258915777898799055 := by
  unfold tailWord_1297427
  simp only [CollatzResearch.WordTrace]
  refine ⟨47321050270651036735594535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31547366847100691157063023 47321050270651036735594535)
  ·
    refine ⟨70981575405976555103391803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47321050270651036735594535 70981575405976555103391803)
    ·
      refine ⟨106472363108964832655087705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70981575405976555103391803 106472363108964832655087705)
      ·
        refine ⟨79854272331723624491315779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106472363108964832655087705 79854272331723624491315779)
        ·
          refine ⟨119781408497585436736973669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79854272331723624491315779 119781408497585436736973669)
          ·
            refine ⟨22459014093297269388182563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 119781408497585436736973669 22459014093297269388182563)
            ·
              refine ⟨33688521139945904082273845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22459014093297269388182563 33688521139945904082273845)
              ·
                refine ⟨3158298856869928507713173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33688521139945904082273845 3158298856869928507713173)
                ·
                  refine ⟨148045258915777898799055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3158298856869928507713173 148045258915777898799055)
                  ·
                    rfl

theorem cell22_1297427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 5, 6].length) (baseStart_1297427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297427 prefixEnd_1297427 := by exact prefixLift 1297427
  have htrace : WordTrace (prefixWord ++ tailWord_1297427) baseStart_1297427 baseEnd_1297427 := by
    simpa [prefixWord, tailWord_1297427, baseEnd_1297427] using wordTrace_append hprefix tailTrace_1297427
  have hstable : (prefixWord ++ tailWord_1297427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297427).length < 2 ^ (prefixWord ++ tailWord_1297427).sum := by decide
  have hdescent : baseEnd_1297427 < baseStart_1297427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297429 : List Nat := [1, 3, 2, 1, 4, 1, 1, 2, 3, 4]
def baseStart_1297429 : Nat := 118140960795 + 1297429 * 2 ^ 59
def prefixEnd_1297429 : Nat := 4983230072969 + 3 ^ 40 * 1297429 * 2
def baseEnd_1297429 : Nat := 444136461388206357847159

theorem tailTrace_1297429 : CollatzResearch.WordTrace tailWord_1297429 prefixEnd_1297429 444136461388206357847159 := by
  unfold tailWord_1297429
  simp only [CollatzResearch.WordTrace]
  refine ⟨47321123216643791077167341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31547415477762527384778227 47321123216643791077167341)
  ·
    refine ⟨17745421206241421653937753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47321123216643791077167341 17745421206241421653937753)
    ·
      refine ⟨13309065904681066240453315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17745421206241421653937753 13309065904681066240453315)
      ·
        refine ⟨19963598857021599360679973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13309065904681066240453315 19963598857021599360679973)
        ·
          refine ⟨3743174785691549880127495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19963598857021599360679973 3743174785691549880127495)
          ·
            refine ⟨5614762178537324820191243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3743174785691549880127495 5614762178537324820191243)
            ·
              refine ⟨8422143267805987230286865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5614762178537324820191243 8422143267805987230286865)
              ·
                refine ⟨6316607450854490422715149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8422143267805987230286865 6316607450854490422715149)
                ·
                  refine ⟨2368727794070433908518181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6316607450854490422715149 2368727794070433908518181)
                  ·
                    refine ⟨444136461388206357847159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2368727794070433908518181 444136461388206357847159)
                    ·
                      rfl

theorem cell22_1297429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_1297429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297429 prefixEnd_1297429 := by exact prefixLift 1297429
  have htrace : WordTrace (prefixWord ++ tailWord_1297429) baseStart_1297429 baseEnd_1297429 := by
    simpa [prefixWord, tailWord_1297429, baseEnd_1297429] using wordTrace_append hprefix tailTrace_1297429
  have hstable : (prefixWord ++ tailWord_1297429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297429).length < 2 ^ (prefixWord ++ tailWord_1297429).sum := by decide
  have hdescent : baseEnd_1297429 < baseStart_1297429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297444 : List Nat := [2, 3, 1, 4, 1, 1, 1, 1, 8]
def baseStart_1297444 : Nat := 118140960795 + 1297444 * 2 ^ 59
def prefixEnd_1297444 : Nat := 4983230072969 + 3 ^ 40 * 1297444 * 2
def baseEnd_1297444 : Nat := 148047198731583772907371

theorem tailTrace_1297444 : CollatzResearch.WordTrace tailWord_1297444 prefixEnd_1297444 148047198731583772907371 := by
  unfold tailWord_1297444
  simp only [CollatzResearch.WordTrace]
  refine ⟨23660835155794724319481693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31547780207726299092642257 23660835155794724319481693)
  ·
    refine ⟨8872813183423021619805635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23660835155794724319481693 8872813183423021619805635)
    ·
      refine ⟨13309219775134532429708453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8872813183423021619805635 13309219775134532429708453)
      ·
        refine ⟨2495478707837724830570335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13309219775134532429708453 2495478707837724830570335)
        ·
          refine ⟨3743218061756587245855503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495478707837724830570335 3743218061756587245855503)
          ·
            refine ⟨5614827092634880868783255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3743218061756587245855503 5614827092634880868783255)
            ·
              refine ⟨8422240638952321303174883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5614827092634880868783255 8422240638952321303174883)
              ·
                refine ⟨12633360958428481954762325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8422240638952321303174883 12633360958428481954762325)
                ·
                  refine ⟨148047198731583772907371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12633360958428481954762325 148047198731583772907371)
                  ·
                    rfl

theorem cell22_1297444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_1297444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297444 prefixEnd_1297444 := by exact prefixLift 1297444
  have htrace : WordTrace (prefixWord ++ tailWord_1297444) baseStart_1297444 baseEnd_1297444 := by
    simpa [prefixWord, tailWord_1297444, baseEnd_1297444] using wordTrace_append hprefix tailTrace_1297444
  have hstable : (prefixWord ++ tailWord_1297444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297444).length < 2 ^ (prefixWord ++ tailWord_1297444).sum := by decide
  have hdescent : baseEnd_1297444 < baseStart_1297444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297459 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 4, 3]
def baseStart_1297459 : Nat := 118140960795 + 1297459 * 2 ^ 59
def prefixEnd_1297459 : Nat := 4983230072969 + 3 ^ 40 * 1297459 * 2
def baseEnd_1297459 : Nat := 444146731001296279597067

theorem tailTrace_1297459 : CollatzResearch.WordTrace tailWord_1297459 prefixEnd_1297459 444146731001296279597067 := by
  unfold tailWord_1297459
  simp only [CollatzResearch.WordTrace]
  refine ⟨47322217406535106200759431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31548144937690070800506287 47322217406535106200759431)
  ·
    refine ⟨70983326109802659301139147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47322217406535106200759431 70983326109802659301139147)
    ·
      refine ⟨106474989164703988951708721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70983326109802659301139147 106474989164703988951708721)
      ·
        refine ⟨79856241873527991713781541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106474989164703988951708721 79856241873527991713781541)
        ·
          refine ⟨14973045351286498446334039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 79856241873527991713781541 14973045351286498446334039)
          ·
            refine ⟨22459568026929747669501059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14973045351286498446334039 22459568026929747669501059)
            ·
              refine ⟨33689352040394621504251589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22459568026929747669501059 33689352040394621504251589)
              ·
                refine ⟨6316753507573991532047173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33689352040394621504251589 6316753507573991532047173)
                ·
                  refine ⟨1184391282670123412258845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6316753507573991532047173 1184391282670123412258845)
                  ·
                    refine ⟨444146731001296279597067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1184391282670123412258845 444146731001296279597067)
                    ·
                      rfl

theorem cell22_1297459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 3].length) (baseStart_1297459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297459 prefixEnd_1297459 := by exact prefixLift 1297459
  have htrace : WordTrace (prefixWord ++ tailWord_1297459) baseStart_1297459 baseEnd_1297459 := by
    simpa [prefixWord, tailWord_1297459, baseEnd_1297459] using wordTrace_append hprefix tailTrace_1297459
  have hstable : (prefixWord ++ tailWord_1297459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297459).length < 2 ^ (prefixWord ++ tailWord_1297459).sum := by decide
  have hdescent : baseEnd_1297459 < baseStart_1297459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297472 : List Nat := [2, 1, 1, 2, 2, 3, 11]
def baseStart_1297472 : Nat := 118140960795 + 1297472 * 2 ^ 59
def prefixEnd_1297472 : Nat := 4983230072969 + 3 ^ 40 * 1297472 * 2
def baseEnd_1297472 : Nat := 16450043746924762186001

theorem tailTrace_1297472 : CollatzResearch.WordTrace tailWord_1297472 prefixEnd_1297472 16450043746924762186001 := by
  unfold tailWord_1297472
  simp only [CollatzResearch.WordTrace]
  refine ⟨23661345777744004710491335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31548461036992006280655113 23661345777744004710491335)
  ·
    refine ⟨35492018666616007065737003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23661345777744004710491335 35492018666616007065737003)
    ·
      refine ⟨53238027999924010598605505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35492018666616007065737003 53238027999924010598605505)
      ·
        refine ⟨39928520999943007948954129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53238027999924010598605505 39928520999943007948954129)
        ·
          refine ⟨29946390749957255961715597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39928520999943007948954129 29946390749957255961715597)
          ·
            refine ⟨11229896531233970985643349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29946390749957255961715597 11229896531233970985643349)
            ·
              refine ⟨16450043746924762186001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 11229896531233970985643349 16450043746924762186001)
              ·
                rfl

theorem cell22_1297472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 11].length) (baseStart_1297472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297472 prefixEnd_1297472 := by exact prefixLift 1297472
  have htrace : WordTrace (prefixWord ++ tailWord_1297472) baseStart_1297472 baseEnd_1297472 := by
    simpa [prefixWord, tailWord_1297472, baseEnd_1297472] using wordTrace_append hprefix tailTrace_1297472
  have hstable : (prefixWord ++ tailWord_1297472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297472).length < 2 ^ (prefixWord ++ tailWord_1297472).sum := by decide
  have hdescent : baseEnd_1297472 < baseStart_1297472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297478 : List Nat := [6, 1, 1, 1, 1, 3, 2, 1, 6]
def baseStart_1297478 : Nat := 118140960795 + 1297478 * 2 ^ 59
def prefixEnd_1297478 : Nat := 4983230072969 + 3 ^ 40 * 1297478 * 2
def baseEnd_1297478 : Nat := 148051078363195521124003

theorem tailTrace_1297478 : CollatzResearch.WordTrace tailWord_1297478 prefixEnd_1297478 148051078363195521124003 := by
  unfold tailWord_1297478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1478840949795821013928159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31548606928977514963800725 1478840949795821013928159)
  ·
    refine ⟨2218261424693731520892239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1478840949795821013928159 2218261424693731520892239)
    ·
      refine ⟨3327392137040597281338359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2218261424693731520892239 3327392137040597281338359)
      ·
        refine ⟨4991088205560895922007539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3327392137040597281338359 4991088205560895922007539)
        ·
          refine ⟨7486632308341343883011309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4991088205560895922007539 7486632308341343883011309)
          ·
            refine ⟨2807487115628003956129241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7486632308341343883011309 2807487115628003956129241)
            ·
              refine ⟨2105615336721002967096931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2807487115628003956129241 2105615336721002967096931)
              ·
                refine ⟨3158423005081504450645397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2105615336721002967096931 3158423005081504450645397)
                ·
                  refine ⟨148051078363195521124003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3158423005081504450645397 148051078363195521124003)
                  ·
                    rfl

theorem cell22_1297478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_1297478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297478 prefixEnd_1297478 := by exact prefixLift 1297478
  have htrace : WordTrace (prefixWord ++ tailWord_1297478) baseStart_1297478 baseEnd_1297478 := by
    simpa [prefixWord, tailWord_1297478, baseEnd_1297478] using wordTrace_append hprefix tailTrace_1297478
  have hstable : (prefixWord ++ tailWord_1297478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297478).length < 2 ^ (prefixWord ++ tailWord_1297478).sum := by decide
  have hdescent : baseEnd_1297478 < baseStart_1297478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297487 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 4, 7]
def baseStart_1297487 : Nat := 118140960795 + 1297487 * 2 ^ 59
def prefixEnd_1297487 : Nat := 4983230072969 + 3 ^ 40 * 1297487 * 2
def baseEnd_1297487 : Nat := 444156315973513539896981

theorem tailTrace_1297487 : CollatzResearch.WordTrace tailWord_1297487 prefixEnd_1297487 444156315973513539896981 := by
  unfold tailWord_1297487
  simp only [CollatzResearch.WordTrace]
  refine ⟨47323238650433666982778715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31548825766955777988519143 47323238650433666982778715)
  ·
    refine ⟨70984857975650500474168073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47323238650433666982778715 70984857975650500474168073)
    ·
      refine ⟨53238643481737875355626055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 70984857975650500474168073 53238643481737875355626055)
      ·
        refine ⟨79857965222606813033439083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53238643481737875355626055 79857965222606813033439083)
        ·
          refine ⟨119786947833910219550158625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79857965222606813033439083 119786947833910219550158625)
          ·
            refine ⟨89840210875432664662618969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119786947833910219550158625 89840210875432664662618969)
            ·
              refine ⟨67380158156574498496964227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89840210875432664662618969 67380158156574498496964227)
              ·
                refine ⟨101070237234861747745446341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67380158156574498496964227 101070237234861747745446341)
                ·
                  refine ⟨18950669481536577702271189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 101070237234861747745446341 18950669481536577702271189)
                  ·
                    refine ⟨444156315973513539896981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18950669481536577702271189 444156315973513539896981)
                    ·
                      rfl

theorem cell22_1297487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 4, 7].length) (baseStart_1297487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297487 prefixEnd_1297487 := by exact prefixLift 1297487
  have htrace : WordTrace (prefixWord ++ tailWord_1297487) baseStart_1297487 baseEnd_1297487 := by
    simpa [prefixWord, tailWord_1297487, baseEnd_1297487] using wordTrace_append hprefix tailTrace_1297487
  have hstable : (prefixWord ++ tailWord_1297487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297487).length < 2 ^ (prefixWord ++ tailWord_1297487).sum := by decide
  have hdescent : baseEnd_1297487 < baseStart_1297487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297493 : List Nat := [1, 3, 2, 2, 1, 2, 5, 1, 2, 3]
def baseStart_1297493 : Nat := 118140960795 + 1297493 * 2 ^ 59
def prefixEnd_1297493 : Nat := 4983230072969 + 3 ^ 40 * 1297493 * 2
def baseEnd_1297493 : Nat := 444158369896131524246963

theorem tailTrace_1297493 : CollatzResearch.WordTrace tailWord_1297493 prefixEnd_1297493 444158369896131524246963 := by
  unfold tailWord_1297493
  simp only [CollatzResearch.WordTrace]
  refine ⟨47323457488411930007497133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31548971658941286671664755 47323457488411930007497133)
  ·
    refine ⟨17746296558154473752811425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47323457488411930007497133 17746296558154473752811425)
    ·
      refine ⟨13309722418615855314608569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17746296558154473752811425 13309722418615855314608569)
      ·
        refine ⟨9982291813961891485956427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13309722418615855314608569 9982291813961891485956427)
        ·
          refine ⟨14973437720942837228934641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9982291813961891485956427 14973437720942837228934641)
          ·
            refine ⟨11230078290707127921700981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14973437720942837228934641 11230078290707127921700981)
            ·
              refine ⟨1052819839753793242659467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11230078290707127921700981 1052819839753793242659467)
              ·
                refine ⟨1579229759630689863989201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052819839753793242659467 1579229759630689863989201)
                ·
                  refine ⟨1184422319723017397991901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1579229759630689863989201 1184422319723017397991901)
                  ·
                    refine ⟨444158369896131524246963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1184422319723017397991901 444158369896131524246963)
                    ·
                      rfl

theorem cell22_1297493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 2, 3].length) (baseStart_1297493 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297493 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297493 prefixEnd_1297493 := by exact prefixLift 1297493
  have htrace : WordTrace (prefixWord ++ tailWord_1297493) baseStart_1297493 baseEnd_1297493 := by
    simpa [prefixWord, tailWord_1297493, baseEnd_1297493] using wordTrace_append hprefix tailTrace_1297493
  have hstable : (prefixWord ++ tailWord_1297493).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297493).length < 2 ^ (prefixWord ++ tailWord_1297493).sum := by decide
  have hdescent : baseEnd_1297493 < baseStart_1297493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297506 : List Nat := [3, 3, 2, 2, 1, 2, 1, 8]
def baseStart_1297506 : Nat := 118140960795 + 1297506 * 2 ^ 59
def prefixEnd_1297506 : Nat := 4983230072969 + 3 ^ 40 * 1297506 * 2
def baseEnd_1297506 : Nat := 49351424451311535963547

theorem tailTrace_1297506 : CollatzResearch.WordTrace tailWord_1297506 prefixEnd_1297506 49351424451311535963547 := by
  unfold tailWord_1297506
  simp only [CollatzResearch.WordTrace]
  refine ⟨11830982909341208306930093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31549287758243222151813581 11830982909341208306930093)
  ·
    refine ⟨4436618591002953115098785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11830982909341208306930093 4436618591002953115098785)
    ·
      refine ⟨3327463943252214836324089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4436618591002953115098785 3327463943252214836324089)
      ·
        refine ⟨2495597957439161127243067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3327463943252214836324089 2495597957439161127243067)
        ·
          refine ⟨3743396936158741690864601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2495597957439161127243067 3743396936158741690864601)
          ·
            refine ⟨2807547702119056268148451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3743396936158741690864601 2807547702119056268148451)
            ·
              refine ⟨4211321553178584402222677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2807547702119056268148451 4211321553178584402222677)
              ·
                refine ⟨49351424451311535963547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4211321553178584402222677 49351424451311535963547)
                ·
                  rfl

theorem cell22_1297506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 2, 1, 8].length) (baseStart_1297506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297506 prefixEnd_1297506 := by exact prefixLift 1297506
  have htrace : WordTrace (prefixWord ++ tailWord_1297506) baseStart_1297506 baseEnd_1297506 := by
    simpa [prefixWord, tailWord_1297506, baseEnd_1297506] using wordTrace_append hprefix tailTrace_1297506
  have hstable : (prefixWord ++ tailWord_1297506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297506).length < 2 ^ (prefixWord ++ tailWord_1297506).sum := by decide
  have hdescent : baseEnd_1297506 < baseStart_1297506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297512 : List Nat := [2, 1, 4, 4, 2, 1, 1, 3, 4]
def baseStart_1297512 : Nat := 118140960795 + 1297512 * 2 ^ 59
def prefixEnd_1297512 : Nat := 4983230072969 + 3 ^ 40 * 1297512 * 2
def baseEnd_1297512 : Nat := 148054957994807269340635

theorem tailTrace_1297512 : CollatzResearch.WordTrace tailWord_1297512 prefixEnd_1297512 148054957994807269340635 := by
  unfold tailWord_1297512
  simp only [CollatzResearch.WordTrace]
  refine ⟨23662075237671548126219395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31549433650228730834959193 23662075237671548126219395)
  ·
    refine ⟨35493112856507322189329093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23662075237671548126219395 35493112856507322189329093)
    ·
      refine ⟨6654958660595122910499205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35493112856507322189329093 6654958660595122910499205)
      ·
        refine ⟨1247804748861585545718601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6654958660595122910499205 1247804748861585545718601)
        ·
          refine ⟨935853561646189159288951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1247804748861585545718601 935853561646189159288951)
          ·
            refine ⟨1403780342469283738933427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 935853561646189159288951 1403780342469283738933427)
            ·
              refine ⟨2105670513703925608400141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1403780342469283738933427 2105670513703925608400141)
              ·
                refine ⟨789626442638972103150053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2105670513703925608400141 789626442638972103150053)
                ·
                  refine ⟨148054957994807269340635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 789626442638972103150053 148054957994807269340635)
                  ·
                    rfl

theorem cell22_1297512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 2, 1, 1, 3, 4].length) (baseStart_1297512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297512 prefixEnd_1297512 := by exact prefixLift 1297512
  have htrace : WordTrace (prefixWord ++ tailWord_1297512) baseStart_1297512 baseEnd_1297512 := by
    simpa [prefixWord, tailWord_1297512, baseEnd_1297512] using wordTrace_append hprefix tailTrace_1297512
  have hstable : (prefixWord ++ tailWord_1297512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297512).length < 2 ^ (prefixWord ++ tailWord_1297512).sum := by decide
  have hdescent : baseEnd_1297512 < baseStart_1297512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297594 : List Nat := [3, 1, 1, 1, 2, 2, 1, 1, 5, 5]
def baseStart_1297594 : Nat := 118140960795 + 1297594 * 2 ^ 59
def prefixEnd_1297594 : Nat := 4983230072969 + 3 ^ 40 * 1297594 * 2
def baseEnd_1297594 : Nat := 444192944260200927471653

theorem tailTrace_1297594 : CollatzResearch.WordTrace tailWord_1297594 prefixEnd_1297594 444192944260200927471653 := by
  unfold tailWord_1297594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11831785315261506064230959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31551427507364016171282557 11831785315261506064230959)
  ·
    refine ⟨17747677972892259096346439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11831785315261506064230959 17747677972892259096346439)
    ·
      refine ⟨26621516959338388644519659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17747677972892259096346439 26621516959338388644519659)
      ·
        refine ⟨39932275439007582966779489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26621516959338388644519659 39932275439007582966779489)
        ·
          refine ⟨29949206579255687225084617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39932275439007582966779489 29949206579255687225084617)
          ·
            refine ⟨22461904934441765418813463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29949206579255687225084617 22461904934441765418813463)
            ·
              refine ⟨33692857401662648128220195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22461904934441765418813463 33692857401662648128220195)
              ·
                refine ⟨50539286102493972192330293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33692857401662648128220195 50539286102493972192330293)
                ·
                  refine ⟨4738058072108809893030965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 50539286102493972192330293 4738058072108809893030965)
                  ·
                    refine ⟨444192944260200927471653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4738058072108809893030965 444192944260200927471653)
                    ·
                      rfl

theorem cell22_1297594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 1, 5, 5].length) (baseStart_1297594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297594 prefixEnd_1297594 := by exact prefixLift 1297594
  have htrace : WordTrace (prefixWord ++ tailWord_1297594) baseStart_1297594 baseEnd_1297594 := by
    simpa [prefixWord, tailWord_1297594, baseEnd_1297594] using wordTrace_append hprefix tailTrace_1297594
  have hstable : (prefixWord ++ tailWord_1297594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297594).length < 2 ^ (prefixWord ++ tailWord_1297594).sum := by decide
  have hdescent : baseEnd_1297594 < baseStart_1297594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297645 : List Nat := [1, 5, 1, 2, 2, 1, 3, 2, 2, 3]
def baseStart_1297645 : Nat := 118140960795 + 1297645 * 2 ^ 59
def prefixEnd_1297645 : Nat := 4983230072969 + 3 ^ 40 * 1297645 * 2
def baseEnd_1297645 : Nat := 444210402602453794446497

theorem tailTrace_1297645 : CollatzResearch.WordTrace tailWord_1297645 prefixEnd_1297645 444210402602453794446497 := by
  unfold tailWord_1297645
  simp only [CollatzResearch.WordTrace]
  refine ⟨47329001383861259967030389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31552667589240839978020259 47329001383861259967030389)
  ·
    refine ⟨4437093879736993121909099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47329001383861259967030389 4437093879736993121909099)
    ·
      refine ⟨6655640819605489682863649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4437093879736993121909099 6655640819605489682863649)
      ·
        refine ⟨4991730614704117262147737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6655640819605489682863649 4991730614704117262147737)
        ·
          refine ⟨3743797961028087946610803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4991730614704117262147737 3743797961028087946610803)
          ·
            refine ⟨5615696941542131919916205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3743797961028087946610803 5615696941542131919916205)
            ·
              refine ⟨2105886353078299469968577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5615696941542131919916205 2105886353078299469968577)
              ·
                refine ⟨1579414764808724602476433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2105886353078299469968577 1579414764808724602476433)
                ·
                  refine ⟨1184561073606543451857325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1579414764808724602476433 1184561073606543451857325)
                  ·
                    refine ⟨444210402602453794446497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1184561073606543451857325 444210402602453794446497)
                    ·
                      rfl

theorem cell22_1297645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_1297645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297645 prefixEnd_1297645 := by exact prefixLift 1297645
  have htrace : WordTrace (prefixWord ++ tailWord_1297645) baseStart_1297645 baseEnd_1297645 := by
    simpa [prefixWord, tailWord_1297645, baseEnd_1297645] using wordTrace_append hprefix tailTrace_1297645
  have hstable : (prefixWord ++ tailWord_1297645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297645).length < 2 ^ (prefixWord ++ tailWord_1297645).sum := by decide
  have hdescent : baseEnd_1297645 < baseStart_1297645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297662 : List Nat := [4, 2, 2, 1, 1, 3, 3, 1, 2, 3]
def baseStart_1297662 : Nat := 118140960795 + 1297662 * 2 ^ 59
def prefixEnd_1297662 : Nat := 4983230072969 + 3 ^ 40 * 1297662 * 2
def baseEnd_1297662 : Nat := 444216222049871416771445

theorem tailTrace_1297662 : CollatzResearch.WordTrace tailWord_1297662 prefixEnd_1297662 444216222049871416771445 := by
  unfold tailWord_1297662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5916202678099958983799905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31553080949866447913599493 5916202678099958983799905)
  ·
    refine ⟨4437152008574969237849929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5916202678099958983799905 4437152008574969237849929)
    ·
      refine ⟨3327864006431226928387447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4437152008574969237849929 3327864006431226928387447)
      ·
        refine ⟨4991796009646840392581171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3327864006431226928387447 4991796009646840392581171)
        ·
          refine ⟨7487694014470260588871757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4991796009646840392581171 7487694014470260588871757)
          ·
            refine ⟨2807885255426347720826909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7487694014470260588871757 2807885255426347720826909)
            ·
              refine ⟨1052956970784880395310091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2807885255426347720826909 1052956970784880395310091)
              ·
                refine ⟨1579435456177320592965137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1052956970784880395310091 1579435456177320592965137)
                ·
                  refine ⟨1184576592132990444723853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1579435456177320592965137 1184576592132990444723853)
                  ·
                    refine ⟨444216222049871416771445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1184576592132990444723853 444216222049871416771445)
                    ·
                      rfl

theorem cell22_1297662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_1297662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297662 prefixEnd_1297662 := by exact prefixLift 1297662
  have htrace : WordTrace (prefixWord ++ tailWord_1297662) baseStart_1297662 baseEnd_1297662 := by
    simpa [prefixWord, tailWord_1297662, baseEnd_1297662] using wordTrace_append hprefix tailTrace_1297662
  have hstable : (prefixWord ++ tailWord_1297662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297662).length < 2 ^ (prefixWord ++ tailWord_1297662).sum := by decide
  have hdescent : baseEnd_1297662 < baseStart_1297662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297795 : List Nat := [1, 1, 1, 3, 5, 3, 1, 1, 2, 4]
def baseStart_1297795 : Nat := 118140960795 + 1297795 * 2 ^ 59
def prefixEnd_1297795 : Nat := 4983230072969 + 3 ^ 40 * 1297795 * 2
def baseEnd_1297795 : Nat := 444261750667903403196037

theorem tailTrace_1297795 : CollatzResearch.WordTrace tailWord_1297795 prefixEnd_1297795 444261750667903403196037 := by
  unfold tailWord_1297795
  simp only [CollatzResearch.WordTrace]
  refine ⟨47334472333317835584990839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31556314888878557056660559 47334472333317835584990839)
  ·
    refine ⟨71001708499976753377486259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47334472333317835584990839 71001708499976753377486259)
    ·
      refine ⟨106502562749965130066229389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71001708499976753377486259 106502562749965130066229389)
      ·
        refine ⟨39938461031236923774836021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106502562749965130066229389 39938461031236923774836021)
        ·
          refine ⟨3744230721678461603890877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39938461031236923774836021 3744230721678461603890877)
          ·
            refine ⟨1404086520629423101459079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3744230721678461603890877 1404086520629423101459079)
            ·
              refine ⟨2106129780944134652188619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404086520629423101459079 2106129780944134652188619)
              ·
                refine ⟨3159194671416201978282929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2106129780944134652188619 3159194671416201978282929)
                ·
                  refine ⟨2369396003562151483712197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3159194671416201978282929 2369396003562151483712197)
                  ·
                    refine ⟨444261750667903403196037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2369396003562151483712197 444261750667903403196037)
                    ·
                      rfl

theorem cell22_1297795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 1, 1, 2, 4].length) (baseStart_1297795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297795 prefixEnd_1297795 := by exact prefixLift 1297795
  have htrace : WordTrace (prefixWord ++ tailWord_1297795) baseStart_1297795 baseEnd_1297795 := by
    simpa [prefixWord, tailWord_1297795, baseEnd_1297795] using wordTrace_append hprefix tailTrace_1297795
  have hstable : (prefixWord ++ tailWord_1297795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297795).length < 2 ^ (prefixWord ++ tailWord_1297795).sum := by decide
  have hdescent : baseEnd_1297795 < baseStart_1297795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297810 : List Nat := [3, 2, 3, 3, 1, 1, 9]
def baseStart_1297810 : Nat := 118140960795 + 1297810 * 2 ^ 59
def prefixEnd_1297810 : Nat := 4983230072969 + 3 ^ 40 * 1297810 * 2
def baseEnd_1297810 : Nat := 16454329091646235706333

theorem tailTrace_1297810 : CollatzResearch.WordTrace tailWord_1297810 prefixEnd_1297810 16454329091646235706333 := by
  unfold tailWord_1297810
  simp only [CollatzResearch.WordTrace]
  refine ⟨11833754857065873286696721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31556679618842328764524589 11833754857065873286696721)
  ·
    refine ⟨8875316142799404965022541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11833754857065873286696721 8875316142799404965022541)
    ·
      refine ⟨3328243553549776861883453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8875316142799404965022541 3328243553549776861883453)
      ·
        refine ⟨1248091332581166323206295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3328243553549776861883453 1248091332581166323206295)
        ·
          refine ⟨1872136998871749484809443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248091332581166323206295 1872136998871749484809443)
          ·
            refine ⟨2808205498307624227214165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872136998871749484809443 2808205498307624227214165)
            ·
              refine ⟨16454329091646235706333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2808205498307624227214165 16454329091646235706333)
              ·
                rfl

theorem cell22_1297810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 9].length) (baseStart_1297810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297810 prefixEnd_1297810 := by exact prefixLift 1297810
  have htrace : WordTrace (prefixWord ++ tailWord_1297810) baseStart_1297810 baseEnd_1297810 := by
    simpa [prefixWord, tailWord_1297810, baseEnd_1297810] using wordTrace_append hprefix tailTrace_1297810
  have hstable : (prefixWord ++ tailWord_1297810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297810).length < 2 ^ (prefixWord ++ tailWord_1297810).sum := by decide
  have hdescent : baseEnd_1297810 < baseStart_1297810 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297876 : List Nat := [2, 4, 1, 2, 3, 1, 3, 2, 1, 3]
def baseStart_1297876 : Nat := 118140960795 + 1297876 * 2 ^ 59
def prefixEnd_1297876 : Nat := 4983230072969 + 3 ^ 40 * 1297876 * 2
def baseEnd_1297876 : Nat := 444289478623246191920789

theorem tailTrace_1297876 : CollatzResearch.WordTrace tailWord_1297876 prefixEnd_1297876 444289478623246191920789 := by
  unfold tailWord_1297876
  simp only [CollatzResearch.WordTrace]
  refine ⟨23668713323012193209344741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31558284430682924279126321 23668713323012193209344741)
  ·
    refine ⟨4437883748064786226752139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23668713323012193209344741 4437883748064786226752139)
    ·
      refine ⟨6656825622097179340128209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4437883748064786226752139 6656825622097179340128209)
      ·
        refine ⟨4992619216572884505096157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6656825622097179340128209 4992619216572884505096157)
        ·
          refine ⟨1872232206214831689411059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4992619216572884505096157 1872232206214831689411059)
          ·
            refine ⟨2808348309322247534116589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872232206214831689411059 2808348309322247534116589)
            ·
              refine ⟨1053130615995842825293721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2808348309322247534116589 1053130615995842825293721)
              ·
                refine ⟨789847961996882118970291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1053130615995842825293721 789847961996882118970291)
                ·
                  refine ⟨1184771942995323178455437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 789847961996882118970291 1184771942995323178455437)
                  ·
                    refine ⟨444289478623246191920789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1184771942995323178455437 444289478623246191920789)
                    ·
                      rfl

theorem cell22_1297876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 2, 1, 3].length) (baseStart_1297876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297876 prefixEnd_1297876 := by exact prefixLift 1297876
  have htrace : WordTrace (prefixWord ++ tailWord_1297876) baseStart_1297876 baseEnd_1297876 := by
    simpa [prefixWord, tailWord_1297876, baseEnd_1297876] using wordTrace_append hprefix tailTrace_1297876
  have hstable : (prefixWord ++ tailWord_1297876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297876).length < 2 ^ (prefixWord ++ tailWord_1297876).sum := by decide
  have hdescent : baseEnd_1297876 < baseStart_1297876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1297930 : List Nat := [3, 1, 2, 2, 2, 2, 2, 2, 2, 4]
def baseStart_1297930 : Nat := 118140960795 + 1297930 * 2 ^ 59
def prefixEnd_1297930 : Nat := 4983230072969 + 3 ^ 40 * 1297930 * 2
def baseEnd_1297930 : Nat := 444307963926808051070623

theorem tailTrace_1297930 : CollatzResearch.WordTrace tailWord_1297930 prefixEnd_1297930 444307963926808051070623 := by
  unfold tailWord_1297930
  simp only [CollatzResearch.WordTrace]
  refine ⟨11834849046957188410288811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31559597458552502427436829 11834849046957188410288811)
  ·
    refine ⟨17752273570435782615433217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11834849046957188410288811 17752273570435782615433217)
    ·
      refine ⟨13314205177826836961574913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17752273570435782615433217 13314205177826836961574913)
      ·
        refine ⟨9985653883370127721181185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13314205177826836961574913 9985653883370127721181185)
        ·
          refine ⟨7489240412527595790885889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9985653883370127721181185 7489240412527595790885889)
          ·
            refine ⟨5616930309395696843164417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7489240412527595790885889 5616930309395696843164417)
            ·
              refine ⟨4212697732046772632373313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5616930309395696843164417 4212697732046772632373313)
              ·
                refine ⟨3159523299035079474279985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4212697732046772632373313 3159523299035079474279985)
                ·
                  refine ⟨2369642474276309605709989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3159523299035079474279985 2369642474276309605709989)
                  ·
                    refine ⟨444307963926808051070623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2369642474276309605709989 444307963926808051070623)
                    ·
                      rfl

theorem cell22_1297930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_1297930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1297930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1297930 prefixEnd_1297930 := by exact prefixLift 1297930
  have htrace : WordTrace (prefixWord ++ tailWord_1297930) baseStart_1297930 baseEnd_1297930 := by
    simpa [prefixWord, tailWord_1297930, baseEnd_1297930] using wordTrace_append hprefix tailTrace_1297930
  have hstable : (prefixWord ++ tailWord_1297930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1297930).length < 2 ^ (prefixWord ++ tailWord_1297930).sum := by decide
  have hdescent : baseEnd_1297930 < baseStart_1297930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1297930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298007 : List Nat := [1, 1, 3, 2, 2, 4, 3, 1, 5]
def baseStart_1298007 : Nat := 118140960795 + 1298007 * 2 ^ 59
def prefixEnd_1298007 : Nat := 4983230072969 + 3 ^ 40 * 1298007 * 2
def baseEnd_1298007 : Nat := 148111440866801838965129

theorem tailTrace_1298007 : CollatzResearch.WordTrace tailWord_1298007 prefixEnd_1298007 148111440866801838965129 := by
  unfold tailWord_1298007
  simp only [CollatzResearch.WordTrace]
  refine ⟨47342204608549795791708275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31561469739033197194472183 47342204608549795791708275)
  ·
    refine ⟨71013306912824693687562413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47342204608549795791708275 71013306912824693687562413)
    ·
      refine ⟨26629990092309260132835905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71013306912824693687562413 26629990092309260132835905)
      ·
        refine ⟨19972492569231945099626929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26629990092309260132835905 19972492569231945099626929)
        ·
          refine ⟨14979369426923958824720197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19972492569231945099626929 14979369426923958824720197)
          ·
            refine ⟨2808631767548242279635037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14979369426923958824720197 2808631767548242279635037)
            ·
              refine ⟨1053236912830590854863139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2808631767548242279635037 1053236912830590854863139)
              ·
                refine ⟨1579855369245886282294709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053236912830590854863139 1579855369245886282294709)
                ·
                  refine ⟨148111440866801838965129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1579855369245886282294709 148111440866801838965129)
                  ·
                    rfl

theorem cell22_1298007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 3, 1, 5].length) (baseStart_1298007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298007 prefixEnd_1298007 := by exact prefixLift 1298007
  have htrace : WordTrace (prefixWord ++ tailWord_1298007) baseStart_1298007 baseEnd_1298007 := by
    simpa [prefixWord, tailWord_1298007, baseEnd_1298007] using wordTrace_append hprefix tailTrace_1298007
  have hstable : (prefixWord ++ tailWord_1298007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298007).length < 2 ^ (prefixWord ++ tailWord_1298007).sum := by decide
  have hdescent : baseEnd_1298007 < baseStart_1298007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298080 : List Nat := [2, 1, 1, 4, 3, 1, 2, 8]
def baseStart_1298080 : Nat := 118140960795 + 1298080 * 2 ^ 59
def prefixEnd_1298080 : Nat := 4983230072969 + 3 ^ 40 * 1298080 * 2
def baseEnd_1298080 : Nat := 49373256888028628868907

theorem tailTrace_1298080 : CollatzResearch.WordTrace tailWord_1298080 prefixEnd_1298080 49373256888028628868907 := by
  unfold tailWord_1298080
  simp only [CollatzResearch.WordTrace]
  refine ⟨23672433568642664629557847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31563244758190219506077129 23672433568642664629557847)
  ·
    refine ⟨35508650352963996944336771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23672433568642664629557847 35508650352963996944336771)
    ·
      refine ⟨53262975529445995416505157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35508650352963996944336771 53262975529445995416505157)
      ·
        refine ⟨9986807911771124140594717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53262975529445995416505157 9986807911771124140594717)
        ·
          refine ⟨3745052966914171552723019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9986807911771124140594717 3745052966914171552723019)
          ·
            refine ⟨5617579450371257329084529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3745052966914171552723019 5617579450371257329084529)
            ·
              refine ⟨4213184587778442996813397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5617579450371257329084529 4213184587778442996813397)
              ·
                refine ⟨49373256888028628868907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4213184587778442996813397 49373256888028628868907)
                ·
                  rfl

theorem cell22_1298080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 8].length) (baseStart_1298080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298080 prefixEnd_1298080 := by exact prefixLift 1298080
  have htrace : WordTrace (prefixWord ++ tailWord_1298080) baseStart_1298080 baseEnd_1298080 := by
    simpa [prefixWord, tailWord_1298080, baseEnd_1298080] using wordTrace_append hprefix tailTrace_1298080
  have hstable : (prefixWord ++ tailWord_1298080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298080).length < 2 ^ (prefixWord ++ tailWord_1298080).sum := by decide
  have hdescent : baseEnd_1298080 < baseStart_1298080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298101 : List Nat := [1, 3, 3, 3, 2, 1, 2, 2, 2, 3]
def baseStart_1298101 : Nat := 118140960795 + 1298101 * 2 ^ 59
def prefixEnd_1298101 : Nat := 4983230072969 + 3 ^ 40 * 1298101 * 2
def baseEnd_1298101 : Nat := 444366500721420605045099

theorem tailTrace_1298101 : CollatzResearch.WordTrace tailWord_1298101 prefixEnd_1298101 444366500721420605045099 := by
  unfold tailWord_1298101
  simp only [CollatzResearch.WordTrace]
  refine ⟨47345633070209249845630157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31563755380139499897086771 47345633070209249845630157)
  ·
    refine ⟨17754612401328468692111309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47345633070209249845630157 17754612401328468692111309)
    ·
      refine ⟨6657979650498175759541741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17754612401328468692111309 6657979650498175759541741)
      ·
        refine ⟨2496742368936815909828153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6657979650498175759541741 2496742368936815909828153)
        ·
          refine ⟨1872556776702611932371115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2496742368936815909828153 1872556776702611932371115)
          ·
            refine ⟨2808835165053917898556673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1872556776702611932371115 2808835165053917898556673)
            ·
              refine ⟨2106626373790438423917505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2808835165053917898556673 2106626373790438423917505)
              ·
                refine ⟨1579969780342828817938129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2106626373790438423917505 1579969780342828817938129)
                ·
                  refine ⟨1184977335257121613453597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1579969780342828817938129 1184977335257121613453597)
                  ·
                    refine ⟨444366500721420605045099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1184977335257121613453597 444366500721420605045099)
                    ·
                      rfl

theorem cell22_1298101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_1298101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298101 prefixEnd_1298101 := by exact prefixLift 1298101
  have htrace : WordTrace (prefixWord ++ tailWord_1298101) baseStart_1298101 baseEnd_1298101 := by
    simpa [prefixWord, tailWord_1298101, baseEnd_1298101] using wordTrace_append hprefix tailTrace_1298101
  have hstable : (prefixWord ++ tailWord_1298101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298101).length < 2 ^ (prefixWord ++ tailWord_1298101).sum := by decide
  have hdescent : baseEnd_1298101 < baseStart_1298101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298112 : List Nat := [2, 1, 1, 2, 4, 1, 2, 3, 3, 3]
def baseStart_1298112 : Nat := 118140960795 + 1298112 * 2 ^ 59
def prefixEnd_1298112 : Nat := 4983230072969 + 3 ^ 40 * 1298112 * 2
def baseEnd_1298112 : Nat := 444370266246220243020065

theorem tailTrace_1298112 : CollatzResearch.WordTrace tailWord_1298112 prefixEnd_1298112 444370266246220243020065 := by
  unfold tailWord_1298112
  simp only [CollatzResearch.WordTrace]
  refine ⟨23673017136584699362140295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31564022848779599149520393 23673017136584699362140295)
  ·
    refine ⟨35509525704877049043210443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23673017136584699362140295 35509525704877049043210443)
    ·
      refine ⟨53264288557315573564815665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35509525704877049043210443 53264288557315573564815665)
      ·
        refine ⟨39948216417986680173611749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53264288557315573564815665 39948216417986680173611749)
        ·
          refine ⟨7490290578372502532552203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39948216417986680173611749 7490290578372502532552203)
          ·
            refine ⟨11235435867558753798828305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7490290578372502532552203 11235435867558753798828305)
            ·
              refine ⟨8426576900669065349121229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11235435867558753798828305 8426576900669065349121229)
              ·
                refine ⟨3159966337750899505920461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8426576900669065349121229 3159966337750899505920461)
                ·
                  refine ⟨1184987376656587314720173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3159966337750899505920461 1184987376656587314720173)
                  ·
                    refine ⟨444370266246220243020065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1184987376656587314720173 444370266246220243020065)
                    ·
                      rfl

theorem cell22_1298112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 3, 3, 3].length) (baseStart_1298112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298112 prefixEnd_1298112 := by exact prefixLift 1298112
  have htrace : WordTrace (prefixWord ++ tailWord_1298112) baseStart_1298112 baseEnd_1298112 := by
    simpa [prefixWord, tailWord_1298112, baseEnd_1298112] using wordTrace_append hprefix tailTrace_1298112
  have hstable : (prefixWord ++ tailWord_1298112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298112).length < 2 ^ (prefixWord ++ tailWord_1298112).sum := by decide
  have hdescent : baseEnd_1298112 < baseStart_1298112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298118 : List Nat := [6, 1, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1298118 : Nat := 118140960795 + 1298118 * 2 ^ 59
def prefixEnd_1298118 : Nat := 4983230072969 + 3 ^ 40 * 1298118 * 2
def baseEnd_1298118 : Nat := 444372320168838227370047

theorem tailTrace_1298118 : CollatzResearch.WordTrace tailWord_1298118 prefixEnd_1298118 444372320168838227370047 := by
  unfold tailWord_1298118
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479570409723364429656219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31564168740765107832666005 1479570409723364429656219)
  ·
    refine ⟨2219355614585046644484329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1479570409723364429656219 2219355614585046644484329)
    ·
      refine ⟨1664516710938784983363247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2219355614585046644484329 1664516710938784983363247)
      ·
        refine ⟨2496775066408177475044871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1664516710938784983363247 2496775066408177475044871)
        ·
          refine ⟨3745162599612266212567307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2496775066408177475044871 3745162599612266212567307)
          ·
            refine ⟨5617743899418399318850961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3745162599612266212567307 5617743899418399318850961)
            ·
              refine ⟨4213307924563799489138221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5617743899418399318850961 4213307924563799489138221)
              ·
                refine ⟨1579990471711424808426833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4213307924563799489138221 1579990471711424808426833)
                ·
                  refine ⟨1184992853783568606320125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1579990471711424808426833 1184992853783568606320125)
                  ·
                    refine ⟨444372320168838227370047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1184992853783568606320125 444372320168838227370047)
                    ·
                      rfl

theorem cell22_1298118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1298118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298118 prefixEnd_1298118 := by exact prefixLift 1298118
  have htrace : WordTrace (prefixWord ++ tailWord_1298118) baseStart_1298118 baseEnd_1298118 := by
    simpa [prefixWord, tailWord_1298118, baseEnd_1298118] using wordTrace_append hprefix tailTrace_1298118
  have hstable : (prefixWord ++ tailWord_1298118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298118).length < 2 ^ (prefixWord ++ tailWord_1298118).sum := by decide
  have hdescent : baseEnd_1298118 < baseStart_1298118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298157 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 2, 5]
def baseStart_1298157 : Nat := 118140960795 + 1298157 * 2 ^ 59
def prefixEnd_1298157 : Nat := 4983230072969 + 3 ^ 40 * 1298157 * 2
def baseEnd_1298157 : Nat := 444385670665855125644927

theorem tailTrace_1298157 : CollatzResearch.WordTrace tailWord_1298157 prefixEnd_1298157 444385670665855125644927 := by
  unfold tailWord_1298157
  simp only [CollatzResearch.WordTrace]
  refine ⟨47347675558006371409668725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31565117038670914273112483 47347675558006371409668725)
  ·
    refine ⟨4438844583563097319656443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47347675558006371409668725 4438844583563097319656443)
    ·
      refine ⟨6658266875344645979484665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4438844583563097319656443 6658266875344645979484665)
      ·
        refine ⟨4993700156508484484613499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6658266875344645979484665 4993700156508484484613499)
        ·
          refine ⟨7490550234762726726920249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4993700156508484484613499 7490550234762726726920249)
          ·
            refine ⟨5617912676072045045190187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7490550234762726726920249 5617912676072045045190187)
            ·
              refine ⟨8426869014108067567785281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5617912676072045045190187 8426869014108067567785281)
              ·
                refine ⟨6320151760581050675838961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8426869014108067567785281 6320151760581050675838961)
                ·
                  refine ⟨4740113820435788006879221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6320151760581050675838961 4740113820435788006879221)
                  ·
                    refine ⟨444385670665855125644927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4740113820435788006879221 444385670665855125644927)
                    ·
                      rfl

theorem cell22_1298157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 2, 5].length) (baseStart_1298157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298157 prefixEnd_1298157 := by exact prefixLift 1298157
  have htrace : WordTrace (prefixWord ++ tailWord_1298157) baseStart_1298157 baseEnd_1298157 := by
    simpa [prefixWord, tailWord_1298157, baseEnd_1298157] using wordTrace_append hprefix tailTrace_1298157
  have hstable : (prefixWord ++ tailWord_1298157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298157).length < 2 ^ (prefixWord ++ tailWord_1298157).sum := by decide
  have hdescent : baseEnd_1298157 < baseStart_1298157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298182 : List Nat := [6, 2, 2, 1, 1, 2, 2, 6]
def baseStart_1298182 : Nat := 118140960795 + 1298182 * 2 ^ 59
def prefixEnd_1298182 : Nat := 4983230072969 + 3 ^ 40 * 1298182 * 2
def baseEnd_1298182 : Nat := 49377136519640377085539

theorem tailTrace_1298182 : CollatzResearch.WordTrace tailWord_1298182 prefixEnd_1298182 49377136519640377085539 := by
  unfold tailWord_1298182
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479643355716118771229025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31565724921943867119552533 1479643355716118771229025)
  ·
    refine ⟨1109732516787089078421769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1479643355716118771229025 1109732516787089078421769)
    ·
      refine ⟨832299387590316808816327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1109732516787089078421769 832299387590316808816327)
      ·
        refine ⟨1248449081385475213224491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 832299387590316808816327 1248449081385475213224491)
        ·
          refine ⟨1872673622078212819836737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248449081385475213224491 1872673622078212819836737)
          ·
            refine ⟨1404505216558659614877553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872673622078212819836737 1404505216558659614877553)
            ·
              refine ⟨1053378912418994711158165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404505216558659614877553 1053378912418994711158165)
              ·
                refine ⟨49377136519640377085539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1053378912418994711158165 49377136519640377085539)
                ·
                  rfl

theorem cell22_1298182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_1298182 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298182 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298182 prefixEnd_1298182 := by exact prefixLift 1298182
  have htrace : WordTrace (prefixWord ++ tailWord_1298182) baseStart_1298182 baseEnd_1298182 := by
    simpa [prefixWord, tailWord_1298182, baseEnd_1298182] using wordTrace_append hprefix tailTrace_1298182
  have hstable : (prefixWord ++ tailWord_1298182).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298182).length < 2 ^ (prefixWord ++ tailWord_1298182).sum := by decide
  have hdescent : baseEnd_1298182 < baseStart_1298182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298232 : List Nat := [2, 1, 2, 1, 3, 4, 2, 7]
def baseStart_1298232 : Nat := 118140960795 + 1298232 * 2 ^ 59
def prefixEnd_1298232 : Nat := 4983230072969 + 3 ^ 40 * 1298232 * 2
def baseEnd_1298232 : Nat := 49379038299842214446633

theorem tailTrace_1298232 : CollatzResearch.WordTrace tailWord_1298232 prefixEnd_1298232 49379038299842214446633 := by
  unfold tailWord_1298232
  simp only [CollatzResearch.WordTrace]
  refine ⟨23675205516367329609324475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31566940688489772812432633 23675205516367329609324475)
  ·
    refine ⟨35512808274550994413986713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23675205516367329609324475 35512808274550994413986713)
    ·
      refine ⟨26634606205913245810490035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35512808274550994413986713 26634606205913245810490035)
      ·
        refine ⟨39951909308869868715735053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26634606205913245810490035 39951909308869868715735053)
        ·
          refine ⟨14981965990826200768400645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39951909308869868715735053 14981965990826200768400645)
          ·
            refine ⟨2809118623279912644075121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14981965990826200768400645 2809118623279912644075121)
            ·
              refine ⟨2106838967459934483056341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2809118623279912644075121 2106838967459934483056341)
              ·
                refine ⟨49379038299842214446633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2106838967459934483056341 49379038299842214446633)
                ·
                  rfl

theorem cell22_1298232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 7].length) (baseStart_1298232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298232 prefixEnd_1298232 := by exact prefixLift 1298232
  have htrace : WordTrace (prefixWord ++ tailWord_1298232) baseStart_1298232 baseEnd_1298232 := by
    simpa [prefixWord, tailWord_1298232, baseEnd_1298232] using wordTrace_append hprefix tailTrace_1298232
  have hstable : (prefixWord ++ tailWord_1298232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298232).length < 2 ^ (prefixWord ++ tailWord_1298232).sum := by decide
  have hdescent : baseEnd_1298232 < baseStart_1298232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298236 : List Nat := [2, 2, 2, 2, 1, 1, 6, 1, 2, 3]
def baseStart_1298236 : Nat := 118140960795 + 1298236 * 2 ^ 59
def prefixEnd_1298236 : Nat := 4983230072969 + 3 ^ 40 * 1298236 * 2
def baseEnd_1298236 : Nat := 444412713980325252919685

theorem tailTrace_1298236 : CollatzResearch.WordTrace tailWord_1298236 prefixEnd_1298236 444412713980325252919685 := by
  unfold tailWord_1298236
  simp only [CollatzResearch.WordTrace]
  refine ⟨23675278462360083950897281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31567037949813445267863041 23675278462360083950897281)
  ·
    refine ⟨17756458846770062963172961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23675278462360083950897281 17756458846770062963172961)
    ·
      refine ⟨13317344135077547222379721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17756458846770062963172961 13317344135077547222379721)
      ·
        refine ⟨9988008101308160416784791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13317344135077547222379721 9988008101308160416784791)
        ·
          refine ⟨14982012151962240625177187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9988008101308160416784791 14982012151962240625177187)
          ·
            refine ⟨22473018227943360937765781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14982012151962240625177187 22473018227943360937765781)
            ·
              refine ⟨1053422729434845043957771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22473018227943360937765781 1053422729434845043957771)
              ·
                refine ⟨1580134094152267565936657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053422729434845043957771 1580134094152267565936657)
                ·
                  refine ⟨1185100570614200674452493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1580134094152267565936657 1185100570614200674452493)
                  ·
                    refine ⟨444412713980325252919685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1185100570614200674452493 444412713980325252919685)
                    ·
                      rfl

theorem cell22_1298236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 6, 1, 2, 3].length) (baseStart_1298236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298236 prefixEnd_1298236 := by exact prefixLift 1298236
  have htrace : WordTrace (prefixWord ++ tailWord_1298236) baseStart_1298236 baseEnd_1298236 := by
    simpa [prefixWord, tailWord_1298236, baseEnd_1298236] using wordTrace_append hprefix tailTrace_1298236
  have hstable : (prefixWord ++ tailWord_1298236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298236).length < 2 ^ (prefixWord ++ tailWord_1298236).sum := by decide
  have hdescent : baseEnd_1298236 < baseStart_1298236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298328 : List Nat := [2, 1, 2, 6, 1, 2, 1, 2, 5]
def baseStart_1298328 : Nat := 118140960795 + 1298328 * 2 ^ 59
def prefixEnd_1298328 : Nat := 4983230072969 + 3 ^ 40 * 1298328 * 2
def baseEnd_1298328 : Nat := 148148069153489226539801

theorem tailTrace_1298328 : CollatzResearch.WordTrace tailWord_1298328 prefixEnd_1298328 148148069153489226539801 := by
  unfold tailWord_1298328
  simp only [CollatzResearch.WordTrace]
  refine ⟨23676956220193433807071819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31569274960257911742762425 23676956220193433807071819)
  ·
    refine ⟨35515434330290150710607729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23676956220193433807071819 35515434330290150710607729)
    ·
      refine ⟨26636575747717613032955797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35515434330290150710607729 26636575747717613032955797)
      ·
        refine ⟨1248589488174263110919803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 26636575747717613032955797 1248589488174263110919803)
        ·
          refine ⟨1872884232261394666379705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1248589488174263110919803 1872884232261394666379705)
          ·
            refine ⟨1404663174196045999784779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1872884232261394666379705 1404663174196045999784779)
            ·
              refine ⟨2106994761294068999677169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404663174196045999784779 2106994761294068999677169)
              ·
                refine ⟨1580246070970551749757877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2106994761294068999677169 1580246070970551749757877)
                ·
                  refine ⟨148148069153489226539801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1580246070970551749757877 148148069153489226539801)
                  ·
                    rfl

theorem cell22_1298328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 2, 5].length) (baseStart_1298328 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298328 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298328 prefixEnd_1298328 := by exact prefixLift 1298328
  have htrace : WordTrace (prefixWord ++ tailWord_1298328) baseStart_1298328 baseEnd_1298328 := by
    simpa [prefixWord, tailWord_1298328, baseEnd_1298328] using wordTrace_append hprefix tailTrace_1298328
  have hstable : (prefixWord ++ tailWord_1298328).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298328).length < 2 ^ (prefixWord ++ tailWord_1298328).sum := by decide
  have hdescent : baseEnd_1298328 < baseStart_1298328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298367 : List Nat := [1, 1, 2, 2, 2, 1, 5, 8]
def baseStart_1298367 : Nat := 118140960795 + 1298367 * 2 ^ 59
def prefixEnd_1298367 : Nat := 4983230072969 + 3 ^ 40 * 1298367 * 2
def baseEnd_1298367 : Nat := 49384173106387175321587

theorem tailTrace_1298367 : CollatzResearch.WordTrace tailWord_1298367 prefixEnd_1298367 49384173106387175321587 := by
  unfold tailWord_1298367
  simp only [CollatzResearch.WordTrace]
  refine ⟨47355334887245577274813355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31570223258163718183208903 47355334887245577274813355)
  ·
    refine ⟨71033002330868365912220033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47355334887245577274813355 71033002330868365912220033)
    ·
      refine ⟨53274751748151274434165025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71033002330868365912220033 53274751748151274434165025)
      ·
        refine ⟨39956063811113455825623769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53274751748151274434165025 39956063811113455825623769)
        ·
          refine ⟨29967047858335091869217827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39956063811113455825623769 29967047858335091869217827)
          ·
            refine ⟨44950571787502637803826741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29967047858335091869217827 44950571787502637803826741)
            ·
              refine ⟨4214116105078372294108757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44950571787502637803826741 4214116105078372294108757)
              ·
                refine ⟨49384173106387175321587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4214116105078372294108757 49384173106387175321587)
                ·
                  rfl

theorem cell22_1298367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 8].length) (baseStart_1298367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298367 prefixEnd_1298367 := by exact prefixLift 1298367
  have htrace : WordTrace (prefixWord ++ tailWord_1298367) baseStart_1298367 baseEnd_1298367 := by
    simpa [prefixWord, tailWord_1298367, baseEnd_1298367] using wordTrace_append hprefix tailTrace_1298367
  have hstable : (prefixWord ++ tailWord_1298367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298367).length < 2 ^ (prefixWord ++ tailWord_1298367).sum := by decide
  have hdescent : baseEnd_1298367 < baseStart_1298367 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298390 : List Nat := [5, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_1298390 : Nat := 118140960795 + 1298390 * 2 ^ 59
def prefixEnd_1298390 : Nat := 4983230072969 + 3 ^ 40 * 1298390 * 2
def baseEnd_1298390 : Nat := 148155143775840061523071

theorem tailTrace_1298390 : CollatzResearch.WordTrace tailWord_1298390 prefixEnd_1298390 148155143775840061523071 := by
  unfold tailWord_1298390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959760860385140762681289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31570782510774834801933749 2959760860385140762681289)
  ·
    refine ⟨2219820645288855572010967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2959760860385140762681289 2219820645288855572010967)
    ·
      refine ⟨3329730967933283358016451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2219820645288855572010967 3329730967933283358016451)
      ·
        refine ⟨4994596451899925037024677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3329730967933283358016451 4994596451899925037024677)
        ·
          refine ⟨936486834731235944442127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4994596451899925037024677 936486834731235944442127)
          ·
            refine ⟨1404730252096853916663191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936486834731235944442127 1404730252096853916663191)
            ·
              refine ⟨2107095378145280874994787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404730252096853916663191 2107095378145280874994787)
              ·
                refine ⟨3160643067217921312492181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107095378145280874994787 3160643067217921312492181)
                ·
                  refine ⟨148155143775840061523071, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3160643067217921312492181 148155143775840061523071)
                  ·
                    rfl

theorem cell22_1298390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_1298390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298390 prefixEnd_1298390 := by exact prefixLift 1298390
  have htrace : WordTrace (prefixWord ++ tailWord_1298390) baseStart_1298390 baseEnd_1298390 := by
    simpa [prefixWord, tailWord_1298390, baseEnd_1298390] using wordTrace_append hprefix tailTrace_1298390
  have hstable : (prefixWord ++ tailWord_1298390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298390).length < 2 ^ (prefixWord ++ tailWord_1298390).sum := by decide
  have hdescent : baseEnd_1298390 < baseStart_1298390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298433 : List Nat := [1, 2, 4, 1, 2, 1, 2, 5, 1, 3]
def baseStart_1298433 : Nat := 118140960795 + 1298433 * 2 ^ 59
def prefixEnd_1298433 : Nat := 4983230072969 + 3 ^ 40 * 1298433 * 2
def baseEnd_1298433 : Nat := 444480151106282405744081

theorem tailTrace_1298433 : CollatzResearch.WordTrace tailWord_1298433 prefixEnd_1298433 444480151106282405744081 := by
  unfold tailWord_1298433
  simp only [CollatzResearch.WordTrace]
  refine ⟨47357742105006470546715953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31571828070004313697810635 47357742105006470546715953)
  ·
    refine ⟨35518306578754852910036965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47357742105006470546715953 35518306578754852910036965)
    ·
      refine ⟨6659682483516534920631931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35518306578754852910036965 6659682483516534920631931)
      ·
        refine ⟨9989523725274802380947897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6659682483516534920631931 9989523725274802380947897)
        ·
          refine ⟨7492142793956101785710923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9989523725274802380947897 7492142793956101785710923)
          ·
            refine ⟨11238214190934152678566385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7492142793956101785710923 11238214190934152678566385)
            ·
              refine ⟨8428660643200614508924789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11238214190934152678566385 8428660643200614508924789)
              ·
                refine ⟨790186935300057610211699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8428660643200614508924789 790186935300057610211699)
                ·
                  refine ⟨1185280402950086415317549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790186935300057610211699 1185280402950086415317549)
                  ·
                    refine ⟨444480151106282405744081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1185280402950086415317549 444480151106282405744081)
                    ·
                      rfl

theorem cell22_1298433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_1298433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298433 prefixEnd_1298433 := by exact prefixLift 1298433
  have htrace : WordTrace (prefixWord ++ tailWord_1298433) baseStart_1298433 baseEnd_1298433 := by
    simpa [prefixWord, tailWord_1298433, baseEnd_1298433] using wordTrace_append hprefix tailTrace_1298433
  have hstable : (prefixWord ++ tailWord_1298433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298433).length < 2 ^ (prefixWord ++ tailWord_1298433).sum := by decide
  have hdescent : baseEnd_1298433 < baseStart_1298433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298444 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 2, 5]
def baseStart_1298444 : Nat := 118140960795 + 1298444 * 2 ^ 59
def prefixEnd_1298444 : Nat := 4983230072969 + 3 ^ 40 * 1298444 * 2
def baseEnd_1298444 : Nat := 444483916631082043719047

theorem tailTrace_1298444 : CollatzResearch.WordTrace tailWord_1298444 prefixEnd_1298444 444483916631082043719047 := by
  unfold tailWord_1298444
  simp only [CollatzResearch.WordTrace]
  refine ⟨23679071653983309712683193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31572095538644412950244257 23679071653983309712683193)
  ·
    refine ⟨17759303740487482284512395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23679071653983309712683193 17759303740487482284512395)
    ·
      refine ⟨26638955610731223426768593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17759303740487482284512395 26638955610731223426768593)
      ·
        refine ⟨19979216708048417570076445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26638955610731223426768593 19979216708048417570076445)
        ·
          refine ⟨7492206265518156588778667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19979216708048417570076445 7492206265518156588778667)
          ·
            refine ⟨11238309398277234883168001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7492206265518156588778667 11238309398277234883168001)
            ·
              refine ⟨8428732048707926162376001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11238309398277234883168001 8428732048707926162376001)
              ·
                refine ⟨6321549036530944621782001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8428732048707926162376001 6321549036530944621782001)
                ·
                  refine ⟨4741161777398208466336501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6321549036530944621782001 4741161777398208466336501)
                  ·
                    refine ⟨444483916631082043719047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4741161777398208466336501 444483916631082043719047)
                    ·
                      rfl

theorem cell22_1298444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 2, 5].length) (baseStart_1298444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298444 prefixEnd_1298444 := by exact prefixLift 1298444
  have htrace : WordTrace (prefixWord ++ tailWord_1298444) baseStart_1298444 baseEnd_1298444 := by
    simpa [prefixWord, tailWord_1298444, baseEnd_1298444] using wordTrace_append hprefix tailTrace_1298444
  have hstable : (prefixWord ++ tailWord_1298444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298444).length < 2 ^ (prefixWord ++ tailWord_1298444).sum := by decide
  have hdescent : baseEnd_1298444 < baseStart_1298444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298446 : List Nat := [4, 1, 1, 2, 2, 1, 4, 2, 5]
def baseStart_1298446 : Nat := 118140960795 + 1298446 * 2 ^ 59
def prefixEnd_1298446 : Nat := 4983230072969 + 3 ^ 40 * 1298446 * 2
def baseEnd_1298446 : Nat := 148161533757318235056347

theorem tailTrace_1298446 : CollatzResearch.WordTrace tailWord_1298446 prefixEnd_1298446 148161533757318235056347 := by
  unfold tailWord_1298446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5919777031744921720867399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31572144169306249177959461 5919777031744921720867399)
  ·
    refine ⟨8879665547617382581301099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5919777031744921720867399 8879665547617382581301099)
    ·
      refine ⟨13319498321426073871951649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8879665547617382581301099 13319498321426073871951649)
      ·
        refine ⟨9989623741069555403963737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13319498321426073871951649 9989623741069555403963737)
        ·
          refine ⟨7492217805802166552972803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9989623741069555403963737 7492217805802166552972803)
          ·
            refine ⟨11238326708703249829459205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7492217805802166552972803 11238326708703249829459205)
            ·
              refine ⟨2107186257881859343023601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11238326708703249829459205 2107186257881859343023601)
              ·
                refine ⟨1580389693411394507267701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2107186257881859343023601 1580389693411394507267701)
                ·
                  refine ⟨148161533757318235056347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1580389693411394507267701 148161533757318235056347)
                  ·
                    rfl

theorem cell22_1298446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_1298446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298446 prefixEnd_1298446 := by exact prefixLift 1298446
  have htrace : WordTrace (prefixWord ++ tailWord_1298446) baseStart_1298446 baseEnd_1298446 := by
    simpa [prefixWord, tailWord_1298446, baseEnd_1298446] using wordTrace_append hprefix tailTrace_1298446
  have hstable : (prefixWord ++ tailWord_1298446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298446).length < 2 ^ (prefixWord ++ tailWord_1298446).sum := by decide
  have hdescent : baseEnd_1298446 < baseStart_1298446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298461 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 2, 5]
def baseStart_1298461 : Nat := 118140960795 + 1298461 * 2 ^ 59
def prefixEnd_1298461 : Nat := 4983230072969 + 3 ^ 40 * 1298461 * 2
def baseEnd_1298461 : Nat := 444489736078499666043995

theorem tailTrace_1298461 : CollatzResearch.WordTrace tailWord_1298461 prefixEnd_1298461 444489736078499666043995 := by
  unfold tailWord_1298461
  simp only [CollatzResearch.WordTrace]
  refine ⟨47358763348905031328735237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31572508899270020885823491 47358763348905031328735237)
  ·
    refine ⟨8879768127919693374137857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47358763348905031328735237 8879768127919693374137857)
    ·
      refine ⟨6659826095939770030603393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8879768127919693374137857 6659826095939770030603393)
      ·
        refine ⟨4994869571954827522952545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6659826095939770030603393 4994869571954827522952545)
        ·
          refine ⟨3746152178966120642214409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4994869571954827522952545 3746152178966120642214409)
          ·
            refine ⟨2809614134224590481660807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3746152178966120642214409 2809614134224590481660807)
            ·
              refine ⟨4214421201336885722491211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2809614134224590481660807 4214421201336885722491211)
              ·
                refine ⟨6321631802005328583736817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4214421201336885722491211 6321631802005328583736817)
                ·
                  refine ⟨4741223851503996437802613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6321631802005328583736817 4741223851503996437802613)
                  ·
                    refine ⟨444489736078499666043995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4741223851503996437802613 444489736078499666043995)
                    ·
                      rfl

theorem cell22_1298461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_1298461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298461 prefixEnd_1298461 := by exact prefixLift 1298461
  have htrace : WordTrace (prefixWord ++ tailWord_1298461) baseStart_1298461 baseEnd_1298461 := by
    simpa [prefixWord, tailWord_1298461, baseEnd_1298461] using wordTrace_append hprefix tailTrace_1298461
  have hstable : (prefixWord ++ tailWord_1298461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298461).length < 2 ^ (prefixWord ++ tailWord_1298461).sum := by decide
  have hdescent : baseEnd_1298461 < baseStart_1298461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298574 : List Nat := [4, 1, 1, 3, 4, 1, 2, 1, 2, 3]
def baseStart_1298574 : Nat := 118140960795 + 1298574 * 2 ^ 59
def prefixEnd_1298574 : Nat := 4983230072969 + 3 ^ 40 * 1298574 * 2
def baseEnd_1298574 : Nat := 444528418287805037968649

theorem tailTrace_1298574 : CollatzResearch.WordTrace tailWord_1298574 prefixEnd_1298574 444528418287805037968649 := by
  unfold tailWord_1298574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5920360599686956453449847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31575256531663767751732517 5920360599686956453449847)
  ·
    refine ⟨8880540899530434680174771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5920360599686956453449847 8880540899530434680174771)
    ·
      refine ⟨13320811349295652020262157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8880540899530434680174771 13320811349295652020262157)
      ·
        refine ⟨4995304255985869507598309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13320811349295652020262157 4995304255985869507598309)
        ·
          refine ⟨936619547997350532674683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4995304255985869507598309 936619547997350532674683)
          ·
            refine ⟨1404929321996025799012025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936619547997350532674683 1404929321996025799012025)
            ·
              refine ⟨1053696991497019349259019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1404929321996025799012025 1053696991497019349259019)
              ·
                refine ⟨1580545487245529023888529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053696991497019349259019 1580545487245529023888529)
                ·
                  refine ⟨1185409115434146767916397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1580545487245529023888529 1185409115434146767916397)
                  ·
                    refine ⟨444528418287805037968649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1185409115434146767916397 444528418287805037968649)
                    ·
                      rfl

theorem cell22_1298574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 2, 1, 2, 3].length) (baseStart_1298574 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298574 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298574 prefixEnd_1298574 := by exact prefixLift 1298574
  have htrace : WordTrace (prefixWord ++ tailWord_1298574) baseStart_1298574 baseEnd_1298574 := by
    simpa [prefixWord, tailWord_1298574, baseEnd_1298574] using wordTrace_append hprefix tailTrace_1298574
  have hstable : (prefixWord ++ tailWord_1298574).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298574).length < 2 ^ (prefixWord ++ tailWord_1298574).sum := by decide
  have hdescent : baseEnd_1298574 < baseStart_1298574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298579 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 1, 7]
def baseStart_1298579 : Nat := 118140960795 + 1298579 * 2 ^ 59
def prefixEnd_1298579 : Nat := 4983230072969 + 3 ^ 40 * 1298579 * 2
def baseEnd_1298579 : Nat := 444530129889986691593633

theorem tailTrace_1298579 : CollatzResearch.WordTrace tailWord_1298579 prefixEnd_1298579 444530129889986691593633 := by
  unfold tailWord_1298579
  simp only [CollatzResearch.WordTrace]
  refine ⟨47363067162477537481530791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31575378108318358321020527 47363067162477537481530791)
  ·
    refine ⟨71044600743716306222296187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47363067162477537481530791 71044600743716306222296187)
    ·
      refine ⟨106566901115574459333444281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71044600743716306222296187 106566901115574459333444281)
      ·
        refine ⟨79925175836680844500083211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106566901115574459333444281 79925175836680844500083211)
        ·
          refine ⟨119887763755021266750124817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79925175836680844500083211 119887763755021266750124817)
          ·
            refine ⟨89915822816265950062593613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119887763755021266750124817 89915822816265950062593613)
            ·
              refine ⟨33718433556099731273472605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 89915822816265950062593613 33718433556099731273472605)
              ·
                refine ⟨12644412583537399227552227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33718433556099731273472605 12644412583537399227552227)
                ·
                  refine ⟨18966618875306098841328341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12644412583537399227552227 18966618875306098841328341)
                  ·
                    refine ⟨444530129889986691593633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18966618875306098841328341 444530129889986691593633)
                    ·
                      rfl

theorem cell22_1298579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 7].length) (baseStart_1298579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298579 prefixEnd_1298579 := by exact prefixLift 1298579
  have htrace : WordTrace (prefixWord ++ tailWord_1298579) baseStart_1298579 baseEnd_1298579 := by
    simpa [prefixWord, tailWord_1298579, baseEnd_1298579] using wordTrace_append hprefix tailTrace_1298579
  have hstable : (prefixWord ++ tailWord_1298579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298579).length < 2 ^ (prefixWord ++ tailWord_1298579).sum := by decide
  have hdescent : baseEnd_1298579 < baseStart_1298579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298581 : List Nat := [1, 3, 2, 1, 1, 1, 5, 3, 5]
def baseStart_1298581 : Nat := 118140960795 + 1298581 * 2 ^ 59
def prefixEnd_1298581 : Nat := 4983230072969 + 3 ^ 40 * 1298581 * 2
def baseEnd_1298581 : Nat := 148176938176953117681209

theorem tailTrace_1298581 : CollatzResearch.WordTrace tailWord_1298581 prefixEnd_1298581 148176938176953117681209 := by
  unfold tailWord_1298581
  simp only [CollatzResearch.WordTrace]
  refine ⟨47363140108470291823103597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31575426738980194548735731 47363140108470291823103597)
  ·
    refine ⟨17761177540676359433663849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47363140108470291823103597 17761177540676359433663849)
    ·
      refine ⟨13320883155507269575247887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17761177540676359433663849 13320883155507269575247887)
      ·
        refine ⟨19981324733260904362871831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13320883155507269575247887 19981324733260904362871831)
        ·
          refine ⟨29971987099891356544307747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19981324733260904362871831 29971987099891356544307747)
          ·
            refine ⟨44957980649837034816461621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29971987099891356544307747 44957980649837034816461621)
            ·
              refine ⟨4214810685922222014043277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44957980649837034816461621 4214810685922222014043277)
              ·
                refine ⟨1580554007220833255266229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4214810685922222014043277 1580554007220833255266229)
                ·
                  refine ⟨148176938176953117681209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1580554007220833255266229 148176938176953117681209)
                  ·
                    rfl

theorem cell22_1298581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_1298581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298581 prefixEnd_1298581 := by exact prefixLift 1298581
  have htrace : WordTrace (prefixWord ++ tailWord_1298581) baseStart_1298581 baseEnd_1298581 := by
    simpa [prefixWord, tailWord_1298581, baseEnd_1298581] using wordTrace_append hprefix tailTrace_1298581
  have hstable : (prefixWord ++ tailWord_1298581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298581).length < 2 ^ (prefixWord ++ tailWord_1298581).sum := by decide
  have hdescent : baseEnd_1298581 < baseStart_1298581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298628 : List Nat := [2, 3, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1298628 : Nat := 118140960795 + 1298628 * 2 ^ 59
def prefixEnd_1298628 : Nat := 4983230072969 + 3 ^ 40 * 1298628 * 2
def baseEnd_1298628 : Nat := 444546903591366897118483

theorem tailTrace_1298628 : CollatzResearch.WordTrace tailWord_1298628 prefixEnd_1298628 444546903591366897118483 := by
  unfold tailWord_1298628
  simp only [CollatzResearch.WordTrace]
  refine ⟨23682427169650009425032269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31576569559533345900043025 23682427169650009425032269)
  ·
    refine ⟨8880910188618753534387101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23682427169650009425032269 8880910188618753534387101)
    ·
      refine ⟨3330341320732032575395163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8880910188618753534387101 3330341320732032575395163)
      ·
        refine ⟨4995511981098048863092745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3330341320732032575395163 4995511981098048863092745)
        ·
          refine ⟨3746633985823536647319559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4995511981098048863092745 3746633985823536647319559)
          ·
            refine ⟨5619950978735304970979339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3746633985823536647319559 5619950978735304970979339)
            ·
              refine ⟨8429926468102957456469009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5619950978735304970979339 8429926468102957456469009)
              ·
                refine ⟨6322444851077218092351757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8429926468102957456469009 6322444851077218092351757)
                ·
                  refine ⟨2370916819153956784631909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6322444851077218092351757 2370916819153956784631909)
                  ·
                    refine ⟨444546903591366897118483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2370916819153956784631909 444546903591366897118483)
                    ·
                      rfl

theorem cell22_1298628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1298628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298628 prefixEnd_1298628 := by exact prefixLift 1298628
  have htrace : WordTrace (prefixWord ++ tailWord_1298628) baseStart_1298628 baseEnd_1298628 := by
    simpa [prefixWord, tailWord_1298628, baseEnd_1298628] using wordTrace_append hprefix tailTrace_1298628
  have hstable : (prefixWord ++ tailWord_1298628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298628).length < 2 ^ (prefixWord ++ tailWord_1298628).sum := by decide
  have hdescent : baseEnd_1298628 < baseStart_1298628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298641 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 1, 5]
def baseStart_1298641 : Nat := 118140960795 + 1298641 * 2 ^ 59
def prefixEnd_1298641 : Nat := 4983230072969 + 3 ^ 40 * 1298641 * 2
def baseEnd_1298641 : Nat := 444551353757039196543443

theorem tailTrace_1298641 : CollatzResearch.WordTrace tailWord_1298641 prefixEnd_1298641 444551353757039196543443 := by
  unfold tailWord_1298641
  simp only [CollatzResearch.WordTrace]
  refine ⟨47365328488252922070287777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31576885658835281380191851 47365328488252922070287777)
  ·
    refine ⟨35523996366189691552715833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47365328488252922070287777 35523996366189691552715833)
    ·
      refine ⟨26642997274642268664536875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35523996366189691552715833 26642997274642268664536875)
      ·
        refine ⟨39964495911963402996805313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26642997274642268664536875 39964495911963402996805313)
        ·
          refine ⟨29973371933972552247603985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39964495911963402996805313 29973371933972552247603985)
          ·
            refine ⟨22480028950479414185702989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29973371933972552247603985 22480028950479414185702989)
            ·
              refine ⟨8430010856429780319638621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22480028950479414185702989 8430010856429780319638621)
              ·
                refine ⟨3161254071161167619864483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8430010856429780319638621 3161254071161167619864483)
                ·
                  refine ⟨4741881106741751429796725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161254071161167619864483 4741881106741751429796725)
                  ·
                    refine ⟨444551353757039196543443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4741881106741751429796725 444551353757039196543443)
                    ·
                      rfl

theorem cell22_1298641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 5].length) (baseStart_1298641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298641 prefixEnd_1298641 := by exact prefixLift 1298641
  have htrace : WordTrace (prefixWord ++ tailWord_1298641) baseStart_1298641 baseEnd_1298641 := by
    simpa [prefixWord, tailWord_1298641, baseEnd_1298641] using wordTrace_append hprefix tailTrace_1298641
  have hstable : (prefixWord ++ tailWord_1298641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298641).length < 2 ^ (prefixWord ++ tailWord_1298641).sum := by decide
  have hdescent : baseEnd_1298641 < baseStart_1298641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298656 : List Nat := [2, 1, 1, 3, 1, 3, 3, 1, 1, 6]
def baseStart_1298656 : Nat := 118140960795 + 1298656 * 2 ^ 59
def prefixEnd_1298656 : Nat := 4983230072969 + 3 ^ 40 * 1298656 * 2
def baseEnd_1298656 : Nat := 444556488563584157418397

theorem tailTrace_1298656 : CollatzResearch.WordTrace tailWord_1298656 prefixEnd_1298656 444556488563584157418397 := by
  unfold tailWord_1298656
  simp only [CollatzResearch.WordTrace]
  refine ⟨23682937791599289816041911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31577250388799053088055881 23682937791599289816041911)
  ·
    refine ⟨35524406687398934724062867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23682937791599289816041911 35524406687398934724062867)
    ·
      refine ⟨53286610031098402086094301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35524406687398934724062867 53286610031098402086094301)
      ·
        refine ⟨19982478761661900782285363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53286610031098402086094301 19982478761661900782285363)
        ·
          refine ⟨29973718142492851173428045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19982478761661900782285363 29973718142492851173428045)
          ·
            refine ⟨11240144303434819190035517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29973718142492851173428045 11240144303434819190035517)
            ·
              refine ⟨4215054113788057196263319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11240144303434819190035517 4215054113788057196263319)
              ·
                refine ⟨6322581170682085794394979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4215054113788057196263319 6322581170682085794394979)
                ·
                  refine ⟨9483871756023128691592469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6322581170682085794394979 9483871756023128691592469)
                  ·
                    refine ⟨444556488563584157418397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9483871756023128691592469 444556488563584157418397)
                    ·
                      rfl

theorem cell22_1298656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 3, 1, 1, 6].length) (baseStart_1298656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298656 prefixEnd_1298656 := by exact prefixLift 1298656
  have htrace : WordTrace (prefixWord ++ tailWord_1298656) baseStart_1298656 baseEnd_1298656 := by
    simpa [prefixWord, tailWord_1298656, baseEnd_1298656] using wordTrace_append hprefix tailTrace_1298656
  have hstable : (prefixWord ++ tailWord_1298656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298656).length < 2 ^ (prefixWord ++ tailWord_1298656).sum := by decide
  have hdescent : baseEnd_1298656 < baseStart_1298656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298671 : List Nat := [1, 1, 2, 1, 6, 2, 9]
def baseStart_1298671 : Nat := 118140960795 + 1298671 * 2 ^ 59
def prefixEnd_1298671 : Nat := 4983230072969 + 3 ^ 40 * 1298671 * 2
def baseEnd_1298671 : Nat := 16465245310004782159013

theorem tailTrace_1298671 : CollatzResearch.WordTrace tailWord_1298671 prefixEnd_1298671 16465245310004782159013 := by
  unfold tailWord_1298671
  simp only [CollatzResearch.WordTrace]
  refine ⟨47366422678144237193879867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31577615118762824795919911 47366422678144237193879867)
  ·
    refine ⟨71049634017216355790819801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47366422678144237193879867 71049634017216355790819801)
    ·
      refine ⟨53287225512912266843114851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71049634017216355790819801 53287225512912266843114851)
      ·
        refine ⟨79930838269368400264672277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53287225512912266843114851 79930838269368400264672277)
        ·
          refine ⟨3746758043876643762406513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79930838269368400264672277 3746758043876643762406513)
          ·
            refine ⟨2810068532907482821804885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3746758043876643762406513 2810068532907482821804885)
            ·
              refine ⟨16465245310004782159013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2810068532907482821804885 16465245310004782159013)
              ·
                rfl

theorem cell22_1298671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 2, 9].length) (baseStart_1298671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298671 prefixEnd_1298671 := by exact prefixLift 1298671
  have htrace : WordTrace (prefixWord ++ tailWord_1298671) baseStart_1298671 baseEnd_1298671 := by
    simpa [prefixWord, tailWord_1298671, baseEnd_1298671] using wordTrace_append hprefix tailTrace_1298671
  have hstable : (prefixWord ++ tailWord_1298671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298671).length < 2 ^ (prefixWord ++ tailWord_1298671).sum := by decide
  have hdescent : baseEnd_1298671 < baseStart_1298671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298692 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 1, 5]
def baseStart_1298692 : Nat := 118140960795 + 1298692 * 2 ^ 59
def prefixEnd_1298692 : Nat := 4983230072969 + 3 ^ 40 * 1298692 * 2
def baseEnd_1298692 : Nat := 444568812099292063518287

theorem tailTrace_1298692 : CollatzResearch.WordTrace tailWord_1298692 prefixEnd_1298692 444568812099292063518287 := by
  unfold tailWord_1298692
  simp only [CollatzResearch.WordTrace]
  refine ⟨23683594305534078890197165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31578125740712105186929553 23683594305534078890197165)
  ·
    refine ⟨8881347864575279583823937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23683594305534078890197165 8881347864575279583823937)
    ·
      refine ⟨6661010898431459687867953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8881347864575279583823937 6661010898431459687867953)
      ·
        refine ⟨4995758173823594765900965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6661010898431459687867953 4995758173823594765900965)
        ·
          refine ⟨936704657591924018606431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4995758173823594765900965 936704657591924018606431)
          ·
            refine ⟨1405056986387886027909647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936704657591924018606431 1405056986387886027909647)
            ·
              refine ⟨2107585479581829041864471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405056986387886027909647 2107585479581829041864471)
              ·
                refine ⟨3161378219372743562796707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107585479581829041864471 3161378219372743562796707)
                ·
                  refine ⟨4742067329059115344195061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3161378219372743562796707 4742067329059115344195061)
                  ·
                    refine ⟨444568812099292063518287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4742067329059115344195061 444568812099292063518287)
                    ·
                      rfl

theorem cell22_1298692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_1298692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298692 prefixEnd_1298692 := by exact prefixLift 1298692
  have htrace : WordTrace (prefixWord ++ tailWord_1298692) baseStart_1298692 baseEnd_1298692 := by
    simpa [prefixWord, tailWord_1298692, baseEnd_1298692] using wordTrace_append hprefix tailTrace_1298692
  have hstable : (prefixWord ++ tailWord_1298692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298692).length < 2 ^ (prefixWord ++ tailWord_1298692).sum := by decide
  have hdescent : baseEnd_1298692 < baseStart_1298692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298737 : List Nat := [1, 2, 2, 3, 4, 2, 1, 1, 3, 3]
def baseStart_1298737 : Nat := 118140960795 + 1298737 * 2 ^ 59
def prefixEnd_1298737 : Nat := 4983230072969 + 3 ^ 40 * 1298737 * 2
def baseEnd_1298737 : Nat := 444584216518926946143149

theorem tailTrace_1298737 : CollatzResearch.WordTrace tailWord_1298737 prefixEnd_1298737 444584216518926946143149 := by
  unfold tailWord_1298737
  simp only [CollatzResearch.WordTrace]
  refine ⟨47368829895905130465782465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31579219930603420310521643 47368829895905130465782465)
  ·
    refine ⟨35526622421928847849336849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47368829895905130465782465 35526622421928847849336849)
    ·
      refine ⟨26644966816446635887002637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35526622421928847849336849 26644966816446635887002637)
      ·
        refine ⟨9991862556167488457625989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26644966816446635887002637 9991862556167488457625989)
        ·
          refine ⟨1873474229281404085804873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9991862556167488457625989 1873474229281404085804873)
          ·
            refine ⟨1405105671961053064353655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1873474229281404085804873 1405105671961053064353655)
            ·
              refine ⟨2107658507941579596530483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405105671961053064353655 2107658507941579596530483)
              ·
                refine ⟨3161487761912369394795725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107658507941579596530483 3161487761912369394795725)
                ·
                  refine ⟨1185557910717138523048397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3161487761912369394795725 1185557910717138523048397)
                  ·
                    refine ⟨444584216518926946143149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1185557910717138523048397 444584216518926946143149)
                    ·
                      rfl

theorem cell22_1298737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 1, 1, 3, 3].length) (baseStart_1298737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298737 prefixEnd_1298737 := by exact prefixLift 1298737
  have htrace : WordTrace (prefixWord ++ tailWord_1298737) baseStart_1298737 baseEnd_1298737 := by
    simpa [prefixWord, tailWord_1298737, baseEnd_1298737] using wordTrace_append hprefix tailTrace_1298737
  have hstable : (prefixWord ++ tailWord_1298737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298737).length < 2 ^ (prefixWord ++ tailWord_1298737).sum := by decide
  have hdescent : baseEnd_1298737 < baseStart_1298737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298750 : List Nat := [4, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_1298750 : Nat := 118140960795 + 1298750 * 2 ^ 59
def prefixEnd_1298750 : Nat := 4983230072969 + 3 ^ 40 * 1298750 * 2
def baseEnd_1298750 : Nat := 148196222228199748522703

theorem tailTrace_1298750 : CollatzResearch.WordTrace tailWord_1298750 prefixEnd_1298750 148196222228199748522703 := by
  unfold tailWord_1298750
  simp only [CollatzResearch.WordTrace]
  refine ⟨5921163005607254210750713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31579536029905355790670469 5921163005607254210750713)
  ·
    refine ⟨4440872254205440658063035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5921163005607254210750713 4440872254205440658063035)
    ·
      refine ⟨6661308381308160987094553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4440872254205440658063035 6661308381308160987094553)
      ·
        refine ⟨4995981285981120740320915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6661308381308160987094553 4995981285981120740320915)
        ·
          refine ⟨7493971928971681110481373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4995981285981120740320915 7493971928971681110481373)
          ·
            refine ⟨2810239473364380416430515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7493971928971681110481373 2810239473364380416430515)
            ·
              refine ⟨4215359210046570624645773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2810239473364380416430515 4215359210046570624645773)
              ·
                refine ⟨1580759703767463984242165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4215359210046570624645773 1580759703767463984242165)
                ·
                  refine ⟨148196222228199748522703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1580759703767463984242165 148196222228199748522703)
                  ·
                    rfl

theorem cell22_1298750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_1298750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298750 prefixEnd_1298750 := by exact prefixLift 1298750
  have htrace : WordTrace (prefixWord ++ tailWord_1298750) baseStart_1298750 baseEnd_1298750 := by
    simpa [prefixWord, tailWord_1298750, baseEnd_1298750] using wordTrace_append hprefix tailTrace_1298750
  have hstable : (prefixWord ++ tailWord_1298750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298750).length < 2 ^ (prefixWord ++ tailWord_1298750).sum := by decide
  have hdescent : baseEnd_1298750 < baseStart_1298750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298761 : List Nat := [1, 2, 1, 1, 2, 3, 1, 3, 8]
def baseStart_1298761 : Nat := 118140960795 + 1298761 * 2 ^ 59
def prefixEnd_1298761 : Nat := 4983230072969 + 3 ^ 40 * 1298761 * 2
def baseEnd_1298761 : Nat := 148197477403132961181025

theorem tailTrace_1298761 : CollatzResearch.WordTrace tailWord_1298761 prefixEnd_1298761 148197477403132961181025 := by
  unfold tailWord_1298761
  simp only [CollatzResearch.WordTrace]
  refine ⟨47369705247818182564656137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31579803498545455043104091 47369705247818182564656137)
  ·
    refine ⟨35527278935863636923492103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47369705247818182564656137 35527278935863636923492103)
    ·
      refine ⟨53290918403795455385238155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35527278935863636923492103 53290918403795455385238155)
      ·
        refine ⟨79936377605693183077857233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53290918403795455385238155 79936377605693183077857233)
        ·
          refine ⟨59952283204269887308392925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79936377605693183077857233 59952283204269887308392925)
          ·
            refine ⟨22482106201601207740647347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59952283204269887308392925 22482106201601207740647347)
            ·
              refine ⟨33723159302401811610971021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22482106201601207740647347 33723159302401811610971021)
              ·
                refine ⟨12646184738400679354114133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33723159302401811610971021 12646184738400679354114133)
                ·
                  refine ⟨148197477403132961181025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12646184738400679354114133 148197477403132961181025)
                  ·
                    rfl

theorem cell22_1298761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 3, 8].length) (baseStart_1298761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298761 prefixEnd_1298761 := by exact prefixLift 1298761
  have htrace : WordTrace (prefixWord ++ tailWord_1298761) baseStart_1298761 baseEnd_1298761 := by
    simpa [prefixWord, tailWord_1298761, baseEnd_1298761] using wordTrace_append hprefix tailTrace_1298761
  have hstable : (prefixWord ++ tailWord_1298761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298761).length < 2 ^ (prefixWord ++ tailWord_1298761).sum := by decide
  have hdescent : baseEnd_1298761 < baseStart_1298761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298763 : List Nat := [1, 1, 1, 1, 3, 1, 1, 8, 1, 4]
def baseStart_1298763 : Nat := 118140960795 + 1298763 * 2 ^ 59
def prefixEnd_1298763 : Nat := 4983230072969 + 3 ^ 40 * 1298763 * 2
def baseEnd_1298763 : Nat := 444593116850271544993069

theorem tailTrace_1298763 : CollatzResearch.WordTrace tailWord_1298763 prefixEnd_1298763 444593116850271544993069 := by
  unfold tailWord_1298763
  simp only [CollatzResearch.WordTrace]
  refine ⟨47369778193810936906228943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31579852129207291270819295 47369778193810936906228943)
  ·
    refine ⟨71054667290716405359343415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47369778193810936906228943 71054667290716405359343415)
    ·
      refine ⟨106582000936074608039015123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71054667290716405359343415 106582000936074608039015123)
      ·
        refine ⟨159873001404111912058522685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106582000936074608039015123 159873001404111912058522685)
        ·
          refine ⟨59952375526541967021946007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159873001404111912058522685 59952375526541967021946007)
          ·
            refine ⟨89928563289812950532919011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59952375526541967021946007 89928563289812950532919011)
            ·
              refine ⟨134892844934719425799378517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89928563289812950532919011 134892844934719425799378517)
              ·
                refine ⟨1580775526578743271086467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 134892844934719425799378517 1580775526578743271086467)
                ·
                  refine ⟨2371163289868114906629701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1580775526578743271086467 2371163289868114906629701)
                  ·
                    refine ⟨444593116850271544993069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2371163289868114906629701 444593116850271544993069)
                    ·
                      rfl

theorem cell22_1298763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 8, 1, 4].length) (baseStart_1298763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298763 prefixEnd_1298763 := by exact prefixLift 1298763
  have htrace : WordTrace (prefixWord ++ tailWord_1298763) baseStart_1298763 baseEnd_1298763 := by
    simpa [prefixWord, tailWord_1298763, baseEnd_1298763] using wordTrace_append hprefix tailTrace_1298763
  have hstable : (prefixWord ++ tailWord_1298763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298763).length < 2 ^ (prefixWord ++ tailWord_1298763).sum := by decide
  have hdescent : baseEnd_1298763 < baseStart_1298763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298825 : List Nat := [1, 2, 1, 1, 6, 1, 3, 1, 2, 4]
def baseStart_1298825 : Nat := 118140960795 + 1298825 * 2 ^ 59
def prefixEnd_1298825 : Nat := 4983230072969 + 3 ^ 40 * 1298825 * 2
def baseEnd_1298825 : Nat := 444614340717324049942879

theorem tailTrace_1298825 : CollatzResearch.WordTrace tailWord_1298825 prefixEnd_1298825 444614340717324049942879 := by
  unfold tailWord_1298825
  simp only [CollatzResearch.WordTrace]
  refine ⟨47372039519586321494985929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31581359679724214329990619 47372039519586321494985929)
  ·
    refine ⟨35529029639689741121239447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47372039519586321494985929 35529029639689741121239447)
    ·
      refine ⟨53293544459534611681859171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35529029639689741121239447 53293544459534611681859171)
      ·
        refine ⟨79940316689301917522788757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53293544459534611681859171 79940316689301917522788757)
        ·
          refine ⟨3747202344811027383880723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 79940316689301917522788757 3747202344811027383880723)
          ·
            refine ⟨5620803517216541075821085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3747202344811027383880723 5620803517216541075821085)
            ·
              refine ⟨2107801318956202903432907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5620803517216541075821085 2107801318956202903432907)
              ·
                refine ⟨3161701978434304355149361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2107801318956202903432907 3161701978434304355149361)
                ·
                  refine ⟨2371276483825728266362021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3161701978434304355149361 2371276483825728266362021)
                  ·
                    refine ⟨444614340717324049942879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2371276483825728266362021 444614340717324049942879)
                    ·
                      rfl

theorem cell22_1298825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 3, 1, 2, 4].length) (baseStart_1298825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298825 prefixEnd_1298825 := by exact prefixLift 1298825
  have htrace : WordTrace (prefixWord ++ tailWord_1298825) baseStart_1298825 baseEnd_1298825 := by
    simpa [prefixWord, tailWord_1298825, baseEnd_1298825] using wordTrace_append hprefix tailTrace_1298825
  have hstable : (prefixWord ++ tailWord_1298825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298825).length < 2 ^ (prefixWord ++ tailWord_1298825).sum := by decide
  have hdescent : baseEnd_1298825 < baseStart_1298825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298861 : List Nat := [1, 5, 2, 2, 2, 1, 3, 1, 2, 3]
def baseStart_1298861 : Nat := 118140960795 + 1298861 * 2 ^ 59
def prefixEnd_1298861 : Nat := 4983230072969 + 3 ^ 40 * 1298861 * 2
def baseEnd_1298861 : Nat := 444626664253031956042769

theorem tailTrace_1298861 : CollatzResearch.WordTrace tailWord_1298861 prefixEnd_1298861 444626664253031956042769 := by
  unfold tailWord_1298861
  simp only [CollatzResearch.WordTrace]
  refine ⟨47373352547455899643296437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31582235031637266428864291 47373352547455899643296437)
  ·
    refine ⟨4441251801323990591559041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47373352547455899643296437 4441251801323990591559041)
    ·
      refine ⟨3330938850992992943669281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4441251801323990591559041 3330938850992992943669281)
      ·
        refine ⟨2498204138244744707751961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3330938850992992943669281 2498204138244744707751961)
        ·
          refine ⟨1873653103683558530813971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2498204138244744707751961 1873653103683558530813971)
          ·
            refine ⟨2810479655525337796220957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1873653103683558530813971 2810479655525337796220957)
            ·
              refine ⟨1053929870822001673582859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2810479655525337796220957 1053929870822001673582859)
              ·
                refine ⟨1580894806233002510374289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1053929870822001673582859 1580894806233002510374289)
                ·
                  refine ⟨1185671104674751882780717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1580894806233002510374289 1185671104674751882780717)
                  ·
                    refine ⟨444626664253031956042769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1185671104674751882780717 444626664253031956042769)
                    ·
                      rfl

theorem cell22_1298861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_1298861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298861 prefixEnd_1298861 := by exact prefixLift 1298861
  have htrace : WordTrace (prefixWord ++ tailWord_1298861) baseStart_1298861 baseEnd_1298861 := by
    simpa [prefixWord, tailWord_1298861, baseEnd_1298861] using wordTrace_append hprefix tailTrace_1298861
  have hstable : (prefixWord ++ tailWord_1298861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298861).length < 2 ^ (prefixWord ++ tailWord_1298861).sum := by decide
  have hdescent : baseEnd_1298861 < baseStart_1298861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298902 : List Nat := [5, 2, 1, 1, 1, 1, 2, 4, 5]
def baseStart_1298902 : Nat := 118140960795 + 1298902 * 2 ^ 59
def prefixEnd_1298902 : Nat := 4983230072969 + 3 ^ 40 * 1298902 * 2
def baseEnd_1298902 : Nat := 148213566463640505255881

theorem tailTrace_1298902 : CollatzResearch.WordTrace tailWord_1298902 prefixEnd_1298902 148213566463640505255881 := by
  unfold tailWord_1298902
  simp only [CollatzResearch.WordTrace]
  refine ⟨2960927996269210227846185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31583231960204909097025973 2960927996269210227846185)
  ·
    refine ⟨2220695997201907670884639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2960927996269210227846185 2220695997201907670884639)
    ·
      refine ⟨3331043995802861506326959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2220695997201907670884639 3331043995802861506326959)
      ·
        refine ⟨4996565993704292259490439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3331043995802861506326959 4996565993704292259490439)
        ·
          refine ⟨7494848990556438389235659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4996565993704292259490439 7494848990556438389235659)
          ·
            refine ⟨11242273485834657583853489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7494848990556438389235659 11242273485834657583853489)
            ·
              refine ⟨8431705114375993187890117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11242273485834657583853489 8431705114375993187890117)
              ·
                refine ⟨1580944708945498722729397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8431705114375993187890117 1580944708945498722729397)
                ·
                  refine ⟨148213566463640505255881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1580944708945498722729397 148213566463640505255881)
                  ·
                    rfl

theorem cell22_1298902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_1298902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298902 prefixEnd_1298902 := by exact prefixLift 1298902
  have htrace : WordTrace (prefixWord ++ tailWord_1298902) baseStart_1298902 baseEnd_1298902 := by
    simpa [prefixWord, tailWord_1298902, baseEnd_1298902] using wordTrace_append hprefix tailTrace_1298902
  have hstable : (prefixWord ++ tailWord_1298902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298902).length < 2 ^ (prefixWord ++ tailWord_1298902).sum := by decide
  have hdescent : baseEnd_1298902 < baseStart_1298902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1298945 : List Nat := [1, 2, 4, 1, 3, 1, 1, 1, 3, 5]
def baseStart_1298945 : Nat := 118140960795 + 1298945 * 2 ^ 59
def prefixEnd_1298945 : Nat := 4983230072969 + 3 ^ 40 * 1298945 * 2
def baseEnd_1298945 : Nat := 444655419169683736942511

theorem tailTrace_1298945 : CollatzResearch.WordTrace tailWord_1298945 prefixEnd_1298945 444655419169683736942511 := by
  unfold tailWord_1298945
  simp only [CollatzResearch.WordTrace]
  refine ⟨47376416279151581989354289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31584277519434387992902859 47376416279151581989354289)
  ·
    refine ⟨35532312209363686492015717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47376416279151581989354289 35532312209363686492015717)
    ·
      refine ⟨6662308539255691217252947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35532312209363686492015717 6662308539255691217252947)
      ·
        refine ⟨9993462808883536825879421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6662308539255691217252947 9993462808883536825879421)
        ·
          refine ⟨3747548553331326309704783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9993462808883536825879421 3747548553331326309704783)
          ·
            refine ⟨5621322829996989464557175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3747548553331326309704783 5621322829996989464557175)
            ·
              refine ⟨8431984244995484196835763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5621322829996989464557175 8431984244995484196835763)
              ·
                refine ⟨12647976367493226295253645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8431984244995484196835763 12647976367493226295253645)
                ·
                  refine ⟨4742991137809959860720117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12647976367493226295253645 4742991137809959860720117)
                  ·
                    refine ⟨444655419169683736942511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4742991137809959860720117 444655419169683736942511)
                    ·
                      rfl

theorem cell22_1298945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_1298945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1298945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1298945 prefixEnd_1298945 := by exact prefixLift 1298945
  have htrace : WordTrace (prefixWord ++ tailWord_1298945) baseStart_1298945 baseEnd_1298945 := by
    simpa [prefixWord, tailWord_1298945, baseEnd_1298945] using wordTrace_append hprefix tailTrace_1298945
  have hstable : (prefixWord ++ tailWord_1298945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1298945).length < 2 ^ (prefixWord ++ tailWord_1298945).sum := by decide
  have hdescent : baseEnd_1298945 < baseStart_1298945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1298945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299020 : List Nat := [2, 2, 1, 3, 1, 2, 3, 1, 7]
def baseStart_1299020 : Nat := 118140960795 + 1299020 * 2 ^ 59
def prefixEnd_1299020 : Nat := 4983230072969 + 3 ^ 40 * 1299020 * 2
def baseEnd_1299020 : Nat := 148227031067469513772427

theorem tailTrace_1299020 : CollatzResearch.WordTrace tailWord_1299020 prefixEnd_1299020 148227031067469513772427 := by
  unfold tailWord_1299020
  simp only [CollatzResearch.WordTrace]
  refine ⟨23689575876939934899167257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31586101169253246532223009 23689575876939934899167257)
  ·
    refine ⟨17767181907704951174375443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23689575876939934899167257 17767181907704951174375443)
    ·
      refine ⟨26650772861557426761563165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17767181907704951174375443 26650772861557426761563165)
      ·
        refine ⟨9994039823084035035586187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26650772861557426761563165 9994039823084035035586187)
        ·
          refine ⟨14991059734626052553379281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9994039823084035035586187 14991059734626052553379281)
          ·
            refine ⟨11243294800969539415034461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14991059734626052553379281 11243294800969539415034461)
            ·
              refine ⟨4216235550363577280637923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11243294800969539415034461 4216235550363577280637923)
              ·
                refine ⟨6324353325545365920956885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4216235550363577280637923 6324353325545365920956885)
                ·
                  refine ⟨148227031067469513772427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6324353325545365920956885 148227031067469513772427)
                  ·
                    rfl

theorem cell22_1299020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 1, 7].length) (baseStart_1299020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299020 prefixEnd_1299020 := by exact prefixLift 1299020
  have htrace : WordTrace (prefixWord ++ tailWord_1299020) baseStart_1299020 baseEnd_1299020 := by
    simpa [prefixWord, tailWord_1299020, baseEnd_1299020] using wordTrace_append hprefix tailTrace_1299020
  have hstable : (prefixWord ++ tailWord_1299020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299020).length < 2 ^ (prefixWord ++ tailWord_1299020).sum := by decide
  have hdescent : baseEnd_1299020 < baseStart_1299020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299058 : List Nat := [3, 2, 1, 2, 4, 2, 1, 3, 1, 3]
def baseStart_1299058 : Nat := 118140960795 + 1299058 * 2 ^ 59
def prefixEnd_1299058 : Nat := 4983230072969 + 3 ^ 40 * 1299058 * 2
def baseEnd_1299058 : Nat := 444694101378989108867165

theorem tailTrace_1299058 : CollatzResearch.WordTrace tailWord_1299058 prefixEnd_1299058 444694101378989108867165 := by
  unfold tailWord_1299058
  simp only [CollatzResearch.WordTrace]
  refine ⟨11845134431935550572054457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31587025151828134858811885 11845134431935550572054457)
  ·
    refine ⟨8883850823951662929040843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11845134431935550572054457 8883850823951662929040843)
    ·
      refine ⟨13325776235927494393561265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8883850823951662929040843 13325776235927494393561265)
      ·
        refine ⟨9994332176945620795170949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13325776235927494393561265 9994332176945620795170949)
        ·
          refine ⟨1873937283177303899094553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9994332176945620795170949 1873937283177303899094553)
          ·
            refine ⟨1405452962382977924320915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1873937283177303899094553 1405452962382977924320915)
            ·
              refine ⟨2108179443574466886481373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405452962382977924320915 2108179443574466886481373)
              ·
                refine ⟨790567291340425082430515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2108179443574466886481373 790567291340425082430515)
                ·
                  refine ⟨1185850937010637623645773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790567291340425082430515 1185850937010637623645773)
                  ·
                    refine ⟨444694101378989108867165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1185850937010637623645773 444694101378989108867165)
                    ·
                      rfl

theorem cell22_1299058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 3, 1, 3].length) (baseStart_1299058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299058 prefixEnd_1299058 := by exact prefixLift 1299058
  have htrace : WordTrace (prefixWord ++ tailWord_1299058) baseStart_1299058 baseEnd_1299058 := by
    simpa [prefixWord, tailWord_1299058, baseEnd_1299058] using wordTrace_append hprefix tailTrace_1299058
  have hstable : (prefixWord ++ tailWord_1299058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299058).length < 2 ^ (prefixWord ++ tailWord_1299058).sum := by decide
  have hdescent : baseEnd_1299058 < baseStart_1299058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299118 : List Nat := [4, 1, 4, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1299118 : Nat := 118140960795 + 1299118 * 2 ^ 59
def prefixEnd_1299118 : Nat := 4983230072969 + 3 ^ 40 * 1299118 * 2
def baseEnd_1299118 : Nat := 444714640605168952366981

theorem tailTrace_1299118 : CollatzResearch.WordTrace tailWord_1299118 prefixEnd_1299118 444714640605168952366981 := by
  unfold tailWord_1299118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5922840763440604066925251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31588484071683221690268005 5922840763440604066925251)
  ·
    refine ⟨8884261145160906100387877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5922840763440604066925251 8884261145160906100387877)
    ·
      refine ⟨1665798964717669893822727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8884261145160906100387877 1665798964717669893822727)
      ·
        refine ⟨2498698447076504840734091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1665798964717669893822727 2498698447076504840734091)
        ·
          refine ⟨3748047670614757261101137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2498698447076504840734091 3748047670614757261101137)
          ·
            refine ⟨2811035752961067945825853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3748047670614757261101137 2811035752961067945825853)
            ·
              refine ⟨1054138407360400479684695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2811035752961067945825853 1054138407360400479684695)
              ·
                refine ⟨1581207611040600719527043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054138407360400479684695 1581207611040600719527043)
                ·
                  refine ⟨2371811416560901079290565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581207611040600719527043 2371811416560901079290565)
                  ·
                    refine ⟨444714640605168952366981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2371811416560901079290565 444714640605168952366981)
                    ·
                      rfl

theorem cell22_1299118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1299118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299118 prefixEnd_1299118 := by exact prefixLift 1299118
  have htrace : WordTrace (prefixWord ++ tailWord_1299118) baseStart_1299118 baseEnd_1299118 := by
    simpa [prefixWord, tailWord_1299118, baseEnd_1299118] using wordTrace_append hprefix tailTrace_1299118
  have hstable : (prefixWord ++ tailWord_1299118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299118).length < 2 ^ (prefixWord ++ tailWord_1299118).sum := by decide
  have hdescent : baseEnd_1299118 < baseStart_1299118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299127 : List Nat := [1, 1, 3, 1, 7, 9]
def baseStart_1299127 : Nat := 118140960795 + 1299127 * 2 ^ 59
def prefixEnd_1299127 : Nat := 4983230072969 + 3 ^ 40 * 1299127 * 2
def baseEnd_1299127 : Nat := 5490342240606122578913

theorem tailTrace_1299127 : CollatzResearch.WordTrace tailWord_1299127 prefixEnd_1299127 5490342240606122578913 := by
  unfold tailWord_1299127
  simp only [CollatzResearch.WordTrace]
  refine ⟨47383054364492227072479635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31588702909661484714986423 47383054364492227072479635)
  ·
    refine ⟨71074581546738340608719453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47383054364492227072479635 71074581546738340608719453)
    ·
      refine ⟨26652968080026877728269795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71074581546738340608719453 26652968080026877728269795)
      ·
        refine ⟨39979452120040316592404693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26652968080026877728269795 39979452120040316592404693)
        ·
          refine ⟨937018409063444920134485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 39979452120040316592404693 937018409063444920134485)
          ·
            refine ⟨5490342240606122578913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 937018409063444920134485 5490342240606122578913)
            ·
              rfl

theorem cell22_1299127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 9].length) (baseStart_1299127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299127 prefixEnd_1299127 := by exact prefixLift 1299127
  have htrace : WordTrace (prefixWord ++ tailWord_1299127) baseStart_1299127 baseEnd_1299127 := by
    simpa [prefixWord, tailWord_1299127, baseEnd_1299127] using wordTrace_append hprefix tailTrace_1299127
  have hstable : (prefixWord ++ tailWord_1299127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299127).length < 2 ^ (prefixWord ++ tailWord_1299127).sum := by decide
  have hdescent : baseEnd_1299127 < baseStart_1299127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299159 : List Nat := [1, 1, 3, 2, 1, 5, 1, 2, 3, 3]
def baseStart_1299159 : Nat := 118140960795 + 1299159 * 2 ^ 59
def prefixEnd_1299159 : Nat := 4983230072969 + 3 ^ 40 * 1299159 * 2
def baseEnd_1299159 : Nat := 444728675743058512091855

theorem tailTrace_1299159 : CollatzResearch.WordTrace tailWord_1299159 prefixEnd_1299159 444728675743058512091855 := by
  unfold tailWord_1299159
  simp only [CollatzResearch.WordTrace]
  refine ⟨47384221500376296537644531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31589481000250864358429687 47384221500376296537644531)
  ·
    refine ⟨71076332250564444806466797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47384221500376296537644531 71076332250564444806466797)
    ·
      refine ⟨26653624593961666802425049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71076332250564444806466797 26653624593961666802425049)
      ·
        refine ⟨19990218445471250101818787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26653624593961666802425049 19990218445471250101818787)
        ·
          refine ⟨29985327668206875152728181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19990218445471250101818787 29985327668206875152728181)
          ·
            refine ⟨2811124468894394545568267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29985327668206875152728181 2811124468894394545568267)
            ·
              refine ⟨4216686703341591818352401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811124468894394545568267 4216686703341591818352401)
              ·
                refine ⟨3162515027506193863764301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4216686703341591818352401 3162515027506193863764301)
                ·
                  refine ⟨1185943135314822698911613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3162515027506193863764301 1185943135314822698911613)
                  ·
                    refine ⟨444728675743058512091855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1185943135314822698911613 444728675743058512091855)
                    ·
                      rfl

theorem cell22_1299159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 2, 3, 3].length) (baseStart_1299159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299159 prefixEnd_1299159 := by exact prefixLift 1299159
  have htrace : WordTrace (prefixWord ++ tailWord_1299159) baseStart_1299159 baseEnd_1299159 := by
    simpa [prefixWord, tailWord_1299159, baseEnd_1299159] using wordTrace_append hprefix tailTrace_1299159
  have hstable : (prefixWord ++ tailWord_1299159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299159).length < 2 ^ (prefixWord ++ tailWord_1299159).sum := by decide
  have hdescent : baseEnd_1299159 < baseStart_1299159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299217 : List Nat := [1, 2, 2, 1, 1, 3, 4, 2, 6]
def baseStart_1299217 : Nat := 118140960795 + 1299217 * 2 ^ 59
def prefixEnd_1299217 : Nat := 4983230072969 + 3 ^ 40 * 1299217 * 2
def baseEnd_1299217 : Nat := 148249510109455231380559

theorem tailTrace_1299217 : CollatzResearch.WordTrace tailWord_1299217 prefixEnd_1299217 148249510109455231380559 := by
  unfold tailWord_1299217
  simp only [CollatzResearch.WordTrace]
  refine ⟨47386336934166172443255905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31590891289444114962170603 47386336934166172443255905)
  ·
    refine ⟨35539752700624629332441929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47386336934166172443255905 35539752700624629332441929)
    ·
      refine ⟨26654814525468471999331447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35539752700624629332441929 26654814525468471999331447)
      ·
        refine ⟨39982221788202707998997171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26654814525468471999331447 39982221788202707998997171)
        ·
          refine ⟨59973332682304061998495757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39982221788202707998997171 59973332682304061998495757)
          ·
            refine ⟨22489999755864023249435909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 59973332682304061998495757 22489999755864023249435909)
            ·
              refine ⟨4216874954224504359269233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22489999755864023249435909 4216874954224504359269233)
              ·
                refine ⟨3162656215668378269451925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4216874954224504359269233 3162656215668378269451925)
                ·
                  refine ⟨148249510109455231380559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3162656215668378269451925 148249510109455231380559)
                  ·
                    rfl

theorem cell22_1299217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 4, 2, 6].length) (baseStart_1299217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299217 prefixEnd_1299217 := by exact prefixLift 1299217
  have htrace : WordTrace (prefixWord ++ tailWord_1299217) baseStart_1299217 baseEnd_1299217 := by
    simpa [prefixWord, tailWord_1299217, baseEnd_1299217] using wordTrace_append hprefix tailTrace_1299217
  have hstable : (prefixWord ++ tailWord_1299217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299217).length < 2 ^ (prefixWord ++ tailWord_1299217).sum := by decide
  have hdescent : baseEnd_1299217 < baseStart_1299217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299219 : List Nat := [1, 1, 1, 2, 1, 3, 6, 2, 1, 4]
def baseStart_1299219 : Nat := 118140960795 + 1299219 * 2 ^ 59
def prefixEnd_1299219 : Nat := 4983230072969 + 3 ^ 40 * 1299219 * 2
def baseEnd_1299219 : Nat := 444749214969238355591671

theorem tailTrace_1299219 : CollatzResearch.WordTrace tailWord_1299219 prefixEnd_1299219 444749214969238355591671 := by
  unfold tailWord_1299219
  simp only [CollatzResearch.WordTrace]
  refine ⟨47386409880158926784828711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31590939920105951189885807 47386409880158926784828711)
  ·
    refine ⟨71079614820238390177243067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47386409880158926784828711 71079614820238390177243067)
    ·
      refine ⟨106619422230357585265864601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71079614820238390177243067 106619422230357585265864601)
      ·
        refine ⟨79964566672768188949398451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106619422230357585265864601 79964566672768188949398451)
        ·
          refine ⟨119946850009152283424097677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79964566672768188949398451 119946850009152283424097677)
          ·
            refine ⟨44980068753432106284036629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 119946850009152283424097677 44980068753432106284036629)
            ·
              refine ⟨2108440722817129982064217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44980068753432106284036629 2108440722817129982064217)
              ·
                refine ⟨1581330542112847486548163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2108440722817129982064217 1581330542112847486548163)
                ·
                  refine ⟨2371995813169271229822245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581330542112847486548163 2371995813169271229822245)
                  ·
                    refine ⟨444749214969238355591671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2371995813169271229822245 444749214969238355591671)
                    ·
                      rfl

theorem cell22_1299219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 6, 2, 1, 4].length) (baseStart_1299219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299219 prefixEnd_1299219 := by exact prefixLift 1299219
  have htrace : WordTrace (prefixWord ++ tailWord_1299219) baseStart_1299219 baseEnd_1299219 := by
    simpa [prefixWord, tailWord_1299219, baseEnd_1299219] using wordTrace_append hprefix tailTrace_1299219
  have hstable : (prefixWord ++ tailWord_1299219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299219).length < 2 ^ (prefixWord ++ tailWord_1299219).sum := by decide
  have hdescent : baseEnd_1299219 < baseStart_1299219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299249 : List Nat := [1, 2, 2, 3, 2, 1, 1, 3, 4, 3]
def baseStart_1299249 : Nat := 118140960795 + 1299249 * 2 ^ 59
def prefixEnd_1299249 : Nat := 4983230072969 + 3 ^ 40 * 1299249 * 2
def baseEnd_1299249 : Nat := 444759484582328277341579

theorem tailTrace_1299249 : CollatzResearch.WordTrace tailWord_1299249 prefixEnd_1299249 444759484582328277341579 := by
  unfold tailWord_1299249
  simp only [CollatzResearch.WordTrace]
  refine ⟨47387504070050241908420801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31591669380033494605613867 47387504070050241908420801)
  ·
    refine ⟨35540628052537681431315601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47387504070050241908420801 35540628052537681431315601)
    ·
      refine ⟨26655471039403261073486701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35540628052537681431315601 26655471039403261073486701)
      ·
        refine ⟨9995801639776222902557513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26655471039403261073486701 9995801639776222902557513)
        ·
          refine ⟨7496851229832167176918135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9995801639776222902557513 7496851229832167176918135)
          ·
            refine ⟨11245276844748250765377203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7496851229832167176918135 11245276844748250765377203)
            ·
              refine ⟨16867915267122376148065805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11245276844748250765377203 16867915267122376148065805)
              ·
                refine ⟨6325468225170891055524677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16867915267122376148065805 6325468225170891055524677)
                ·
                  refine ⟨1186025292219542072910877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6325468225170891055524677 1186025292219542072910877)
                  ·
                    refine ⟨444759484582328277341579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1186025292219542072910877 444759484582328277341579)
                    ·
                      rfl

theorem cell22_1299249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_1299249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299249 prefixEnd_1299249 := by exact prefixLift 1299249
  have htrace : WordTrace (prefixWord ++ tailWord_1299249) baseStart_1299249 baseEnd_1299249 := by
    simpa [prefixWord, tailWord_1299249, baseEnd_1299249] using wordTrace_append hprefix tailTrace_1299249
  have hstable : (prefixWord ++ tailWord_1299249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299249).length < 2 ^ (prefixWord ++ tailWord_1299249).sum := by decide
  have hdescent : baseEnd_1299249 < baseStart_1299249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299281 : List Nat := [1, 2, 2, 1, 6, 1, 2, 1, 2, 4]
def baseStart_1299281 : Nat := 118140960795 + 1299281 * 2 ^ 59
def prefixEnd_1299281 : Nat := 4983230072969 + 3 ^ 40 * 1299281 * 2
def baseEnd_1299281 : Nat := 444770438836290860541481

theorem tailTrace_1299281 : CollatzResearch.WordTrace tailWord_1299281 prefixEnd_1299281 444770438836290860541481 := by
  unfold tailWord_1299281
  simp only [CollatzResearch.WordTrace]
  refine ⟨47388671205934311373585697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31592447470622874249057131 47388671205934311373585697)
  ·
    refine ⟨35541503404450733530189273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47388671205934311373585697 35541503404450733530189273)
    ·
      refine ⟨26656127553338050147641955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35541503404450733530189273 26656127553338050147641955)
      ·
        refine ⟨39984191330007075221462933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26656127553338050147641955 39984191330007075221462933)
        ·
          refine ⟨1874258968594081651006075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 39984191330007075221462933 1874258968594081651006075)
          ·
            refine ⟨2811388452891122476509113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874258968594081651006075 2811388452891122476509113)
            ·
              refine ⟨2108541339668341857381835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2811388452891122476509113 2108541339668341857381835)
              ·
                refine ⟨3162812009502512786072753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108541339668341857381835 3162812009502512786072753)
                ·
                  refine ⟨2372109007126884589554565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3162812009502512786072753 2372109007126884589554565)
                  ·
                    refine ⟨444770438836290860541481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2372109007126884589554565 444770438836290860541481)
                    ·
                      rfl

theorem cell22_1299281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 4].length) (baseStart_1299281 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299281 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299281 prefixEnd_1299281 := by exact prefixLift 1299281
  have htrace : WordTrace (prefixWord ++ tailWord_1299281) baseStart_1299281 baseEnd_1299281 := by
    simpa [prefixWord, tailWord_1299281, baseEnd_1299281] using wordTrace_append hprefix tailTrace_1299281
  have hstable : (prefixWord ++ tailWord_1299281).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299281).length < 2 ^ (prefixWord ++ tailWord_1299281).sum := by decide
  have hdescent : baseEnd_1299281 < baseStart_1299281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299307 : List Nat := [1, 1, 1, 1, 2, 2, 4, 3, 7]
def baseStart_1299307 : Nat := 118140960795 + 1299307 * 2 ^ 59
def prefixEnd_1299307 : Nat := 4983230072969 + 3 ^ 40 * 1299307 * 2
def baseEnd_1299307 : Nat := 148259779722545153130467

theorem tailTrace_1299307 : CollatzResearch.WordTrace tailWord_1299307 prefixEnd_1299307 148259779722545153130467 := by
  unfold tailWord_1299307
  simp only [CollatzResearch.WordTrace]
  refine ⟨47389619503840117814032175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31593079669226745209354783 47389619503840117814032175)
  ·
    refine ⟨71084429255760176721048263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47389619503840117814032175 71084429255760176721048263)
    ·
      refine ⟨106626643883640265081572395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71084429255760176721048263 106626643883640265081572395)
      ·
        refine ⟨159939965825460397622358593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106626643883640265081572395 159939965825460397622358593)
        ·
          refine ⟨119954974369095298216768945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159939965825460397622358593 119954974369095298216768945)
          ·
            refine ⟨89966230776821473662576709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119954974369095298216768945 89966230776821473662576709)
            ·
              refine ⟨16868668270654026311733133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 89966230776821473662576709 16868668270654026311733133)
              ·
                refine ⟨6325750601495259866899925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16868668270654026311733133 6325750601495259866899925)
                ·
                  refine ⟨148259779722545153130467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6325750601495259866899925 148259779722545153130467)
                  ·
                    rfl

theorem cell22_1299307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 3, 7].length) (baseStart_1299307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299307 prefixEnd_1299307 := by exact prefixLift 1299307
  have htrace : WordTrace (prefixWord ++ tailWord_1299307) baseStart_1299307 baseEnd_1299307 := by
    simpa [prefixWord, tailWord_1299307, baseEnd_1299307] using wordTrace_append hprefix tailTrace_1299307
  have hstable : (prefixWord ++ tailWord_1299307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299307).length < 2 ^ (prefixWord ++ tailWord_1299307).sum := by decide
  have hdescent : baseEnd_1299307 < baseStart_1299307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299330 : List Nat := [3, 4, 2, 2, 1, 1, 3, 6]
def baseStart_1299330 : Nat := 118140960795 + 1299330 * 2 ^ 59
def prefixEnd_1299330 : Nat := 4983230072969 + 3 ^ 40 * 1299330 * 2
def baseEnd_1299330 : Nat := 49420801393074562896259

theorem tailTrace_1299330 : CollatzResearch.WordTrace tailWord_1299330 prefixEnd_1299330 49420801393074562896259 := by
  unfold tailWord_1299330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11847614595689198185529861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31593638921837861828079629 11847614595689198185529861)
  ·
    refine ⟨2221427736691724659786849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11847614595689198185529861 2221427736691724659786849)
    ·
      refine ⟨1666070802518793494840137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2221427736691724659786849 1666070802518793494840137)
      ·
        refine ⟨1249553101889095121130103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1666070802518793494840137 1249553101889095121130103)
        ·
          refine ⟨1874329652833642681695155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249553101889095121130103 1874329652833642681695155)
          ·
            refine ⟨2811494479250464022542733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874329652833642681695155 2811494479250464022542733)
            ·
              refine ⟨1054310429718924008453525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2811494479250464022542733 1054310429718924008453525)
              ·
                refine ⟨49420801393074562896259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1054310429718924008453525 49420801393074562896259)
                ·
                  rfl

theorem cell22_1299330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 1, 3, 6].length) (baseStart_1299330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299330 prefixEnd_1299330 := by exact prefixLift 1299330
  have htrace : WordTrace (prefixWord ++ tailWord_1299330) baseStart_1299330 baseEnd_1299330 := by
    simpa [prefixWord, tailWord_1299330, baseEnd_1299330] using wordTrace_append hprefix tailTrace_1299330
  have hstable : (prefixWord ++ tailWord_1299330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299330).length < 2 ^ (prefixWord ++ tailWord_1299330).sum := by decide
  have hdescent : baseEnd_1299330 < baseStart_1299330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299369 : List Nat := [1, 2, 1, 1, 1, 1, 8, 1, 6]
def baseStart_1299369 : Nat := 118140960795 + 1299369 * 2 ^ 59
def prefixEnd_1299369 : Nat := 4983230072969 + 3 ^ 40 * 1299369 * 2
def baseEnd_1299369 : Nat := 148266854344895988113737

theorem tailTrace_1299369 : CollatzResearch.WordTrace tailWord_1299369 prefixEnd_1299369 148266854344895988113737 := by
  unfold tailWord_1299369
  simp only [CollatzResearch.WordTrace]
  refine ⟨47391880829615502402789161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31594587219743668268526107 47391880829615502402789161)
  ·
    refine ⟨35543910622211626802091871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47391880829615502402789161 35543910622211626802091871)
    ·
      refine ⟨53315865933317440203137807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35543910622211626802091871 53315865933317440203137807)
      ·
        refine ⟨79973798899976160304706711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53315865933317440203137807 79973798899976160304706711)
        ·
          refine ⟨119960698349964240457060067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79973798899976160304706711 119960698349964240457060067)
          ·
            refine ⟨179941047524946360685590101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119960698349964240457060067 179941047524946360685590101)
            ·
              refine ⟨2108684150682965164284259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 179941047524946360685590101 2108684150682965164284259)
              ·
                refine ⟨3163026226024447746426389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108684150682965164284259 3163026226024447746426389)
                ·
                  refine ⟨148266854344895988113737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3163026226024447746426389 148266854344895988113737)
                  ·
                    rfl

theorem cell22_1299369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 6].length) (baseStart_1299369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299369 prefixEnd_1299369 := by exact prefixLift 1299369
  have htrace : WordTrace (prefixWord ++ tailWord_1299369) baseStart_1299369 baseEnd_1299369 := by
    simpa [prefixWord, tailWord_1299369, baseEnd_1299369] using wordTrace_append hprefix tailTrace_1299369
  have hstable : (prefixWord ++ tailWord_1299369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299369).length < 2 ^ (prefixWord ++ tailWord_1299369).sum := by decide
  have hdescent : baseEnd_1299369 < baseStart_1299369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299399 : List Nat := [1, 1, 4, 1, 1, 2, 4, 1, 1, 6]
def baseStart_1299399 : Nat := 118140960795 + 1299399 * 2 ^ 59
def prefixEnd_1299399 : Nat := 4983230072969 + 3 ^ 40 * 1299399 * 2
def baseEnd_1299399 : Nat := 444810832647777886091119

theorem tailTrace_1299399 : CollatzResearch.WordTrace tailWord_1299399 prefixEnd_1299399 444810832647777886091119 := by
  unfold tailWord_1299399
  simp only [CollatzResearch.WordTrace]
  refine ⟨47392975019506817526381251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31595316679671211684254167 47392975019506817526381251)
  ·
    refine ⟨71089462529260226289571877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47392975019506817526381251 71089462529260226289571877)
    ·
      refine ⟨13329274224236292429294727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71089462529260226289571877 13329274224236292429294727)
      ·
        refine ⟨19993911336354438643942091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13329274224236292429294727 19993911336354438643942091)
        ·
          refine ⟨29990867004531657965913137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19993911336354438643942091 29990867004531657965913137)
          ·
            refine ⟨22493150253398743474434853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29990867004531657965913137 22493150253398743474434853)
            ·
              refine ⟨4217465672512264401456535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22493150253398743474434853 4217465672512264401456535)
              ·
                refine ⟨6326198508768396602184803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4217465672512264401456535 6326198508768396602184803)
                ·
                  refine ⟨9489297763152594903277205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6326198508768396602184803 9489297763152594903277205)
                  ·
                    refine ⟨444810832647777886091119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9489297763152594903277205 444810832647777886091119)
                    ·
                      rfl

theorem cell22_1299399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_1299399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299399 prefixEnd_1299399 := by exact prefixLift 1299399
  have htrace : WordTrace (prefixWord ++ tailWord_1299399) baseStart_1299399 baseEnd_1299399 := by
    simpa [prefixWord, tailWord_1299399, baseEnd_1299399] using wordTrace_append hprefix tailTrace_1299399
  have hstable : (prefixWord ++ tailWord_1299399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299399).length < 2 ^ (prefixWord ++ tailWord_1299399).sum := by decide
  have hdescent : baseEnd_1299399 < baseStart_1299399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299403 : List Nat := [1, 1, 1, 1, 3, 7, 1, 3, 4]
def baseStart_1299403 : Nat := 118140960795 + 1299403 * 2 ^ 59
def prefixEnd_1299403 : Nat := 4983230072969 + 3 ^ 40 * 1299403 * 2
def baseEnd_1299403 : Nat := 148270733976507736330369

theorem tailTrace_1299403 : CollatzResearch.WordTrace tailWord_1299403 prefixEnd_1299403 148270733976507736330369 := by
  unfold tailWord_1299403
  simp only [CollatzResearch.WordTrace]
  refine ⟨47393120911492326209526863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31595413940994884139684575 47393120911492326209526863)
  ·
    refine ⟨71089681367238489314290295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47393120911492326209526863 71089681367238489314290295)
    ·
      refine ⟨106634522050857733971435443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71089681367238489314290295 106634522050857733971435443)
      ·
        refine ⟨159951783076286600957153165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106634522050857733971435443 159951783076286600957153165)
        ·
          refine ⟨59981918653607475358932437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 159951783076286600957153165 59981918653607475358932437)
          ·
            refine ⟨1405826218443925203724979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 59981918653607475358932437 1405826218443925203724979)
            ·
              refine ⟨2108739327665887805587469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1405826218443925203724979 2108739327665887805587469)
              ·
                refine ⟨790777247874707927095301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2108739327665887805587469 790777247874707927095301)
                ·
                  refine ⟨148270733976507736330369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 790777247874707927095301 148270733976507736330369)
                  ·
                    rfl

theorem cell22_1299403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 7, 1, 3, 4].length) (baseStart_1299403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299403 prefixEnd_1299403 := by exact prefixLift 1299403
  have htrace : WordTrace (prefixWord ++ tailWord_1299403) baseStart_1299403 baseEnd_1299403 := by
    simpa [prefixWord, tailWord_1299403, baseEnd_1299403] using wordTrace_append hprefix tailTrace_1299403
  have hstable : (prefixWord ++ tailWord_1299403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299403).length < 2 ^ (prefixWord ++ tailWord_1299403).sum := by decide
  have hdescent : baseEnd_1299403 < baseStart_1299403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299416 : List Nat := [2, 1, 2, 2, 2, 4, 1, 2, 2, 4]
def baseStart_1299416 : Nat := 118140960795 + 1299416 * 2 ^ 59
def prefixEnd_1299416 : Nat := 4983230072969 + 3 ^ 40 * 1299416 * 2
def baseEnd_1299416 : Nat := 444816652095195508416067

theorem tailTrace_1299416 : CollatzResearch.WordTrace tailWord_1299416 prefixEnd_1299416 444816652095195508416067 := by
  unfold tailWord_1299416
  simp only [CollatzResearch.WordTrace]
  refine ⟨23696797530222614714875051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31595730040296819619833401 23696797530222614714875051)
  ·
    refine ⟨35545196295333922072312577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23696797530222614714875051 35545196295333922072312577)
    ·
      refine ⟨26658897221500441554234433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35545196295333922072312577 26658897221500441554234433)
      ·
        refine ⟨19994172916125331165675825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26658897221500441554234433 19994172916125331165675825)
        ·
          refine ⟨14995629687093998374256869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19994172916125331165675825 14995629687093998374256869)
          ·
            refine ⟨2811680566330124695173163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14995629687093998374256869 2811680566330124695173163)
            ·
              refine ⟨4217520849495187042759745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811680566330124695173163 4217520849495187042759745)
              ·
                refine ⟨3163140637121390282069809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4217520849495187042759745 3163140637121390282069809)
                ·
                  refine ⟨2372355477841042711552357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3163140637121390282069809 2372355477841042711552357)
                  ·
                    refine ⟨444816652095195508416067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2372355477841042711552357 444816652095195508416067)
                    ·
                      rfl

theorem cell22_1299416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 1, 2, 2, 4].length) (baseStart_1299416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299416 prefixEnd_1299416 := by exact prefixLift 1299416
  have htrace : WordTrace (prefixWord ++ tailWord_1299416) baseStart_1299416 baseEnd_1299416 := by
    simpa [prefixWord, tailWord_1299416, baseEnd_1299416] using wordTrace_append hprefix tailTrace_1299416
  have hstable : (prefixWord ++ tailWord_1299416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299416).length < 2 ^ (prefixWord ++ tailWord_1299416).sum := by decide
  have hdescent : baseEnd_1299416 < baseStart_1299416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299431 : List Nat := [1, 1, 5, 2, 2, 2, 2, 7]
def baseStart_1299431 : Nat := 118140960795 + 1299431 * 2 ^ 59
def prefixEnd_1299431 : Nat := 4983230072969 + 3 ^ 40 * 1299431 * 2
def baseEnd_1299431 : Nat := 49424642989082274365669

theorem tailTrace_1299431 : CollatzResearch.WordTrace tailWord_1299431 prefixEnd_1299431 49424642989082274365669 := by
  unfold tailWord_1299431
  simp only [CollatzResearch.WordTrace]
  refine ⟨47394142155390886991546147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31596094770260591327697431 47394142155390886991546147)
  ·
    refine ⟨71091213233086330487319221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47394142155390886991546147 71091213233086330487319221)
    ·
      refine ⟨6664801240601843483186177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 71091213233086330487319221 6664801240601843483186177)
      ·
        refine ⟨4998600930451382612389633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6664801240601843483186177 4998600930451382612389633)
        ·
          refine ⟨3748950697838536959292225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4998600930451382612389633 3748950697838536959292225)
          ·
            refine ⟨2811713023378902719469169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3748950697838536959292225 2811713023378902719469169)
            ·
              refine ⟨2108784767534177039601877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2811713023378902719469169 2108784767534177039601877)
              ·
                refine ⟨49424642989082274365669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2108784767534177039601877 49424642989082274365669)
                ·
                  rfl

theorem cell22_1299431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 7].length) (baseStart_1299431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299431 prefixEnd_1299431 := by exact prefixLift 1299431
  have htrace : WordTrace (prefixWord ++ tailWord_1299431) baseStart_1299431 baseEnd_1299431 := by
    simpa [prefixWord, tailWord_1299431, baseEnd_1299431] using wordTrace_append hprefix tailTrace_1299431
  have hstable : (prefixWord ++ tailWord_1299431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299431).length < 2 ^ (prefixWord ++ tailWord_1299431).sum := by decide
  have hdescent : baseEnd_1299431 < baseStart_1299431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299480 : List Nat := [2, 1, 2, 3, 2, 3, 1, 4, 1, 3]
def baseStart_1299480 : Nat := 118140960795 + 1299480 * 2 ^ 59
def prefixEnd_1299480 : Nat := 4983230072969 + 3 ^ 40 * 1299480 * 2
def baseEnd_1299480 : Nat := 444838560603120674815871

theorem tailTrace_1299480 : CollatzResearch.WordTrace tailWord_1299480 prefixEnd_1299480 444838560603120674815871 := by
  unfold tailWord_1299480
  simp only [CollatzResearch.WordTrace]
  refine ⟨23697964666106684180039947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31597286221475578906719929 23697964666106684180039947)
  ·
    refine ⟨35546946999160026270059921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23697964666106684180039947 35546946999160026270059921)
    ·
      refine ⟨26660210249370019702544941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35546946999160026270059921 26660210249370019702544941)
      ·
        refine ⟨9997578843513757388454353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26660210249370019702544941 9997578843513757388454353)
        ·
          refine ⟨7498184132635318041340765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9997578843513757388454353 7498184132635318041340765)
          ·
            refine ⟨2811819049738244265502787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7498184132635318041340765 2811819049738244265502787)
            ·
              refine ⟨4217728574607366398254181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811819049738244265502787 4217728574607366398254181)
              ·
                refine ⟨790824107738881199672659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4217728574607366398254181 790824107738881199672659)
                ·
                  refine ⟨1186236161608321799508989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790824107738881199672659 1186236161608321799508989)
                  ·
                    refine ⟨444838560603120674815871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1186236161608321799508989 444838560603120674815871)
                    ·
                      rfl

theorem cell22_1299480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 1, 4, 1, 3].length) (baseStart_1299480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299480 prefixEnd_1299480 := by exact prefixLift 1299480
  have htrace : WordTrace (prefixWord ++ tailWord_1299480) baseStart_1299480 baseEnd_1299480 := by
    simpa [prefixWord, tailWord_1299480, baseEnd_1299480] using wordTrace_append hprefix tailTrace_1299480
  have hstable : (prefixWord ++ tailWord_1299480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299480).length < 2 ^ (prefixWord ++ tailWord_1299480).sum := by decide
  have hdescent : baseEnd_1299480 < baseStart_1299480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299491 : List Nat := [1, 1, 1, 4, 3, 3, 1, 1, 2, 5]
def baseStart_1299491 : Nat := 118140960795 + 1299491 * 2 ^ 59
def prefixEnd_1299491 : Nat := 4983230072969 + 3 ^ 40 * 1299491 * 2
def baseEnd_1299491 : Nat := 444842326127920312790837

theorem tailTrace_1299491 : CollatzResearch.WordTrace tailWord_1299491 prefixEnd_1299491 444842326127920312790837 := by
  unfold tailWord_1299491
  simp only [CollatzResearch.WordTrace]
  refine ⟨47396330535173517238730327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31597553690115678159153551 47396330535173517238730327)
  ·
    refine ⟨71094495802760275858095491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47396330535173517238730327 71094495802760275858095491)
    ·
      refine ⟨106641743704140413787143237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71094495802760275858095491 106641743704140413787143237)
      ·
        refine ⟨19995326944526327585089357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106641743704140413787143237 19995326944526327585089357)
        ·
          refine ⟨7498247604197372844408509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19995326944526327585089357 7498247604197372844408509)
          ·
            refine ⟨2811842851574014816653191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7498247604197372844408509 2811842851574014816653191)
            ·
              refine ⟨4217764277361022224979787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2811842851574014816653191 4217764277361022224979787)
              ·
                refine ⟨6326646416041533337469681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4217764277361022224979787 6326646416041533337469681)
                ·
                  refine ⟨4744984812031150003102261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6326646416041533337469681 4744984812031150003102261)
                  ·
                    refine ⟨444842326127920312790837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4744984812031150003102261 444842326127920312790837)
                    ·
                      rfl

theorem cell22_1299491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 1, 2, 5].length) (baseStart_1299491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299491 prefixEnd_1299491 := by exact prefixLift 1299491
  have htrace : WordTrace (prefixWord ++ tailWord_1299491) baseStart_1299491 baseEnd_1299491 := by
    simpa [prefixWord, tailWord_1299491, baseEnd_1299491] using wordTrace_append hprefix tailTrace_1299491
  have hstable : (prefixWord ++ tailWord_1299491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299491).length < 2 ^ (prefixWord ++ tailWord_1299491).sum := by decide
  have hdescent : baseEnd_1299491 < baseStart_1299491 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299506 : List Nat := [3, 2, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_1299506 : Nat := 118140960795 + 1299506 * 2 ^ 59
def prefixEnd_1299506 : Nat := 4983230072969 + 3 ^ 40 * 1299506 * 2
def baseEnd_1299506 : Nat := 444847460934465273665791

theorem tailTrace_1299506 : CollatzResearch.WordTrace tailWord_1299506 prefixEnd_1299506 444847460934465273665791 := by
  unfold tailWord_1299506
  simp only [CollatzResearch.WordTrace]
  refine ⟨11849219407529793700131593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31597918420079449867017581 11849219407529793700131593)
  ·
    refine ⟨8886914555647345275098695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11849219407529793700131593 8886914555647345275098695)
    ·
      refine ⟨13330371833471017912648043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8886914555647345275098695 13330371833471017912648043)
      ·
        refine ⟨19995557750206526868972065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13330371833471017912648043 19995557750206526868972065)
        ·
          refine ⟨14996668312654895151729049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19995557750206526868972065 14996668312654895151729049)
          ·
            refine ⟨11247501234491171363796787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14996668312654895151729049 11247501234491171363796787)
            ·
              refine ⟨16871251851736757045695181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11247501234491171363796787 16871251851736757045695181)
              ·
                refine ⟨6326719444401283892135693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16871251851736757045695181 6326719444401283892135693)
                ·
                  refine ⟨2372519791650481459550885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6326719444401283892135693 2372519791650481459550885)
                  ·
                    refine ⟨444847460934465273665791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2372519791650481459550885 444847460934465273665791)
                    ·
                      rfl

theorem cell22_1299506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_1299506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299506 prefixEnd_1299506 := by exact prefixLift 1299506
  have htrace : WordTrace (prefixWord ++ tailWord_1299506) baseStart_1299506 baseEnd_1299506 := by
    simpa [prefixWord, tailWord_1299506, baseEnd_1299506] using wordTrace_append hprefix tailTrace_1299506
  have hstable : (prefixWord ++ tailWord_1299506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299506).length < 2 ^ (prefixWord ++ tailWord_1299506).sum := by decide
  have hdescent : baseEnd_1299506 < baseStart_1299506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299538 : List Nat := [3, 2, 2, 1, 3, 2, 2, 1, 6]
def baseStart_1299538 : Nat := 118140960795 + 1299538 * 2 ^ 59
def prefixEnd_1299538 : Nat := 4983230072969 + 3 ^ 40 * 1299538 * 2
def baseEnd_1299538 : Nat := 148286138396142618955231

theorem tailTrace_1299538 : CollatzResearch.WordTrace tailWord_1299538 prefixEnd_1299538 148286138396142618955231 := by
  unfold tailWord_1299538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11849511191500811066422817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31598696510668829510460845 11849511191500811066422817)
  ·
    refine ⟨8887133393625608299817113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11849511191500811066422817 8887133393625608299817113)
    ·
      refine ⟨6665350045219206224862835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8887133393625608299817113 6665350045219206224862835)
      ·
        refine ⟨9998025067828809337294253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6665350045219206224862835 9998025067828809337294253)
        ·
          refine ⟨3749259400435803501485345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9998025067828809337294253 3749259400435803501485345)
          ·
            refine ⟨2811944550326852626114009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3749259400435803501485345 2811944550326852626114009)
            ·
              refine ⟨2108958412745139469585507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2811944550326852626114009 2108958412745139469585507)
              ·
                refine ⟨3163437619117709204378261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2108958412745139469585507 3163437619117709204378261)
                ·
                  refine ⟨148286138396142618955231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3163437619117709204378261 148286138396142618955231)
                  ·
                    rfl

theorem cell22_1299538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_1299538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299538 prefixEnd_1299538 := by exact prefixLift 1299538
  have htrace : WordTrace (prefixWord ++ tailWord_1299538) baseStart_1299538 baseEnd_1299538 := by
    simpa [prefixWord, tailWord_1299538, baseEnd_1299538] using wordTrace_append hprefix tailTrace_1299538
  have hstable : (prefixWord ++ tailWord_1299538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299538).length < 2 ^ (prefixWord ++ tailWord_1299538).sum := by decide
  have hdescent : baseEnd_1299538 < baseStart_1299538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299553 : List Nat := [1, 2, 3, 1, 1, 2, 2, 5, 2, 3]
def baseStart_1299553 : Nat := 118140960795 + 1299553 * 2 ^ 59
def prefixEnd_1299553 : Nat := 4983230072969 + 3 ^ 40 * 1299553 * 2
def baseEnd_1299553 : Nat := 444863549994972817740647

theorem tailTrace_1299553 : CollatzResearch.WordTrace tailWord_1299553 prefixEnd_1299553 444863549994972817740647 := by
  unfold tailWord_1299553
  simp only [CollatzResearch.WordTrace]
  refine ⟨47398591860948901827487313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31599061240632601218324875 47398591860948901827487313)
  ·
    refine ⟨35548943895711676370615485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47398591860948901827487313 35548943895711676370615485)
    ·
      refine ⟨13330853960891878638980807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35548943895711676370615485 13330853960891878638980807)
      ·
        refine ⟨19996280941337817958471211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13330853960891878638980807 19996280941337817958471211)
        ·
          refine ⟨29994421412006726937706817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19996280941337817958471211 29994421412006726937706817)
          ·
            refine ⟨22495816059005045203280113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29994421412006726937706817 22495816059005045203280113)
            ·
              refine ⟨16871862044253783902460085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22495816059005045203280113 16871862044253783902460085)
              ·
                refine ⟨1581737066648792240855633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16871862044253783902460085 1581737066648792240855633)
                ·
                  refine ⟨1186302799986594180641725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1581737066648792240855633 1186302799986594180641725)
                  ·
                    refine ⟨444863549994972817740647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1186302799986594180641725 444863549994972817740647)
                    ·
                      rfl

theorem cell22_1299553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5, 2, 3].length) (baseStart_1299553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299553 prefixEnd_1299553 := by exact prefixLift 1299553
  have htrace : WordTrace (prefixWord ++ tailWord_1299553) baseStart_1299553 baseEnd_1299553 := by
    simpa [prefixWord, tailWord_1299553, baseEnd_1299553] using wordTrace_append hprefix tailTrace_1299553
  have hstable : (prefixWord ++ tailWord_1299553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299553).length < 2 ^ (prefixWord ++ tailWord_1299553).sum := by decide
  have hdescent : baseEnd_1299553 < baseStart_1299553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299649 : List Nat := [1, 2, 6, 1, 1, 2, 1, 4, 1, 3]
def baseStart_1299649 : Nat := 118140960795 + 1299649 * 2 ^ 59
def prefixEnd_1299649 : Nat := 4983230072969 + 3 ^ 40 * 1299649 * 2
def baseEnd_1299649 : Nat := 444896412756860567340353

theorem tailTrace_1299649 : CollatzResearch.WordTrace tailWord_1299649 prefixEnd_1299649 444896412756860567340353 := by
  unfold tailWord_1299649
  simp only [CollatzResearch.WordTrace]
  refine ⟨47402093268601110222982001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31601395512400740148654667 47402093268601110222982001)
  ·
    refine ⟨35551569951450832667236501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47402093268601110222982001 35551569951450832667236501)
    ·
      refine ⟨1666479841474257781276711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35551569951450832667236501 1666479841474257781276711)
      ·
        refine ⟨2499719762211386671915067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1666479841474257781276711 2499719762211386671915067)
        ·
          refine ⟨3749579643317080007872601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2499719762211386671915067 3749579643317080007872601)
          ·
            refine ⟨2812184732487810005904451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3749579643317080007872601 2812184732487810005904451)
            ·
              refine ⟨4218277098731715008856677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2812184732487810005904451 4218277098731715008856677)
              ·
                refine ⟨790926956012196564160627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4218277098731715008856677 790926956012196564160627)
                ·
                  refine ⟨1186390434018294846240941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 790926956012196564160627 1186390434018294846240941)
                  ·
                    refine ⟨444896412756860567340353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1186390434018294846240941 444896412756860567340353)
                    ·
                      rfl

theorem cell22_1299649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_1299649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299649 prefixEnd_1299649 := by exact prefixLift 1299649
  have htrace : WordTrace (prefixWord ++ tailWord_1299649) baseStart_1299649 baseEnd_1299649 := by
    simpa [prefixWord, tailWord_1299649, baseEnd_1299649] using wordTrace_append hprefix tailTrace_1299649
  have hstable : (prefixWord ++ tailWord_1299649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299649).length < 2 ^ (prefixWord ++ tailWord_1299649).sum := by decide
  have hdescent : baseEnd_1299649 < baseStart_1299649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299658 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_1299658 : Nat := 118140960795 + 1299658 * 2 ^ 59
def prefixEnd_1299658 : Nat := 4983230072969 + 3 ^ 40 * 1299658 * 2
def baseEnd_1299658 : Nat := 444899493640787543865325

theorem tailTrace_1299658 : CollatzResearch.WordTrace tailWord_1299658 prefixEnd_1299658 444899493640787543865325 := by
  unfold tailWord_1299658
  simp only [CollatzResearch.WordTrace]
  refine ⟨11850605381392126190014907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31601614350379003173373085 11850605381392126190014907)
  ·
    refine ⟨17775908072088189285022361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11850605381392126190014907 17775908072088189285022361)
    ·
      refine ⟨13331931054066141963766771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17775908072088189285022361 13331931054066141963766771)
      ·
        refine ⟨19997896581099212945650157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13331931054066141963766771 19997896581099212945650157)
        ·
          refine ⟨7499211217912204854618809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19997896581099212945650157 7499211217912204854618809)
          ·
            refine ⟨5624408413434153640964107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7499211217912204854618809 5624408413434153640964107)
            ·
              refine ⟨8436612620151230461446161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624408413434153640964107 8436612620151230461446161)
              ·
                refine ⟨6327459465113422846084621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8436612620151230461446161 6327459465113422846084621)
                ·
                  refine ⟨2372797299417533567281733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6327459465113422846084621 2372797299417533567281733)
                  ·
                    refine ⟨444899493640787543865325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2372797299417533567281733 444899493640787543865325)
                    ·
                      rfl

theorem cell22_1299658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_1299658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299658 prefixEnd_1299658 := by exact prefixLift 1299658
  have htrace : WordTrace (prefixWord ++ tailWord_1299658) baseStart_1299658 baseEnd_1299658 := by
    simpa [prefixWord, tailWord_1299658, baseEnd_1299658] using wordTrace_append hprefix tailTrace_1299658
  have hstable : (prefixWord ++ tailWord_1299658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299658).length < 2 ^ (prefixWord ++ tailWord_1299658).sum := by decide
  have hdescent : baseEnd_1299658 < baseStart_1299658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299688 : List Nat := [2, 1, 4, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1299688 : Nat := 118140960795 + 1299688 * 2 ^ 59
def prefixEnd_1299688 : Nat := 4983230072969 + 3 ^ 40 * 1299688 * 2
def baseEnd_1299688 : Nat := 444909763253877465615233

theorem tailTrace_1299688 : CollatzResearch.WordTrace tailWord_1299688 prefixEnd_1299688 444909763253877465615233 := by
  unfold tailWord_1299688
  simp only [CollatzResearch.WordTrace]
  refine ⟨23701757857729909941825859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31602343810306546589101145 23701757857729909941825859)
  ·
    refine ⟨35552636786594864912738789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23701757857729909941825859 35552636786594864912738789)
    ·
      refine ⟨6666119397486537171138523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35552636786594864912738789 6666119397486537171138523)
      ·
        refine ⟨9999179096229805756707785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6666119397486537171138523 9999179096229805756707785)
        ·
          refine ⟨7499384322172354317530839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9999179096229805756707785 7499384322172354317530839)
          ·
            refine ⟨11249076483258531476296259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7499384322172354317530839 11249076483258531476296259)
            ·
              refine ⟨16873614724887797214444389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11249076483258531476296259 16873614724887797214444389)
              ·
                refine ⟨3163802760916461977708323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16873614724887797214444389 3163802760916461977708323)
                ·
                  refine ⟨4745704141374692966562485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3163802760916461977708323 4745704141374692966562485)
                  ·
                    refine ⟨444909763253877465615233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4745704141374692966562485 444909763253877465615233)
                    ·
                      rfl

theorem cell22_1299688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1299688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299688 prefixEnd_1299688 := by exact prefixLift 1299688
  have htrace : WordTrace (prefixWord ++ tailWord_1299688) baseStart_1299688 baseEnd_1299688 := by
    simpa [prefixWord, tailWord_1299688, baseEnd_1299688] using wordTrace_append hprefix tailTrace_1299688
  have hstable : (prefixWord ++ tailWord_1299688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299688).length < 2 ^ (prefixWord ++ tailWord_1299688).sum := by decide
  have hdescent : baseEnd_1299688 < baseStart_1299688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299690 : List Nat := [3, 1, 3, 1, 1, 3, 1, 5, 4]
def baseStart_1299690 : Nat := 118140960795 + 1299690 * 2 ^ 59
def prefixEnd_1299690 : Nat := 4983230072969 + 3 ^ 40 * 1299690 * 2
def baseEnd_1299690 : Nat := 148303482631583375688409

theorem tailTrace_1299690 : CollatzResearch.WordTrace tailWord_1299690 prefixEnd_1299690 148303482631583375688409 := by
  unfold tailWord_1299690
  simp only [CollatzResearch.WordTrace]
  refine ⟨11850897165363143556306131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31602392440968382816816349 11850897165363143556306131)
  ·
    refine ⟨17776345748044715334459197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11850897165363143556306131 17776345748044715334459197)
    ·
      refine ⟨6666129655516768250422199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17776345748044715334459197 6666129655516768250422199)
      ·
        refine ⟨9999194483275152375633299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6666129655516768250422199 9999194483275152375633299)
        ·
          refine ⟨14998791724912728563449949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9999194483275152375633299 14998791724912728563449949)
          ·
            refine ⟨5624546896842273211293731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14998791724912728563449949 5624546896842273211293731)
            ·
              refine ⟨8436820345263409816940597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5624546896842273211293731 8436820345263409816940597)
              ·
                refine ⟨790951907368444670338181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8436820345263409816940597 790951907368444670338181)
                ·
                  refine ⟨148303482631583375688409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 790951907368444670338181 148303482631583375688409)
                  ·
                    rfl

theorem cell22_1299690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 3, 1, 5, 4].length) (baseStart_1299690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299690 prefixEnd_1299690 := by exact prefixLift 1299690
  have htrace : WordTrace (prefixWord ++ tailWord_1299690) baseStart_1299690 baseEnd_1299690 := by
    simpa [prefixWord, tailWord_1299690, baseEnd_1299690] using wordTrace_append hprefix tailTrace_1299690
  have hstable : (prefixWord ++ tailWord_1299690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299690).length < 2 ^ (prefixWord ++ tailWord_1299690).sum := by decide
  have hdescent : baseEnd_1299690 < baseStart_1299690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299692 : List Nat := [2, 2, 1, 1, 2, 6, 2, 1, 1, 4]
def baseStart_1299692 : Nat := 118140960795 + 1299692 * 2 ^ 59
def prefixEnd_1299692 : Nat := 4983230072969 + 3 ^ 40 * 1299692 * 2
def baseEnd_1299692 : Nat := 444911132535622788515221

theorem tailTrace_1299692 : CollatzResearch.WordTrace tailWord_1299692 prefixEnd_1299692 444911132535622788515221 := by
  unfold tailWord_1299692
  simp only [CollatzResearch.WordTrace]
  refine ⟨23701830803722664283398665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31602441071630219044531553 23701830803722664283398665)
  ·
    refine ⟨17776373102791998212548999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23701830803722664283398665 17776373102791998212548999)
    ·
      refine ⟨26664559654187997318823499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17776373102791998212548999 26664559654187997318823499)
      ·
        refine ⟨39996839481281995978235249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26664559654187997318823499 39996839481281995978235249)
        ·
          refine ⟨29997629610961496983676437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39996839481281995978235249 29997629610961496983676437)
          ·
            refine ⟨1406138888013820171109833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 29997629610961496983676437 1406138888013820171109833)
            ·
              refine ⟨1054604166010365128332375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1406138888013820171109833 1054604166010365128332375)
              ·
                refine ⟨1581906249015547692498563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054604166010365128332375 1581906249015547692498563)
                ·
                  refine ⟨2372859373523321538747845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1581906249015547692498563 2372859373523321538747845)
                  ·
                    refine ⟨444911132535622788515221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2372859373523321538747845 444911132535622788515221)
                    ·
                      rfl

theorem cell22_1299692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 4].length) (baseStart_1299692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299692 prefixEnd_1299692 := by exact prefixLift 1299692
  have htrace : WordTrace (prefixWord ++ tailWord_1299692) baseStart_1299692 baseEnd_1299692 := by
    simpa [prefixWord, tailWord_1299692, baseEnd_1299692] using wordTrace_append hprefix tailTrace_1299692
  have hstable : (prefixWord ++ tailWord_1299692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299692).length < 2 ^ (prefixWord ++ tailWord_1299692).sum := by decide
  have hdescent : baseEnd_1299692 < baseStart_1299692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299763 : List Nat := [1, 1, 1, 2, 5, 2, 2, 1, 7]
def baseStart_1299763 : Nat := 118140960795 + 1299763 * 2 ^ 59
def prefixEnd_1299763 : Nat := 4983230072969 + 3 ^ 40 * 1299763 * 2
def baseEnd_1299763 : Nat := 148311812428867423330001

theorem tailTrace_1299763 : CollatzResearch.WordTrace tailWord_1299763 prefixEnd_1299763 148311812428867423330001 := by
  unfold tailWord_1299763
  simp only [CollatzResearch.WordTrace]
  refine ⟨47406251190188107692631943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31604167460125405128421295 47406251190188107692631943)
  ·
    refine ⟨71109376785282161538947915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47406251190188107692631943 71109376785282161538947915)
    ·
      refine ⟨106664065177923242308421873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71109376785282161538947915 106664065177923242308421873)
      ·
        refine ⟨79998048883442431731316405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106664065177923242308421873 79998048883442431731316405)
        ·
          refine ⟨7499817082822727974810913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 79998048883442431731316405 7499817082822727974810913)
          ·
            refine ⟨5624862812117045981108185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7499817082822727974810913 5624862812117045981108185)
            ·
              refine ⟨4218647109087784485831139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5624862812117045981108185 4218647109087784485831139)
              ·
                refine ⟨6327970663631676728746709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4218647109087784485831139 6327970663631676728746709)
                ·
                  refine ⟨148311812428867423330001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6327970663631676728746709 148311812428867423330001)
                  ·
                    rfl

theorem cell22_1299763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 1, 7].length) (baseStart_1299763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299763 prefixEnd_1299763 := by exact prefixLift 1299763
  have htrace : WordTrace (prefixWord ++ tailWord_1299763) baseStart_1299763 baseEnd_1299763 := by
    simpa [prefixWord, tailWord_1299763, baseEnd_1299763] using wordTrace_append hprefix tailTrace_1299763
  have hstable : (prefixWord ++ tailWord_1299763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299763).length < 2 ^ (prefixWord ++ tailWord_1299763).sum := by decide
  have hdescent : baseEnd_1299763 < baseStart_1299763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299773 : List Nat := [1, 4, 1, 5, 2, 1, 2, 1, 2, 3]
def baseStart_1299773 : Nat := 118140960795 + 1299773 * 2 ^ 59
def prefixEnd_1299773 : Nat := 4983230072969 + 3 ^ 40 * 1299773 * 2
def baseEnd_1299773 : Nat := 444938860490965577239973

theorem tailTrace_1299773 : CollatzResearch.WordTrace tailWord_1299773 prefixEnd_1299773 444938860490965577239973 := by
  unfold tailWord_1299773
  simp only [CollatzResearch.WordTrace]
  refine ⟨47406615920151879400495973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31604410613434586266997315 47406615920151879400495973)
  ·
    refine ⟨8888740485028477387592995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47406615920151879400495973 8888740485028477387592995)
    ·
      refine ⟨13333110727542716081389493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8888740485028477387592995 13333110727542716081389493)
      ·
        refine ⟨1249979130707129632630265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13333110727542716081389493 1249979130707129632630265)
        ·
          refine ⟨937484348030347224472699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1249979130707129632630265 937484348030347224472699)
          ·
            refine ⟨1406226522045520836709049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937484348030347224472699 1406226522045520836709049)
            ·
              refine ⟨1054669891534140627531787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1406226522045520836709049 1054669891534140627531787)
              ·
                refine ⟨1582004837301210941297681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1054669891534140627531787 1582004837301210941297681)
                ·
                  refine ⟨1186503627975908205973261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1582004837301210941297681 1186503627975908205973261)
                  ·
                    refine ⟨444938860490965577239973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1186503627975908205973261 444938860490965577239973)
                    ·
                      rfl

theorem cell22_1299773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 1, 2, 3].length) (baseStart_1299773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299773 prefixEnd_1299773 := by exact prefixLift 1299773
  have htrace : WordTrace (prefixWord ++ tailWord_1299773) baseStart_1299773 baseEnd_1299773 := by
    simpa [prefixWord, tailWord_1299773, baseEnd_1299773] using wordTrace_append hprefix tailTrace_1299773
  have hstable : (prefixWord ++ tailWord_1299773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299773).length < 2 ^ (prefixWord ++ tailWord_1299773).sum := by decide
  have hdescent : baseEnd_1299773 < baseStart_1299773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299818 : List Nat := [3, 1, 3, 3, 2, 2, 2, 2, 1, 3]
def baseStart_1299818 : Nat := 118140960795 + 1299818 * 2 ^ 59
def prefixEnd_1299818 : Nat := 4983230072969 + 3 ^ 40 * 1299818 * 2
def baseEnd_1299818 : Nat := 444954264910600459864835

theorem tailTrace_1299818 : CollatzResearch.WordTrace tailWord_1299818 prefixEnd_1299818 444954264910600459864835 := by
  unfold tailWord_1299818
  simp only [CollatzResearch.WordTrace]
  refine ⟨11852064301247213021471027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31605504803325901390589405 11852064301247213021471027)
  ·
    refine ⟨17778096451870819532206541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11852064301247213021471027 17778096451870819532206541)
    ·
      refine ⟨6666786169451557324577453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17778096451870819532206541 6666786169451557324577453)
      ·
        refine ⟨2500044813544333996716545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6666786169451557324577453 2500044813544333996716545)
        ·
          refine ⟨1875033610158250497537409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2500044813544333996716545 1875033610158250497537409)
          ·
            refine ⟨1406275207618687873153057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1875033610158250497537409 1406275207618687873153057)
            ·
              refine ⟨1054706405714015904864793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1406275207618687873153057 1054706405714015904864793)
              ·
                refine ⟨791029804285511928648595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1054706405714015904864793 791029804285511928648595)
                ·
                  refine ⟨1186544706428267892972893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791029804285511928648595 1186544706428267892972893)
                  ·
                    refine ⟨444954264910600459864835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1186544706428267892972893 444954264910600459864835)
                    ·
                      rfl

theorem cell22_1299818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_1299818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299818 prefixEnd_1299818 := by exact prefixLift 1299818
  have htrace : WordTrace (prefixWord ++ tailWord_1299818) baseStart_1299818 baseEnd_1299818 := by
    simpa [prefixWord, tailWord_1299818, baseEnd_1299818] using wordTrace_append hprefix tailTrace_1299818
  have hstable : (prefixWord ++ tailWord_1299818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299818).length < 2 ^ (prefixWord ++ tailWord_1299818).sum := by decide
  have hdescent : baseEnd_1299818 < baseStart_1299818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299823 : List Nat := [1, 1, 2, 1, 3, 1, 3, 2, 3, 5]
def baseStart_1299823 : Nat := 118140960795 + 1299823 * 2 ^ 59
def prefixEnd_1299823 : Nat := 4983230072969 + 3 ^ 40 * 1299823 * 2
def baseEnd_1299823 : Nat := 444955976512782113489819

theorem tailTrace_1299823 : CollatzResearch.WordTrace tailWord_1299823 prefixEnd_1299823 444955976512782113489819 := by
  unfold tailWord_1299823
  simp only [CollatzResearch.WordTrace]
  refine ⟨47408439569970737939816123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31605626379980491959877415 47408439569970737939816123)
  ·
    refine ⟨71112659354956106909724185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47408439569970737939816123 71112659354956106909724185)
    ·
      refine ⟨53334494516217080182293139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71112659354956106909724185 53334494516217080182293139)
      ·
        refine ⟨80001741774325620273439709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53334494516217080182293139 80001741774325620273439709)
        ·
          refine ⟨30000653165372107602539891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80001741774325620273439709 30000653165372107602539891)
          ·
            refine ⟨45000979748058161403809837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30000653165372107602539891 45000979748058161403809837)
            ·
              refine ⟨16875367405521810526428689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45000979748058161403809837 16875367405521810526428689)
              ·
                refine ⟨12656525554141357894821517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16875367405521810526428689 12656525554141357894821517)
                ·
                  refine ⟨4746197082803009210558069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12656525554141357894821517 4746197082803009210558069)
                  ·
                    refine ⟨444955976512782113489819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4746197082803009210558069 444955976512782113489819)
                    ·
                      rfl

theorem cell22_1299823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 5].length) (baseStart_1299823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299823 prefixEnd_1299823 := by exact prefixLift 1299823
  have htrace : WordTrace (prefixWord ++ tailWord_1299823) baseStart_1299823 baseEnd_1299823 := by
    simpa [prefixWord, tailWord_1299823, baseEnd_1299823] using wordTrace_append hprefix tailTrace_1299823
  have hstable : (prefixWord ++ tailWord_1299823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299823).length < 2 ^ (prefixWord ++ tailWord_1299823).sum := by decide
  have hdescent : baseEnd_1299823 < baseStart_1299823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299842 : List Nat := [3, 4, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1299842 : Nat := 118140960795 + 1299842 * 2 ^ 59
def prefixEnd_1299842 : Nat := 4983230072969 + 3 ^ 40 * 1299842 * 2
def baseEnd_1299842 : Nat := 148320826867024132421587

theorem tailTrace_1299842 : CollatzResearch.WordTrace tailWord_1299842 prefixEnd_1299842 148320826867024132421587 := by
  unfold tailWord_1299842
  simp only [CollatzResearch.WordTrace]
  refine ⟨11852283139225476046189445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31606088371267936123171853 11852283139225476046189445)
  ·
    refine ⟨2222303088604776758660521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11852283139225476046189445 2222303088604776758660521)
    ·
      refine ⟨1666727316453582568995391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2222303088604776758660521 1666727316453582568995391)
      ·
        refine ⟨2500090974680373853493087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1666727316453582568995391 2500090974680373853493087)
        ·
          refine ⟨3750136462020560780239631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2500090974680373853493087 3750136462020560780239631)
          ·
            refine ⟨5625204693030841170359447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3750136462020560780239631 5625204693030841170359447)
            ·
              refine ⟨8437807039546261755539171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5625204693030841170359447 8437807039546261755539171)
              ·
                refine ⟨12656710559319392633308757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8437807039546261755539171 12656710559319392633308757)
                ·
                  refine ⟨148320826867024132421587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12656710559319392633308757 148320826867024132421587)
                  ·
                    rfl

theorem cell22_1299842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1299842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299842 prefixEnd_1299842 := by exact prefixLift 1299842
  have htrace : WordTrace (prefixWord ++ tailWord_1299842) baseStart_1299842 baseEnd_1299842 := by
    simpa [prefixWord, tailWord_1299842, baseEnd_1299842] using wordTrace_append hprefix tailTrace_1299842
  have hstable : (prefixWord ++ tailWord_1299842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299842).length < 2 ^ (prefixWord ++ tailWord_1299842).sum := by decide
  have hdescent : baseEnd_1299842 < baseStart_1299842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299874 : List Nat := [3, 3, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_1299874 : Nat := 118140960795 + 1299874 * 2 ^ 59
def prefixEnd_1299874 : Nat := 4983230072969 + 3 ^ 40 * 1299874 * 2
def baseEnd_1299874 : Nat := 444973434855034980464663

theorem tailTrace_1299874 : CollatzResearch.WordTrace tailWord_1299874 prefixEnd_1299874 444973434855034980464663 := by
  unfold tailWord_1299874
  simp only [CollatzResearch.WordTrace]
  refine ⟨11852574923196493412480669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31606866461857315766615117 11852574923196493412480669)
  ·
    refine ⟨4444715596198685029680251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11852574923196493412480669 4444715596198685029680251)
    ·
      refine ⟨6667073394298027544520377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4444715596198685029680251 6667073394298027544520377)
      ·
        refine ⟨5000305045723520658390283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6667073394298027544520377 5000305045723520658390283)
        ·
          refine ⟨7500457568585280987585425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5000305045723520658390283 7500457568585280987585425)
          ·
            refine ⟨5625343176438960740689069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7500457568585280987585425 5625343176438960740689069)
            ·
              refine ⟨2109503691164610277758401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5625343176438960740689069 2109503691164610277758401)
              ·
                refine ⟨1582127768373457708318801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2109503691164610277758401 1582127768373457708318801)
                ·
                  refine ⟨1186595826280093281239101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1582127768373457708318801 1186595826280093281239101)
                  ·
                    refine ⟨444973434855034980464663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1186595826280093281239101 444973434855034980464663)
                    ·
                      rfl

theorem cell22_1299874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_1299874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299874 prefixEnd_1299874 := by exact prefixLift 1299874
  have htrace : WordTrace (prefixWord ++ tailWord_1299874) baseStart_1299874 baseEnd_1299874 := by
    simpa [prefixWord, tailWord_1299874, baseEnd_1299874] using wordTrace_append hprefix tailTrace_1299874
  have hstable : (prefixWord ++ tailWord_1299874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299874).length < 2 ^ (prefixWord ++ tailWord_1299874).sum := by decide
  have hdescent : baseEnd_1299874 < baseStart_1299874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299883 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 6, 6]
def baseStart_1299883 : Nat := 118140960795 + 1299883 * 2 ^ 59
def prefixEnd_1299883 : Nat := 4983230072969 + 3 ^ 40 * 1299883 * 2
def baseEnd_1299883 : Nat := 444976515738961956989635

theorem tailTrace_1299883 : CollatzResearch.WordTrace tailWord_1299883 prefixEnd_1299883 444976515738961956989635 := by
  unfold tailWord_1299883
  simp only [CollatzResearch.WordTrace]
  refine ⟨47410627949753368187000303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31607085299835578791333535 47410627949753368187000303)
  ·
    refine ⟨71115941924630052280500455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47410627949753368187000303 71115941924630052280500455)
    ·
      refine ⟨106673912886945078420750683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71115941924630052280500455 106673912886945078420750683)
      ·
        refine ⟨160010869330417617631126025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106673912886945078420750683 160010869330417617631126025)
        ·
          refine ⟨120008151997813213223344519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160010869330417617631126025 120008151997813213223344519)
          ·
            refine ⟨180012227996719819835016779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120008151997813213223344519 180012227996719819835016779)
            ·
              refine ⟨270018341995079729752525169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180012227996719819835016779 270018341995079729752525169)
              ·
                refine ⟨202513756496309797314393877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 270018341995079729752525169 202513756496309797314393877)
                ·
                  refine ⟨9492832335764521749112213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 202513756496309797314393877 9492832335764521749112213)
                  ·
                    refine ⟨444976515738961956989635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9492832335764521749112213 444976515738961956989635)
                    ·
                      rfl

theorem cell22_1299883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 6].length) (baseStart_1299883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299883 prefixEnd_1299883 := by exact prefixLift 1299883
  have htrace : WordTrace (prefixWord ++ tailWord_1299883) baseStart_1299883 baseEnd_1299883 := by
    simpa [prefixWord, tailWord_1299883, baseEnd_1299883] using wordTrace_append hprefix tailTrace_1299883
  have hstable : (prefixWord ++ tailWord_1299883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299883).length < 2 ^ (prefixWord ++ tailWord_1299883).sum := by decide
  have hdescent : baseEnd_1299883 < baseStart_1299883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299919 : List Nat := [1, 1, 2, 1, 1, 4, 5, 3, 1, 3]
def baseStart_1299919 : Nat := 118140960795 + 1299919 * 2 ^ 59
def prefixEnd_1299919 : Nat := 4983230072969 + 3 ^ 40 * 1299919 * 2
def baseEnd_1299919 : Nat := 444988839274669863089525

theorem tailTrace_1299919 : CollatzResearch.WordTrace tailWord_1299919 prefixEnd_1299919 444988839274669863089525 := by
  unfold tailWord_1299919
  simp only [CollatzResearch.WordTrace]
  refine ⟨47411940977622946335310811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31607960651748630890207207 47411940977622946335310811)
  ·
    refine ⟨71117911466434419502966217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47411940977622946335310811 71117911466434419502966217)
    ·
      refine ⟨53338433599825814627224663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71117911466434419502966217 53338433599825814627224663)
      ·
        refine ⟨80007650399738721940836995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53338433599825814627224663 80007650399738721940836995)
        ·
          refine ⟨120011475599608082911255493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80007650399738721940836995 120011475599608082911255493)
          ·
            refine ⟨22502151674926515545860405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 120011475599608082911255493 22502151674926515545860405)
            ·
              refine ⟨2109576719524360832424413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22502151674926515545860405 2109576719524360832424413)
              ·
                refine ⟨791091269821635312159155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2109576719524360832424413 791091269821635312159155)
                ·
                  refine ⟨1186636904732452968238733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791091269821635312159155 1186636904732452968238733)
                  ·
                    refine ⟨444988839274669863089525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1186636904732452968238733 444988839274669863089525)
                    ·
                      rfl

theorem cell22_1299919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 3, 1, 3].length) (baseStart_1299919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299919 prefixEnd_1299919 := by exact prefixLift 1299919
  have htrace : WordTrace (prefixWord ++ tailWord_1299919) baseStart_1299919 baseEnd_1299919 := by
    simpa [prefixWord, tailWord_1299919, baseEnd_1299919] using wordTrace_append hprefix tailTrace_1299919
  have hstable : (prefixWord ++ tailWord_1299919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299919).length < 2 ^ (prefixWord ++ tailWord_1299919).sum := by decide
  have hdescent : baseEnd_1299919 < baseStart_1299919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299949 : List Nat := [1, 5, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1299949 : Nat := 118140960795 + 1299949 * 2 ^ 59
def prefixEnd_1299949 : Nat := 4983230072969 + 3 ^ 40 * 1299949 * 2
def baseEnd_1299949 : Nat := 148333036295919928279811

theorem tailTrace_1299949 : CollatzResearch.WordTrace tailWord_1299949 prefixEnd_1299949 148333036295919928279811 := by
  unfold tailWord_1299949
  simp only [CollatzResearch.WordTrace]
  refine ⟨47413035167514261458902901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31608690111676174305935267 47413035167514261458902901)
  ·
    refine ⟨4444972046954462011772147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47413035167514261458902901 4444972046954462011772147)
    ·
      refine ⟨6667458070431693017658221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4444972046954462011772147 6667458070431693017658221)
      ·
        refine ⟨2500296776411884881621833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6667458070431693017658221 2500296776411884881621833)
        ·
          refine ⟨1875222582308913661216375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2500296776411884881621833 1875222582308913661216375)
          ·
            refine ⟨2812833873463370491824563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875222582308913661216375 2812833873463370491824563)
            ·
              refine ⟨4219250810195055737736845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2812833873463370491824563 4219250810195055737736845)
              ·
                refine ⟨1582219053823145901651317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4219250810195055737736845 1582219053823145901651317)
                ·
                  refine ⟨148333036295919928279811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1582219053823145901651317 148333036295919928279811)
                  ·
                    rfl

theorem cell22_1299949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1299949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299949 prefixEnd_1299949 := by exact prefixLift 1299949
  have htrace : WordTrace (prefixWord ++ tailWord_1299949) baseStart_1299949 baseEnd_1299949 := by
    simpa [prefixWord, tailWord_1299949, baseEnd_1299949] using wordTrace_append hprefix tailTrace_1299949
  have hstable : (prefixWord ++ tailWord_1299949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299949).length < 2 ^ (prefixWord ++ tailWord_1299949).sum := by decide
  have hdescent : baseEnd_1299949 < baseStart_1299949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299977 : List Nat := [1, 2, 1, 1, 3, 1, 4, 5, 4]
def baseStart_1299977 : Nat := 118140960795 + 1299977 * 2 ^ 59
def prefixEnd_1299977 : Nat := 4983230072969 + 3 ^ 40 * 1299977 * 2
def baseEnd_1299977 : Nat := 148336231286659015046449

theorem tailTrace_1299977 : CollatzResearch.WordTrace tailWord_1299977 prefixEnd_1299977 148336231286659015046449 := by
  unfold tailWord_1299977
  simp only [CollatzResearch.WordTrace]
  refine ⟨47414056411412822240922185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31609370940941881493948123 47414056411412822240922185)
  ·
    refine ⟨35560542308559616680691639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47414056411412822240922185 35560542308559616680691639)
    ·
      refine ⟨53340813462839425021037459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35560542308559616680691639 53340813462839425021037459)
      ·
        refine ⟨80011220194259137531556189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53340813462839425021037459 80011220194259137531556189)
        ·
          refine ⟨30004207572847176574333571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80011220194259137531556189 30004207572847176574333571)
          ·
            refine ⟨45006311359270764861500357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30004207572847176574333571 45006311359270764861500357)
            ·
              refine ⟨8438683379863268411531317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45006311359270764861500357 8438683379863268411531317)
              ·
                refine ⟨791126566862181413581061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8438683379863268411531317 791126566862181413581061)
                ·
                  refine ⟨148336231286659015046449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 791126566862181413581061 148336231286659015046449)
                  ·
                    rfl

theorem cell22_1299977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 4, 5, 4].length) (baseStart_1299977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299977 prefixEnd_1299977 := by exact prefixLift 1299977
  have htrace : WordTrace (prefixWord ++ tailWord_1299977) baseStart_1299977 baseEnd_1299977 := by
    simpa [prefixWord, tailWord_1299977, baseEnd_1299977] using wordTrace_append hprefix tailTrace_1299977
  have hstable : (prefixWord ++ tailWord_1299977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299977).length < 2 ^ (prefixWord ++ tailWord_1299977).sum := by decide
  have hdescent : baseEnd_1299977 < baseStart_1299977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1299998 : List Nat := [4, 3, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1299998 : Nat := 118140960795 + 1299998 * 2 ^ 59
def prefixEnd_1299998 : Nat := 4983230072969 + 3 ^ 40 * 1299998 * 2
def baseEnd_1299998 : Nat := 445015882589139990364283

theorem tailTrace_1299998 : CollatzResearch.WordTrace tailWord_1299998 prefixEnd_1299998 445015882589139990364283 := by
  unfold tailWord_1299998
  simp only [CollatzResearch.WordTrace]
  refine ⟨5926852793042092853429581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31609881562891161884957765 5926852793042092853429581)
  ·
    refine ⟨2222569797390784820036093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5926852793042092853429581 2222569797390784820036093)
    ·
      refine ⟨833463674021544307513535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2222569797390784820036093 833463674021544307513535)
      ·
        refine ⟨1250195511032316461270303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833463674021544307513535 1250195511032316461270303)
        ·
          refine ⟨1875293266548474691905455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250195511032316461270303 1875293266548474691905455)
          ·
            refine ⟨2812939899822712037858183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875293266548474691905455 2812939899822712037858183)
            ·
              refine ⟨4219409849734068056787275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2812939899822712037858183 4219409849734068056787275)
              ·
                refine ⟨6329114774601102085180913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4219409849734068056787275 6329114774601102085180913)
                ·
                  refine ⟨4746836080950826563885685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6329114774601102085180913 4746836080950826563885685)
                  ·
                    refine ⟨445015882589139990364283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4746836080950826563885685 445015882589139990364283)
                    ·
                      rfl

theorem cell22_1299998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1299998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1299998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1299998 prefixEnd_1299998 := by exact prefixLift 1299998
  have htrace : WordTrace (prefixWord ++ tailWord_1299998) baseStart_1299998 baseEnd_1299998 := by
    simpa [prefixWord, tailWord_1299998, baseEnd_1299998] using wordTrace_append hprefix tailTrace_1299998
  have hstable : (prefixWord ++ tailWord_1299998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1299998).length < 2 ^ (prefixWord ++ tailWord_1299998).sum := by decide
  have hdescent : baseEnd_1299998 < baseStart_1299998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1299998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300024 : List Nat := [2, 1, 2, 1, 4, 4, 1, 1, 2, 4]
def baseStart_1300024 : Nat := 118140960795 + 1300024 * 2 ^ 59
def prefixEnd_1300024 : Nat := 4983230072969 + 3 ^ 40 * 1300024 * 2
def baseEnd_1300024 : Nat := 445024782920484589214203

theorem tailTrace_1300024 : CollatzResearch.WordTrace tailWord_1300024 prefixEnd_1300024 445024782920484589214203 := by
  unfold tailWord_1300024
  simp only [CollatzResearch.WordTrace]
  refine ⟨23707885321121274633941563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31610513761495032845255417 23707885321121274633941563)
  ·
    refine ⟨35561827981681911950912345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23707885321121274633941563 35561827981681911950912345)
    ·
      refine ⟨26671370986261433963184259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35561827981681911950912345 26671370986261433963184259)
      ·
        refine ⟨40007056479392150944776389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26671370986261433963184259 40007056479392150944776389)
        ·
          refine ⟨7501323089886028302145573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40007056479392150944776389 7501323089886028302145573)
          ·
            refine ⟨1406498079353630306652295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7501323089886028302145573 1406498079353630306652295)
            ·
              refine ⟨2109747119030445459978443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406498079353630306652295 2109747119030445459978443)
              ·
                refine ⟨3164620678545668189967665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2109747119030445459978443 3164620678545668189967665)
                ·
                  refine ⟨2373465508909251142475749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3164620678545668189967665 2373465508909251142475749)
                  ·
                    refine ⟨445024782920484589214203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2373465508909251142475749 445024782920484589214203)
                    ·
                      rfl

theorem cell22_1300024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 4, 1, 1, 2, 4].length) (baseStart_1300024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300024 prefixEnd_1300024 := by exact prefixLift 1300024
  have htrace : WordTrace (prefixWord ++ tailWord_1300024) baseStart_1300024 baseEnd_1300024 := by
    simpa [prefixWord, tailWord_1300024, baseEnd_1300024] using wordTrace_append hprefix tailTrace_1300024
  have hstable : (prefixWord ++ tailWord_1300024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300024).length < 2 ^ (prefixWord ++ tailWord_1300024).sum := by decide
  have hdescent : baseEnd_1300024 < baseStart_1300024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300037 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 5, 3]
def baseStart_1300037 : Nat := 118140960795 + 1300037 * 2 ^ 59
def prefixEnd_1300037 : Nat := 4983230072969 + 3 ^ 40 * 1300037 * 2
def baseEnd_1300037 : Nat := 445029233086156888639163

theorem tailTrace_1300037 : CollatzResearch.WordTrace tailWord_1300037 prefixEnd_1300037 445029233086156888639163 := by
  unfold tailWord_1300037
  simp only [CollatzResearch.WordTrace]
  refine ⟨47416244791195452488106365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31610829860796968325404243 47416244791195452488106365)
  ·
    refine ⟨17781091796698294683039887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47416244791195452488106365 17781091796698294683039887)
    ·
      refine ⟨26671637695047442024559831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17781091796698294683039887 26671637695047442024559831)
      ·
        refine ⟨40007456542571163036839747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26671637695047442024559831 40007456542571163036839747)
        ·
          refine ⟨60011184813856744555259621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40007456542571163036839747 60011184813856744555259621)
          ·
            refine ⟨11252097152598139604111179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60011184813856744555259621 11252097152598139604111179)
            ·
              refine ⟨16878145728897209406166769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11252097152598139604111179 16878145728897209406166769)
              ·
                refine ⟨12658609296672907054625077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16878145728897209406166769 12658609296672907054625077)
                ·
                  refine ⟨1186744621563085036371101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12658609296672907054625077 1186744621563085036371101)
                  ·
                    refine ⟨445029233086156888639163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1186744621563085036371101 445029233086156888639163)
                    ·
                      rfl

theorem cell22_1300037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_1300037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300037 prefixEnd_1300037 := by exact prefixLift 1300037
  have htrace : WordTrace (prefixWord ++ tailWord_1300037) baseStart_1300037 baseEnd_1300037 := by
    simpa [prefixWord, tailWord_1300037, baseEnd_1300037] using wordTrace_append hprefix tailTrace_1300037
  have hstable : (prefixWord ++ tailWord_1300037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300037).length < 2 ^ (prefixWord ++ tailWord_1300037).sum := by decide
  have hdescent : baseEnd_1300037 < baseStart_1300037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300193 : List Nat := [1, 2, 3, 1, 6, 1, 1, 1, 2, 4]
def baseStart_1300193 : Nat := 118140960795 + 1300193 * 2 ^ 59
def prefixEnd_1300193 : Nat := 4983230072969 + 3 ^ 40 * 1300193 * 2
def baseEnd_1300193 : Nat := 445082635074224481738685

theorem tailTrace_1300193 : CollatzResearch.WordTrace tailWord_1300193 prefixEnd_1300193 445082635074224481738685 := by
  unfold tailWord_1300193
  simp only [CollatzResearch.WordTrace]
  refine ⟨47421934578630291130785233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31614623052420194087190155 47421934578630291130785233)
  ·
    refine ⟨35566450933972718348088925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47421934578630291130785233 35566450933972718348088925)
    ·
      refine ⟨13337419100239769380533347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35566450933972718348088925 13337419100239769380533347)
      ·
        refine ⟨20006128650359654070800021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13337419100239769380533347 20006128650359654070800021)
        ·
          refine ⟨937787280485608784568751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20006128650359654070800021 937787280485608784568751)
          ·
            refine ⟨1406680920728413176853127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937787280485608784568751 1406680920728413176853127)
            ·
              refine ⟨2110021381092619765279691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406680920728413176853127 2110021381092619765279691)
              ·
                refine ⟨3165032071638929647919537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110021381092619765279691 3165032071638929647919537)
                ·
                  refine ⟨2373774053729197235939653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3165032071638929647919537 2373774053729197235939653)
                  ·
                    refine ⟨445082635074224481738685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2373774053729197235939653 445082635074224481738685)
                    ·
                      rfl

theorem cell22_1300193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 6, 1, 1, 1, 2, 4].length) (baseStart_1300193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300193 prefixEnd_1300193 := by exact prefixLift 1300193
  have htrace : WordTrace (prefixWord ++ tailWord_1300193) baseStart_1300193 baseEnd_1300193 := by
    simpa [prefixWord, tailWord_1300193, baseEnd_1300193] using wordTrace_append hprefix tailTrace_1300193
  have hstable : (prefixWord ++ tailWord_1300193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300193).length < 2 ^ (prefixWord ++ tailWord_1300193).sum := by decide
  have hdescent : baseEnd_1300193 < baseStart_1300193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300212 : List Nat := [2, 6, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_1300212 : Nat := 118140960795 + 1300212 * 2 ^ 59
def prefixEnd_1300212 : Nat := 4983230072969 + 3 ^ 40 * 1300212 * 2
def baseEnd_1300212 : Nat := 445089139162514765513627

theorem tailTrace_1300212 : CollatzResearch.WordTrace tailWord_1300212 prefixEnd_1300212 445089139162514765513627 := by
  unfold tailWord_1300212
  simp only [CollatzResearch.WordTrace]
  refine ⟨23711313782780728687863445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31615085043707638250484593 23711313782780728687863445)
  ·
    refine ⟨1111467833567846657243599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 23711313782780728687863445 1111467833567846657243599)
    ·
      refine ⟨1667201750351769985865399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1111467833567846657243599 1667201750351769985865399)
      ·
        refine ⟨2500802625527654978798099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1667201750351769985865399 2500802625527654978798099)
        ·
          refine ⟨3751203938291482468197149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2500802625527654978798099 3751203938291482468197149)
          ·
            refine ⟨1406701476859305925573931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3751203938291482468197149 1406701476859305925573931)
            ·
              refine ⟨2110052215288958888360897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406701476859305925573931 2110052215288958888360897)
              ·
                refine ⟨1582539161466719166270673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2110052215288958888360897 1582539161466719166270673)
                ·
                  refine ⟨1186904371100039374703005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1582539161466719166270673 1186904371100039374703005)
                  ·
                    refine ⟨445089139162514765513627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1186904371100039374703005 445089139162514765513627)
                    ·
                      rfl

theorem cell22_1300212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_1300212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300212 prefixEnd_1300212 := by exact prefixLift 1300212
  have htrace : WordTrace (prefixWord ++ tailWord_1300212) baseStart_1300212 baseEnd_1300212 := by
    simpa [prefixWord, tailWord_1300212, baseEnd_1300212] using wordTrace_append hprefix tailTrace_1300212
  have hstable : (prefixWord ++ tailWord_1300212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300212).length < 2 ^ (prefixWord ++ tailWord_1300212).sum := by decide
  have hdescent : baseEnd_1300212 < baseStart_1300212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300234 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_1300234 : Nat := 118140960795 + 1300234 * 2 ^ 59
def prefixEnd_1300234 : Nat := 4983230072969 + 3 ^ 40 * 1300234 * 2
def baseEnd_1300234 : Nat := 445096670212114041463559

theorem tailTrace_1300234 : CollatzResearch.WordTrace tailWord_1300234 prefixEnd_1300234 445096670212114041463559 := by
  unfold tailWord_1300234
  simp only [CollatzResearch.WordTrace]
  refine ⟨11855857492870438783256939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31615619980987836755351837 11855857492870438783256939)
  ·
    refine ⟨17783786239305658174885409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11855857492870438783256939 17783786239305658174885409)
    ·
      refine ⟨13337839679479243631164057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17783786239305658174885409 13337839679479243631164057)
      ·
        refine ⟨10003379759609432723373043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13337839679479243631164057 10003379759609432723373043)
        ·
          refine ⟨15005069639414149085059565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10003379759609432723373043 15005069639414149085059565)
          ·
            refine ⟨5626901114780305906897337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15005069639414149085059565 5626901114780305906897337)
            ·
              refine ⟨4220175836085229430173003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5626901114780305906897337 4220175836085229430173003)
              ·
                refine ⟨6330263754127844145259505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4220175836085229430173003 6330263754127844145259505)
                ·
                  refine ⟨4747697815595883108944629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6330263754127844145259505 4747697815595883108944629)
                  ·
                    refine ⟨445096670212114041463559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4747697815595883108944629 445096670212114041463559)
                    ·
                      rfl

theorem cell22_1300234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_1300234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300234 prefixEnd_1300234 := by exact prefixLift 1300234
  have htrace : WordTrace (prefixWord ++ tailWord_1300234) baseStart_1300234 baseEnd_1300234 := by
    simpa [prefixWord, tailWord_1300234, baseEnd_1300234] using wordTrace_append hprefix tailTrace_1300234
  have hstable : (prefixWord ++ tailWord_1300234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300234).length < 2 ^ (prefixWord ++ tailWord_1300234).sum := by decide
  have hdescent : baseEnd_1300234 < baseStart_1300234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300300 : List Nat := [2, 2, 1, 3, 5, 1, 1, 2, 1, 4]
def baseStart_1300300 : Nat := 118140960795 + 1300300 * 2 ^ 59
def prefixEnd_1300300 : Nat := 4983230072969 + 3 ^ 40 * 1300300 * 2
def baseEnd_1300300 : Nat := 445119263360911869313357

theorem tailTrace_1300300 : CollatzResearch.WordTrace tailWord_1300300 prefixEnd_1300300 445119263360911869313357 := by
  unfold tailWord_1300300
  simp only [CollatzResearch.WordTrace]
  refine ⟨23712918594621324202465177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31617224792828432269953569 23712918594621324202465177)
  ·
    refine ⟨17784688945965993151848883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23712918594621324202465177 17784688945965993151848883)
    ·
      refine ⟨26677033418948989727773325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17784688945965993151848883 26677033418948989727773325)
      ·
        refine ⟨10003887532105871147914997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26677033418948989727773325 10003887532105871147914997)
        ·
          refine ⟨937864456134925420117031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10003887532105871147914997 937864456134925420117031)
          ·
            refine ⟨1406796684202388130175547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 937864456134925420117031 1406796684202388130175547)
            ·
              refine ⟨2110195026303582195263321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406796684202388130175547 2110195026303582195263321)
              ·
                refine ⟨1582646269727686646447491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2110195026303582195263321 1582646269727686646447491)
                ·
                  refine ⟨2373969404591529969671237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582646269727686646447491 2373969404591529969671237)
                  ·
                    refine ⟨445119263360911869313357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2373969404591529969671237 445119263360911869313357)
                    ·
                      rfl

theorem cell22_1300300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 2, 1, 4].length) (baseStart_1300300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300300 prefixEnd_1300300 := by exact prefixLift 1300300
  have htrace : WordTrace (prefixWord ++ tailWord_1300300) baseStart_1300300 baseEnd_1300300 := by
    simpa [prefixWord, tailWord_1300300, baseEnd_1300300] using wordTrace_append hprefix tailTrace_1300300
  have hstable : (prefixWord ++ tailWord_1300300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300300).length < 2 ^ (prefixWord ++ tailWord_1300300).sum := by decide
  have hdescent : baseEnd_1300300 < baseStart_1300300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300309 : List Nat := [1, 3, 2, 2, 2, 2, 2, 8]
def baseStart_1300309 : Nat := 118140960795 + 1300309 * 2 ^ 59
def prefixEnd_1300309 : Nat := 4983230072969 + 3 ^ 40 * 1300309 * 2
def baseEnd_1300309 : Nat := 49458038249426538426481

theorem tailTrace_1300309 : CollatzResearch.WordTrace tailWord_1300309 prefixEnd_1300309 49458038249426538426481 := by
  unfold tailWord_1300309
  simp only [CollatzResearch.WordTrace]
  refine ⟨47426165446210042942007981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31617443630806695294671987 47426165446210042942007981)
  ·
    refine ⟨17784812042328766103252993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47426165446210042942007981 17784812042328766103252993)
    ·
      refine ⟨13338609031746574577439745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17784812042328766103252993 13338609031746574577439745)
      ·
        refine ⟨10003956773809930933079809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13338609031746574577439745 10003956773809930933079809)
        ·
          refine ⟨7502967580357448199809857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10003956773809930933079809 7502967580357448199809857)
          ·
            refine ⟨5627225685268086149857393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7502967580357448199809857 5627225685268086149857393)
            ·
              refine ⟨4220419263951064612393045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5627225685268086149857393 4220419263951064612393045)
              ·
                refine ⟨49458038249426538426481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4220419263951064612393045 49458038249426538426481)
                ·
                  rfl

theorem cell22_1300309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 8].length) (baseStart_1300309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300309 prefixEnd_1300309 := by exact prefixLift 1300309
  have htrace : WordTrace (prefixWord ++ tailWord_1300309) baseStart_1300309 baseEnd_1300309 := by
    simpa [prefixWord, tailWord_1300309, baseEnd_1300309] using wordTrace_append hprefix tailTrace_1300309
  have hstable : (prefixWord ++ tailWord_1300309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300309).length < 2 ^ (prefixWord ++ tailWord_1300309).sum := by decide
  have hdescent : baseEnd_1300309 < baseStart_1300309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300375 : List Nat := [1, 1, 3, 3, 1, 4, 2, 3, 1, 3]
def baseStart_1300375 : Nat := 118140960795 + 1300375 * 2 ^ 59
def prefixEnd_1300375 : Nat := 4983230072969 + 3 ^ 40 * 1300375 * 2
def baseEnd_1300375 : Nat := 445144937393636673688127

theorem tailTrace_1300375 : CollatzResearch.WordTrace tailWord_1300375 prefixEnd_1300375 445144937393636673688127 := by
  unfold tailWord_1300375
  simp only [CollatzResearch.WordTrace]
  refine ⟨47428572663970936213910579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31619048442647290809273719 47428572663970936213910579)
  ·
    refine ⟨71142858995956404320865869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47428572663970936213910579 71142858995956404320865869)
    ·
      refine ⟨26678572123483651620324701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71142858995956404320865869 26678572123483651620324701)
      ·
        refine ⟨10004464546306369357621763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26678572123483651620324701 10004464546306369357621763)
        ·
          refine ⟨15006696819459554036432645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10004464546306369357621763 15006696819459554036432645)
          ·
            refine ⟨2813755653648666381831121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15006696819459554036432645 2813755653648666381831121)
            ·
              refine ⟨2110316740236499786373341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2813755653648666381831121 2110316740236499786373341)
              ·
                refine ⟨791368777588687419890003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2110316740236499786373341 791368777588687419890003)
                ·
                  refine ⟨1187053166383031129835005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 791368777588687419890003 1187053166383031129835005)
                  ·
                    refine ⟨445144937393636673688127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1187053166383031129835005 445144937393636673688127)
                    ·
                      rfl

theorem cell22_1300375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 3, 1, 3].length) (baseStart_1300375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300375 prefixEnd_1300375 := by exact prefixLift 1300375
  have htrace : WordTrace (prefixWord ++ tailWord_1300375) baseStart_1300375 baseEnd_1300375 := by
    simpa [prefixWord, tailWord_1300375, baseEnd_1300375] using wordTrace_append hprefix tailTrace_1300375
  have hstable : (prefixWord ++ tailWord_1300375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300375).length < 2 ^ (prefixWord ++ tailWord_1300375).sum := by decide
  have hdescent : baseEnd_1300375 < baseStart_1300375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300388 : List Nat := [2, 3, 1, 2, 1, 5, 1, 2, 5]
def baseStart_1300388 : Nat := 118140960795 + 1300388 * 2 ^ 59
def prefixEnd_1300388 : Nat := 4983230072969 + 3 ^ 40 * 1300388 * 2
def baseEnd_1300388 : Nat := 148383129186436324371029

theorem tailTrace_1300388 : CollatzResearch.WordTrace tailWord_1300388 prefixEnd_1300388 148383129186436324371029 := by
  unfold tailWord_1300388
  simp only [CollatzResearch.WordTrace]
  refine ⟨23714523406461919717066909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31619364541949226289422545 23714523406461919717066909)
  ·
    refine ⟨8892946277423219893900091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23714523406461919717066909 8892946277423219893900091)
    ·
      refine ⟨13339419416134829840850137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8892946277423219893900091 13339419416134829840850137)
      ·
        refine ⟨10004564562101122380637603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13339419416134829840850137 10004564562101122380637603)
        ·
          refine ⟨15006846843151683570956405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10004564562101122380637603 15006846843151683570956405)
          ·
            refine ⟨1406891891545470334777163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15006846843151683570956405 1406891891545470334777163)
            ·
              refine ⟨2110337837318205502165745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1406891891545470334777163 2110337837318205502165745)
              ·
                refine ⟨1582753377988654126624309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2110337837318205502165745 1582753377988654126624309)
                ·
                  refine ⟨148383129186436324371029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1582753377988654126624309 148383129186436324371029)
                  ·
                    rfl

theorem cell22_1300388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 2, 5].length) (baseStart_1300388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300388 prefixEnd_1300388 := by exact prefixLift 1300388
  have htrace : WordTrace (prefixWord ++ tailWord_1300388) baseStart_1300388 baseEnd_1300388 := by
    simpa [prefixWord, tailWord_1300388, baseEnd_1300388] using wordTrace_append hprefix tailTrace_1300388
  have hstable : (prefixWord ++ tailWord_1300388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300388).length < 2 ^ (prefixWord ++ tailWord_1300388).sum := by decide
  have hdescent : baseEnd_1300388 < baseStart_1300388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300392 : List Nat := [2, 1, 6, 2, 1, 1, 2, 1, 3, 3]
def baseStart_1300392 : Nat := 118140960795 + 1300392 * 2 ^ 59
def prefixEnd_1300392 : Nat := 4983230072969 + 3 ^ 40 * 1300392 * 2
def baseEnd_1300392 : Nat := 445150756841054296013075

theorem tailTrace_1300392 : CollatzResearch.WordTrace tailWord_1300392 prefixEnd_1300392 445150756841054296013075 := by
  unfold tailWord_1300392
  simp only [CollatzResearch.WordTrace]
  refine ⟨23714596352454674058639715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31619461803272898744852953 23714596352454674058639715)
  ·
    refine ⟨35571894528682011087959573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23714596352454674058639715 35571894528682011087959573)
    ·
      refine ⟨1667432556031969269748105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35571894528682011087959573 1667432556031969269748105)
      ·
        refine ⟨1250574417023976952311079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1667432556031969269748105 1250574417023976952311079)
        ·
          refine ⟨1875861625535965428466619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1250574417023976952311079 1875861625535965428466619)
          ·
            refine ⟨2813792438303948142699929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875861625535965428466619 2813792438303948142699929)
            ·
              refine ⟨2110344328727961107024947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2813792438303948142699929 2110344328727961107024947)
              ·
                refine ⟨3165516493091941660537421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110344328727961107024947 3165516493091941660537421)
                ·
                  refine ⟨1187068684909478122701533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3165516493091941660537421 1187068684909478122701533)
                  ·
                    refine ⟨445150756841054296013075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1187068684909478122701533 445150756841054296013075)
                    ·
                      rfl

theorem cell22_1300392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_1300392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300392 prefixEnd_1300392 := by exact prefixLift 1300392
  have htrace : WordTrace (prefixWord ++ tailWord_1300392) baseStart_1300392 baseEnd_1300392 := by
    simpa [prefixWord, tailWord_1300392, baseEnd_1300392] using wordTrace_append hprefix tailTrace_1300392
  have hstable : (prefixWord ++ tailWord_1300392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300392).length < 2 ^ (prefixWord ++ tailWord_1300392).sum := by decide
  have hdescent : baseEnd_1300392 < baseStart_1300392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300431 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 6, 3]
def baseStart_1300431 : Nat := 118140960795 + 1300431 * 2 ^ 59
def prefixEnd_1300431 : Nat := 4983230072969 + 3 ^ 40 * 1300431 * 2
def baseEnd_1300431 : Nat := 445164107338071194287955

theorem tailTrace_1300431 : CollatzResearch.WordTrace tailWord_1300431 prefixEnd_1300431 445164107338071194287955 := by
  unfold tailWord_1300431
  simp only [CollatzResearch.WordTrace]
  refine ⟨47430615151768057777949147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31620410101178705185299431 47430615151768057777949147)
  ·
    refine ⟨71145922727652086666923721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47430615151768057777949147 71145922727652086666923721)
    ·
      refine ⟨53359442045739065000192791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71145922727652086666923721 53359442045739065000192791)
      ·
        refine ⟨80039163068608597500289187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53359442045739065000192791 80039163068608597500289187)
        ·
          refine ⟨120058744602912896250433781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80039163068608597500289187 120058744602912896250433781)
          ·
            refine ⟨11255507306523084023478167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 120058744602912896250433781 11255507306523084023478167)
            ·
              refine ⟨16883260959784626035217251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11255507306523084023478167 16883260959784626035217251)
              ·
                refine ⟨25324891439676939052825877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16883260959784626035217251 25324891439676939052825877)
                ·
                  refine ⟨1187104286234856518101213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25324891439676939052825877 1187104286234856518101213)
                  ·
                    refine ⟨445164107338071194287955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1187104286234856518101213 445164107338071194287955)
                    ·
                      rfl

theorem cell22_1300431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 6, 3].length) (baseStart_1300431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300431 prefixEnd_1300431 := by exact prefixLift 1300431
  have htrace : WordTrace (prefixWord ++ tailWord_1300431) baseStart_1300431 baseEnd_1300431 := by
    simpa [prefixWord, tailWord_1300431, baseEnd_1300431] using wordTrace_append hprefix tailTrace_1300431
  have hstable : (prefixWord ++ tailWord_1300431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300431).length < 2 ^ (prefixWord ++ tailWord_1300431).sum := by decide
  have hdescent : baseEnd_1300431 < baseStart_1300431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300465 : List Nat := [1, 2, 2, 2, 5, 1, 1, 3, 2, 3]
def baseStart_1300465 : Nat := 118140960795 + 1300465 * 2 ^ 59
def prefixEnd_1300465 : Nat := 4983230072969 + 3 ^ 40 * 1300465 * 2
def baseEnd_1300465 : Nat := 445175746232906438937851

theorem tailTrace_1300465 : CollatzResearch.WordTrace tailWord_1300465 prefixEnd_1300465 445175746232906438937851 := by
  unfold tailWord_1300465
  simp only [CollatzResearch.WordTrace]
  refine ⟨47431855233644881584686849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31621236822429921056457899 47431855233644881584686849)
  ·
    refine ⟨35573891425233661188515137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47431855233644881584686849 35573891425233661188515137)
    ·
      refine ⟨26680418568925245891386353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35573891425233661188515137 26680418568925245891386353)
      ·
        refine ⟨20010313926693934418539765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26680418568925245891386353 20010313926693934418539765)
        ·
          refine ⟨1875966930627556351738103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20010313926693934418539765 1875966930627556351738103)
          ·
            refine ⟨2813950395941334527607155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1875966930627556351738103 2813950395941334527607155)
            ·
              refine ⟨4220925593912001791410733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2813950395941334527607155 4220925593912001791410733)
              ·
                refine ⟨1582847097717000671779025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4220925593912001791410733 1582847097717000671779025)
                ·
                  refine ⟨1187135323287750503834269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1582847097717000671779025 1187135323287750503834269)
                  ·
                    refine ⟨445175746232906438937851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1187135323287750503834269 445175746232906438937851)
                    ·
                      rfl

theorem cell22_1300465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_1300465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300465 prefixEnd_1300465 := by exact prefixLift 1300465
  have htrace : WordTrace (prefixWord ++ tailWord_1300465) baseStart_1300465 baseEnd_1300465 := by
    simpa [prefixWord, tailWord_1300465, baseEnd_1300465] using wordTrace_append hprefix tailTrace_1300465
  have hstable : (prefixWord ++ tailWord_1300465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300465).length < 2 ^ (prefixWord ++ tailWord_1300465).sum := by decide
  have hdescent : baseEnd_1300465 < baseStart_1300465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300478 : List Nat := [4, 2, 2, 2, 1, 1, 2, 8]
def baseStart_1300478 : Nat := 118140960795 + 1300478 * 2 ^ 59
def prefixEnd_1300478 : Nat := 4983230072969 + 3 ^ 40 * 1300478 * 2
def baseEnd_1300478 : Nat := 49464466266508748706979

theorem tailTrace_1300478 : CollatzResearch.WordTrace tailWord_1300478 prefixEnd_1300478 49464466266508748706979 := by
  unfold tailWord_1300478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5929041172824723100613761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31621552921731856536606725 5929041172824723100613761)
  ·
    refine ⟨4446780879618542325460321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5929041172824723100613761 4446780879618542325460321)
    ·
      refine ⟨3335085659713906744095241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4446780879618542325460321 3335085659713906744095241)
      ·
        refine ⟨2501314244785430058071431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3335085659713906744095241 2501314244785430058071431)
        ·
          refine ⟨3751971367178145087107147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2501314244785430058071431 3751971367178145087107147)
          ·
            refine ⟨5627957050767217630660721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3751971367178145087107147 5627957050767217630660721)
            ·
              refine ⟨4220967788075413222995541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5627957050767217630660721 4220967788075413222995541)
              ·
                refine ⟨49464466266508748706979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4220967788075413222995541 49464466266508748706979)
                ·
                  rfl

theorem cell22_1300478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_1300478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300478 prefixEnd_1300478 := by exact prefixLift 1300478
  have htrace : WordTrace (prefixWord ++ tailWord_1300478) baseStart_1300478 baseEnd_1300478 := by
    simpa [prefixWord, tailWord_1300478, baseEnd_1300478] using wordTrace_append hprefix tailTrace_1300478
  have hstable : (prefixWord ++ tailWord_1300478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300478).length < 2 ^ (prefixWord ++ tailWord_1300478).sum := by decide
  have hdescent : baseEnd_1300478 < baseStart_1300478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300551 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 8]
def baseStart_1300551 : Nat := 118140960795 + 1300551 * 2 ^ 59
def prefixEnd_1300551 : Nat := 4983230072969 + 3 ^ 40 * 1300551 * 2
def baseEnd_1300551 : Nat := 148401728596810293762529

theorem tailTrace_1300551 : CollatzResearch.WordTrace tailWord_1300551 prefixEnd_1300551 148401728596810293762529 := by
  unfold tailWord_1300551
  simp only [CollatzResearch.WordTrace]
  refine ⟨47434991911333318272317507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31623327940888878848211671 47434991911333318272317507)
  ·
    refine ⟨71152487866999977408476261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47434991911333318272317507 71152487866999977408476261)
    ·
      refine ⟨13341091475062495764089299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71152487866999977408476261 13341091475062495764089299)
      ·
        refine ⟨20011637212593743646133949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13341091475062495764089299 20011637212593743646133949)
        ·
          refine ⟨7504363954722653867300231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20011637212593743646133949 7504363954722653867300231)
          ·
            refine ⟨11256545932083980800950347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7504363954722653867300231 11256545932083980800950347)
            ·
              refine ⟨16884818898125971201425521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11256545932083980800950347 16884818898125971201425521)
              ·
                refine ⟨12663614173594478401069141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16884818898125971201425521 12663614173594478401069141)
                ·
                  refine ⟨148401728596810293762529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12663614173594478401069141 148401728596810293762529)
                  ·
                    rfl

theorem cell22_1300551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 8].length) (baseStart_1300551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300551 prefixEnd_1300551 := by exact prefixLift 1300551
  have htrace : WordTrace (prefixWord ++ tailWord_1300551) baseStart_1300551 baseEnd_1300551 := by
    simpa [prefixWord, tailWord_1300551, baseEnd_1300551] using wordTrace_append hprefix tailTrace_1300551
  have hstable : (prefixWord ++ tailWord_1300551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300551).length < 2 ^ (prefixWord ++ tailWord_1300551).sum := by decide
  have hdescent : baseEnd_1300551 < baseStart_1300551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300553 : List Nat := [1, 2, 1, 1, 2, 2, 5, 3, 1, 4]
def baseStart_1300553 : Nat := 118140960795 + 1300553 * 2 ^ 59
def prefixEnd_1300553 : Nat := 4983230072969 + 3 ^ 40 * 1300553 * 2
def baseEnd_1300553 : Nat := 445205870431303542737581

theorem tailTrace_1300553 : CollatzResearch.WordTrace tailWord_1300553 prefixEnd_1300553 445205870431303542737581 := by
  unfold tailWord_1300553
  simp only [CollatzResearch.WordTrace]
  refine ⟨47435064857326072613890313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31623376571550715075926875 47435064857326072613890313)
  ·
    refine ⟨35576298642994554460417735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47435064857326072613890313 35576298642994554460417735)
    ·
      refine ⟨53364447964491831690626603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35576298642994554460417735 53364447964491831690626603)
      ·
        refine ⟨80046671946737747535939905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53364447964491831690626603 80046671946737747535939905)
        ·
          refine ⟨60035003960053310651954929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80046671946737747535939905 60035003960053310651954929)
          ·
            refine ⟨45026252970039982988966197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60035003960053310651954929 45026252970039982988966197)
            ·
              refine ⟨4221211215941248405215581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45026252970039982988966197 4221211215941248405215581)
              ·
                refine ⟨1582954205977968151955843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4221211215941248405215581 1582954205977968151955843)
                ·
                  refine ⟨2374431308966952227933765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1582954205977968151955843 2374431308966952227933765)
                  ·
                    refine ⟨445205870431303542737581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2374431308966952227933765 445205870431303542737581)
                    ·
                      rfl

theorem cell22_1300553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 3, 1, 4].length) (baseStart_1300553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300553 prefixEnd_1300553 := by exact prefixLift 1300553
  have htrace : WordTrace (prefixWord ++ tailWord_1300553) baseStart_1300553 baseEnd_1300553 := by
    simpa [prefixWord, tailWord_1300553, baseEnd_1300553] using wordTrace_append hprefix tailTrace_1300553
  have hstable : (prefixWord ++ tailWord_1300553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300553).length < 2 ^ (prefixWord ++ tailWord_1300553).sum := by decide
  have hdescent : baseEnd_1300553 < baseStart_1300553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300568 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 6]
def baseStart_1300568 : Nat := 118140960795 + 1300568 * 2 ^ 59
def prefixEnd_1300568 : Nat := 4983230072969 + 3 ^ 40 * 1300568 * 2
def baseEnd_1300568 : Nat := 148403668412616167870845

theorem tailTrace_1300568 : CollatzResearch.WordTrace tailWord_1300568 prefixEnd_1300568 148403668412616167870845 := by
  unfold tailWord_1300568
  simp only [CollatzResearch.WordTrace]
  refine ⟨23717805976135865087843179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31623741301514486783790905 23717805976135865087843179)
  ·
    refine ⟨35576708964203797631764769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23717805976135865087843179 35576708964203797631764769)
    ·
      refine ⟨26682531723152848223823577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35576708964203797631764769 26682531723152848223823577)
      ·
        refine ⟨20011898792364636167867683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26682531723152848223823577 20011898792364636167867683)
        ·
          refine ⟨30017848188546954251801525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20011898792364636167867683 30017848188546954251801525)
          ·
            refine ⟨2814173267676276961106393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30017848188546954251801525 2814173267676276961106393)
            ·
              refine ⟨2110629950757207720829795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2814173267676276961106393 2110629950757207720829795)
              ·
                refine ⟨3165944926135811581244693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2110629950757207720829795 3165944926135811581244693)
                ·
                  refine ⟨148403668412616167870845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3165944926135811581244693 148403668412616167870845)
                  ·
                    rfl

theorem cell22_1300568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 6].length) (baseStart_1300568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300568 prefixEnd_1300568 := by exact prefixLift 1300568
  have htrace : WordTrace (prefixWord ++ tailWord_1300568) baseStart_1300568 baseEnd_1300568 := by
    simpa [prefixWord, tailWord_1300568, baseEnd_1300568] using wordTrace_append hprefix tailTrace_1300568
  have hstable : (prefixWord ++ tailWord_1300568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300568).length < 2 ^ (prefixWord ++ tailWord_1300568).sum := by decide
  have hdescent : baseEnd_1300568 < baseStart_1300568 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300613 : List Nat := [1, 3, 1, 1, 5, 3, 8]
def baseStart_1300613 : Nat := 118140960795 + 1300613 * 2 ^ 59
def prefixEnd_1300613 : Nat := 4983230072969 + 3 ^ 40 * 1300613 * 2
def baseEnd_1300613 : Nat := 16489867024351236527311

theorem tailTrace_1300613 : CollatzResearch.WordTrace tailWord_1300613 prefixEnd_1300613 16489867024351236527311 := by
  unfold tailWord_1300613
  simp only [CollatzResearch.WordTrace]
  refine ⟨47437253237108702861074493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31624835491405801907382995 47437253237108702861074493)
  ·
    refine ⟨17788969963915763572902935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47437253237108702861074493 17788969963915763572902935)
    ·
      refine ⟨26683454945873645359354403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17788969963915763572902935 26683454945873645359354403)
      ·
        refine ⟨40025182418810468039031605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26683454945873645359354403 40025182418810468039031605)
        ·
          refine ⟨3752360851763481378659213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40025182418810468039031605 3752360851763481378659213)
          ·
            refine ⟨1407135319411305516997205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3752360851763481378659213 1407135319411305516997205)
            ·
              refine ⟨16489867024351236527311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1407135319411305516997205 16489867024351236527311)
              ·
                rfl

theorem cell22_1300613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 8].length) (baseStart_1300613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300613 prefixEnd_1300613 := by exact prefixLift 1300613
  have htrace : WordTrace (prefixWord ++ tailWord_1300613) baseStart_1300613 baseEnd_1300613 := by
    simpa [prefixWord, tailWord_1300613, baseEnd_1300613] using wordTrace_append hprefix tailTrace_1300613
  have hstable : (prefixWord ++ tailWord_1300613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300613).length < 2 ^ (prefixWord ++ tailWord_1300613).sum := by decide
  have hdescent : baseEnd_1300613 < baseStart_1300613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300690 : List Nat := [3, 2, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1300690 : Nat := 118140960795 + 1300690 * 2 ^ 59
def prefixEnd_1300690 : Nat := 4983230072969 + 3 ^ 40 * 1300690 * 2
def baseEnd_1300690 : Nat := 445252768331080852062161

theorem tailTrace_1300690 : CollatzResearch.WordTrace tailWord_1300690 prefixEnd_1300690 445252768331080852062161 := by
  unfold tailWord_1300690
  simp only [CollatzResearch.WordTrace]
  refine ⟨11860015414457436252906881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31626707771886496674418349 11860015414457436252906881)
  ·
    refine ⟨8895011560843077189680161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11860015414457436252906881 8895011560843077189680161)
    ·
      refine ⟨6671258670632307892260121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8895011560843077189680161 6671258670632307892260121)
      ·
        refine ⟨5003444002974230919195091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6671258670632307892260121 5003444002974230919195091)
        ·
          refine ⟨7505166004461346378792637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5003444002974230919195091 7505166004461346378792637)
          ·
            refine ⟨2814437251673004892047239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7505166004461346378792637 2814437251673004892047239)
            ·
              refine ⟨4221655877509507338070859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2814437251673004892047239 4221655877509507338070859)
              ·
                refine ⟨6332483816264261007106289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4221655877509507338070859 6332483816264261007106289)
                ·
                  refine ⟨4749362862198195755329717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6332483816264261007106289 4749362862198195755329717)
                  ·
                    refine ⟨445252768331080852062161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4749362862198195755329717 445252768331080852062161)
                    ·
                      rfl

theorem cell22_1300690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1300690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300690 prefixEnd_1300690 := by exact prefixLift 1300690
  have htrace : WordTrace (prefixWord ++ tailWord_1300690) baseStart_1300690 baseEnd_1300690 := by
    simpa [prefixWord, tailWord_1300690, baseEnd_1300690] using wordTrace_append hprefix tailTrace_1300690
  have hstable : (prefixWord ++ tailWord_1300690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300690).length < 2 ^ (prefixWord ++ tailWord_1300690).sum := by decide
  have hdescent : baseEnd_1300690 < baseStart_1300690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300705 : List Nat := [1, 2, 3, 1, 3, 1, 2, 4, 1, 4]
def baseStart_1300705 : Nat := 118140960795 + 1300705 * 2 ^ 59
def prefixEnd_1300705 : Nat := 4983230072969 + 3 ^ 40 * 1300705 * 2
def baseEnd_1300705 : Nat := 445257903137625812937115

theorem tailTrace_1300705 : CollatzResearch.WordTrace tailWord_1300705 prefixEnd_1300705 445257903137625812937115 := by
  unfold tailWord_1300705
  simp only [CollatzResearch.WordTrace]
  refine ⟨47440608752775402573423569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31627072501850268382282379 47440608752775402573423569)
  ·
    refine ⟨35580456564581551930067677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47440608752775402573423569 35580456564581551930067677)
    ·
      refine ⟨13342671211718081973775379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35580456564581551930067677 13342671211718081973775379)
      ·
        refine ⟨20014006817577122960663069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13342671211718081973775379 20014006817577122960663069)
        ·
          refine ⟨7505252556591421110248651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20014006817577122960663069 7505252556591421110248651)
          ·
            refine ⟨11257878834887131665372977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7505252556591421110248651 11257878834887131665372977)
            ·
              refine ⟨8443409126165348749029733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11257878834887131665372977 8443409126165348749029733)
              ·
                refine ⟨1583139211156002890443075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8443409126165348749029733 1583139211156002890443075)
                ·
                  refine ⟨2374708816734004335664613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583139211156002890443075 2374708816734004335664613)
                  ·
                    refine ⟨445257903137625812937115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2374708816734004335664613 445257903137625812937115)
                    ·
                      rfl

theorem cell22_1300705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_1300705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300705 prefixEnd_1300705 := by exact prefixLift 1300705
  have htrace : WordTrace (prefixWord ++ tailWord_1300705) baseStart_1300705 baseEnd_1300705 := by
    simpa [prefixWord, tailWord_1300705, baseEnd_1300705] using wordTrace_append hprefix tailTrace_1300705
  have hstable : (prefixWord ++ tailWord_1300705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300705).length < 2 ^ (prefixWord ++ tailWord_1300705).sum := by decide
  have hdescent : baseEnd_1300705 < baseStart_1300705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300722 : List Nat := [3, 2, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_1300722 : Nat := 118140960795 + 1300722 * 2 ^ 59
def prefixEnd_1300722 : Nat := 4983230072969 + 3 ^ 40 * 1300722 * 2
def baseEnd_1300722 : Nat := 445263722585043435262063

theorem tailTrace_1300722 : CollatzResearch.WordTrace tailWord_1300722 prefixEnd_1300722 445263722585043435262063 := by
  unfold tailWord_1300722
  simp only [CollatzResearch.WordTrace]
  refine ⟨11860307198428453619198105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31627485862475876317861613 11860307198428453619198105)
  ·
    refine ⟨8895230398821340214398579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11860307198428453619198105 8895230398821340214398579)
    ·
      refine ⟨13342845598232010321597869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8895230398821340214398579 13342845598232010321597869)
      ·
        refine ⟨5003567099337003870599201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13342845598232010321597869 5003567099337003870599201)
        ·
          refine ⟨3752675324502752902949401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5003567099337003870599201 3752675324502752902949401)
          ·
            refine ⟨2814506493377064677212051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3752675324502752902949401 2814506493377064677212051)
            ·
              refine ⟨4221759740065597015818077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2814506493377064677212051 4221759740065597015818077)
              ·
                refine ⟨1583159902524598880931779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4221759740065597015818077 1583159902524598880931779)
                ·
                  refine ⟨2374739853786898321397669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583159902524598880931779 2374739853786898321397669)
                  ·
                    refine ⟨445263722585043435262063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2374739853786898321397669 445263722585043435262063)
                    ·
                      rfl

theorem cell22_1300722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_1300722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300722 prefixEnd_1300722 := by exact prefixLift 1300722
  have htrace : WordTrace (prefixWord ++ tailWord_1300722) baseStart_1300722 baseEnd_1300722 := by
    simpa [prefixWord, tailWord_1300722, baseEnd_1300722] using wordTrace_append hprefix tailTrace_1300722
  have hstable : (prefixWord ++ tailWord_1300722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300722).length < 2 ^ (prefixWord ++ tailWord_1300722).sum := by decide
  have hdescent : baseEnd_1300722 < baseStart_1300722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300735 : List Nat := [1, 1, 2, 2, 1, 4, 3, 1, 4, 3]
def baseStart_1300735 : Nat := 118140960795 + 1300735 * 2 ^ 59
def prefixEnd_1300735 : Nat := 4983230072969 + 3 ^ 40 * 1300735 * 2
def baseEnd_1300735 : Nat := 445268172750715734687023

theorem tailTrace_1300735 : CollatzResearch.WordTrace tailWord_1300735 prefixEnd_1300735 445268172750715734687023 := by
  unfold tailWord_1300735
  simp only [CollatzResearch.WordTrace]
  refine ⟨47441702942666717697015659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31627801961777811798010439 47441702942666717697015659)
  ·
    refine ⟨71162554414000076545523489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47441702942666717697015659 71162554414000076545523489)
    ·
      refine ⟨53371915810500057409142617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71162554414000076545523489 53371915810500057409142617)
      ·
        refine ⟨40028936857875043056856963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53371915810500057409142617 40028936857875043056856963)
        ·
          refine ⟨60043405286812564585285445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40028936857875043056856963 60043405286812564585285445)
          ·
            refine ⟨11258138491277355859741021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60043405286812564585285445 11258138491277355859741021)
            ·
              refine ⟨4221801934229008447402883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11258138491277355859741021 4221801934229008447402883)
              ·
                refine ⟨6332702901343512671104325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4221801934229008447402883 6332702901343512671104325)
                ·
                  refine ⟨1187381794001908625832061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6332702901343512671104325 1187381794001908625832061)
                  ·
                    refine ⟨445268172750715734687023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1187381794001908625832061 445268172750715734687023)
                    ·
                      rfl

theorem cell22_1300735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 3, 1, 4, 3].length) (baseStart_1300735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300735 prefixEnd_1300735 := by exact prefixLift 1300735
  have htrace : WordTrace (prefixWord ++ tailWord_1300735) baseStart_1300735 baseEnd_1300735 := by
    simpa [prefixWord, tailWord_1300735, baseEnd_1300735] using wordTrace_append hprefix tailTrace_1300735
  have hstable : (prefixWord ++ tailWord_1300735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300735).length < 2 ^ (prefixWord ++ tailWord_1300735).sum := by decide
  have hdescent : baseEnd_1300735 < baseStart_1300735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300748 : List Nat := [2, 2, 1, 2, 2, 2, 2, 9]
def baseStart_1300748 : Nat := 118140960795 + 1300748 * 2 ^ 59
def prefixEnd_1300748 : Nat := 4983230072969 + 3 ^ 40 * 1300748 * 2
def baseEnd_1300748 : Nat := 49474735879598670456887

theorem tailTrace_1300748 : CollatzResearch.WordTrace tailWord_1300748 prefixEnd_1300748 49474735879598670456887 := by
  unfold tailWord_1300748
  simp only [CollatzResearch.WordTrace]
  refine ⟨23721088545809810458619449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31628118061079747278159265 23721088545809810458619449)
  ·
    refine ⟨17790816409357357843964587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23721088545809810458619449 17790816409357357843964587)
    ·
      refine ⟨26686224614036036765946881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17790816409357357843964587 26686224614036036765946881)
      ·
        refine ⟨20014668460527027574460161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26686224614036036765946881 20014668460527027574460161)
        ·
          refine ⟨15011001345395270680845121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20014668460527027574460161 15011001345395270680845121)
          ·
            refine ⟨11258251009046453010633841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15011001345395270680845121 11258251009046453010633841)
            ·
              refine ⟨8443688256784839757975381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11258251009046453010633841 8443688256784839757975381)
              ·
                refine ⟨49474735879598670456887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8443688256784839757975381 49474735879598670456887)
                ·
                  rfl

theorem cell22_1300748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 9].length) (baseStart_1300748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300748 prefixEnd_1300748 := by exact prefixLift 1300748
  have htrace : WordTrace (prefixWord ++ tailWord_1300748) baseStart_1300748 baseEnd_1300748 := by
    simpa [prefixWord, tailWord_1300748, baseEnd_1300748] using wordTrace_append hprefix tailTrace_1300748
  have hstable : (prefixWord ++ tailWord_1300748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300748).length < 2 ^ (prefixWord ++ tailWord_1300748).sum := by decide
  have hdescent : baseEnd_1300748 < baseStart_1300748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300780 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 5, 3]
def baseStart_1300780 : Nat := 118140960795 + 1300780 * 2 ^ 59
def prefixEnd_1300780 : Nat := 4983230072969 + 3 ^ 40 * 1300780 * 2
def baseEnd_1300780 : Nat := 445283577170350617311885

theorem tailTrace_1300780 : CollatzResearch.WordTrace tailWord_1300780 prefixEnd_1300780 445283577170350617311885 := by
  unfold tailWord_1300780
  simp only [CollatzResearch.WordTrace]
  refine ⟨23721672113751845191201897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31628896151669126921602529 23721672113751845191201897)
  ·
    refine ⟨17791254085313883893401423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23721672113751845191201897 17791254085313883893401423)
    ·
      refine ⟨26686881127970825840102135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17791254085313883893401423 26686881127970825840102135)
      ·
        refine ⟨40030321691956238760153203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26686881127970825840102135 40030321691956238760153203)
        ·
          refine ⟨60045482537934358140229805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40030321691956238760153203 60045482537934358140229805)
          ·
            refine ⟨22517055951725384302586177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60045482537934358140229805 22517055951725384302586177)
            ·
              refine ⟨16887791963794038226939633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22517055951725384302586177 16887791963794038226939633)
              ·
                refine ⟨12665843972845528670204725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16887791963794038226939633 12665843972845528670204725)
                ·
                  refine ⟨1187422872454268312831693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12665843972845528670204725 1187422872454268312831693)
                  ·
                    refine ⟨445283577170350617311885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1187422872454268312831693 445283577170350617311885)
                    ·
                      rfl

theorem cell22_1300780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 5, 3].length) (baseStart_1300780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300780 prefixEnd_1300780 := by exact prefixLift 1300780
  have htrace : WordTrace (prefixWord ++ tailWord_1300780) baseStart_1300780 baseEnd_1300780 := by
    simpa [prefixWord, tailWord_1300780, baseEnd_1300780] using wordTrace_append hprefix tailTrace_1300780
  have hstable : (prefixWord ++ tailWord_1300780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300780).length < 2 ^ (prefixWord ++ tailWord_1300780).sum := by decide
  have hdescent : baseEnd_1300780 < baseStart_1300780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300921 : List Nat := [1, 2, 1, 4, 3, 2, 3, 1, 2, 3]
def baseStart_1300921 : Nat := 118140960795 + 1300921 * 2 ^ 59
def prefixEnd_1300921 : Nat := 4983230072969 + 3 ^ 40 * 1300921 * 2
def baseEnd_1300921 : Nat := 445331844351873249536453

theorem tailTrace_1300921 : CollatzResearch.WordTrace tailWord_1300921 prefixEnd_1300921 445331844351873249536453 := by
  unfold tailWord_1300921
  simp only [CollatzResearch.WordTrace]
  refine ⟨47448486919992871463286617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31632324613328580975524411 47448486919992871463286617)
  ·
    refine ⟨35586365189994653597464963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47448486919992871463286617 35586365189994653597464963)
    ·
      refine ⟨53379547784991980396197445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35586365189994653597464963 53379547784991980396197445)
      ·
        refine ⟨10008665209685996324287021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53379547784991980396197445 10008665209685996324287021)
        ·
          refine ⟨3753249453632248621607633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10008665209685996324287021 3753249453632248621607633)
          ·
            refine ⟨2814937090224186466205725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3753249453632248621607633 2814937090224186466205725)
            ·
              refine ⟨1055601408834069924827147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2814937090224186466205725 1055601408834069924827147)
              ·
                refine ⟨1583402113251104887240721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055601408834069924827147 1583402113251104887240721)
                ·
                  refine ⟨1187551584938328665430541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1583402113251104887240721 1187551584938328665430541)
                  ·
                    refine ⟨445331844351873249536453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1187551584938328665430541 445331844351873249536453)
                    ·
                      rfl

theorem cell22_1300921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 1, 2, 3].length) (baseStart_1300921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300921 prefixEnd_1300921 := by exact prefixLift 1300921
  have htrace : WordTrace (prefixWord ++ tailWord_1300921) baseStart_1300921 baseEnd_1300921 := by
    simpa [prefixWord, tailWord_1300921, baseEnd_1300921] using wordTrace_append hprefix tailTrace_1300921
  have hstable : (prefixWord ++ tailWord_1300921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300921).length < 2 ^ (prefixWord ++ tailWord_1300921).sum := by decide
  have hdescent : baseEnd_1300921 < baseStart_1300921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1300975 : List Nat := [1, 1, 2, 1, 4, 1, 1, 1, 2, 8]
def baseStart_1300975 : Nat := 118140960795 + 1300975 * 2 ^ 59
def prefixEnd_1300975 : Nat := 4983230072969 + 3 ^ 40 * 1300975 * 2
def baseEnd_1300975 : Nat := 445350329655435108686287

theorem tailTrace_1300975 : CollatzResearch.WordTrace tailWord_1300975 prefixEnd_1300975 445350329655435108686287 := by
  unfold tailWord_1300975
  simp only [CollatzResearch.WordTrace]
  refine ⟨47450456461797238685752379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31633637641198159123834919 47450456461797238685752379)
  ·
    refine ⟨71175684692695858028628569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47450456461797238685752379 71175684692695858028628569)
    ·
      refine ⟨53381763519521893521471427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71175684692695858028628569 53381763519521893521471427)
      ·
        refine ⟨80072645279282840282207141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53381763519521893521471427 80072645279282840282207141)
        ·
          refine ⟨15013620989865532552913839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80072645279282840282207141 15013620989865532552913839)
          ·
            refine ⟨22520431484798298829370759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15013620989865532552913839 22520431484798298829370759)
            ·
              refine ⟨33780647227197448244056139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22520431484798298829370759 33780647227197448244056139)
              ·
                refine ⟨50670970840796172366084209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33780647227197448244056139 50670970840796172366084209)
                ·
                  refine ⟨38003228130597129274563157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50670970840796172366084209 38003228130597129274563157)
                  ·
                    refine ⟨445350329655435108686287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38003228130597129274563157 445350329655435108686287)
                    ·
                      rfl

theorem cell22_1300975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 2, 8].length) (baseStart_1300975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1300975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1300975 prefixEnd_1300975 := by exact prefixLift 1300975
  have htrace : WordTrace (prefixWord ++ tailWord_1300975) baseStart_1300975 baseEnd_1300975 := by
    simpa [prefixWord, tailWord_1300975, baseEnd_1300975] using wordTrace_append hprefix tailTrace_1300975
  have hstable : (prefixWord ++ tailWord_1300975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1300975).length < 2 ^ (prefixWord ++ tailWord_1300975).sum := by decide
  have hdescent : baseEnd_1300975 < baseStart_1300975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1300975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301060 : List Nat := [2, 3, 5, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1301060 : Nat := 118140960795 + 1301060 * 2 ^ 59
def prefixEnd_1301060 : Nat := 4983230072969 + 3 ^ 40 * 1301060 * 2
def baseEnd_1301060 : Nat := 445379426892523220311027

theorem tailTrace_1301060 : CollatzResearch.WordTrace tailWord_1301060 prefixEnd_1301060 445379426892523220311027 := by
  unfold tailWord_1301060
  simp only [CollatzResearch.WordTrace]
  refine ⟨23726778333244649101298317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31635704444326198801731089 23726778333244649101298317)
  ·
    refine ⟨8897541874966743412986869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23726778333244649101298317 8897541874966743412986869)
    ·
      refine ⟨834144550778132194967519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8897541874966743412986869 834144550778132194967519)
      ·
        refine ⟨1251216826167198292451279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 834144550778132194967519 1251216826167198292451279)
        ·
          refine ⟨1876825239250797438676919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1251216826167198292451279 1876825239250797438676919)
          ·
            refine ⟨2815237858876196158015379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1876825239250797438676919 2815237858876196158015379)
            ·
              refine ⟨4222856788314294237023069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2815237858876196158015379 4222856788314294237023069)
              ·
                refine ⟨1583571295617860338883651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4222856788314294237023069 1583571295617860338883651)
                ·
                  refine ⟨2375356943426790508325477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1583571295617860338883651 2375356943426790508325477)
                  ·
                    refine ⟨445379426892523220311027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2375356943426790508325477 445379426892523220311027)
                    ·
                      rfl

theorem cell22_1301060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1301060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301060 prefixEnd_1301060 := by exact prefixLift 1301060
  have htrace : WordTrace (prefixWord ++ tailWord_1301060) baseStart_1301060 baseEnd_1301060 := by
    simpa [prefixWord, tailWord_1301060, baseEnd_1301060] using wordTrace_append hprefix tailTrace_1301060
  have hstable : (prefixWord ++ tailWord_1301060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301060).length < 2 ^ (prefixWord ++ tailWord_1301060).sum := by decide
  have hdescent : baseEnd_1301060 < baseStart_1301060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301069 : List Nat := [1, 6, 1, 1, 2, 2, 9]
def baseStart_1301069 : Nat := 118140960795 + 1301069 * 2 ^ 59
def prefixEnd_1301069 : Nat := 4983230072969 + 3 ^ 40 * 1301069 * 2
def baseEnd_1301069 : Nat := 16495648436164822105037

theorem tailTrace_1301069 : CollatzResearch.WordTrace tailWord_1301069 prefixEnd_1301069 16495648436164822105037 := by
  unfold tailWord_1301069
  simp only [CollatzResearch.WordTrace]
  refine ⟨47453884923456692739674261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31635923282304461826449507 47453884923456692739674261)
  ·
    refine ⟨2224400855787032472172231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47453884923456692739674261 2224400855787032472172231)
    ·
      refine ⟨3336601283680548708258347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2224400855787032472172231 3336601283680548708258347)
      ·
        refine ⟨5004901925520823062387521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3336601283680548708258347 5004901925520823062387521)
        ·
          refine ⟨3753676444140617296790641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5004901925520823062387521 3753676444140617296790641)
          ·
            refine ⟨2815257333105462972592981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3753676444140617296790641 2815257333105462972592981)
            ·
              refine ⟨16495648436164822105037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2815257333105462972592981 16495648436164822105037)
              ·
                rfl

theorem cell22_1301069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 9].length) (baseStart_1301069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301069 prefixEnd_1301069 := by exact prefixLift 1301069
  have htrace : WordTrace (prefixWord ++ tailWord_1301069) baseStart_1301069 baseEnd_1301069 := by
    simpa [prefixWord, tailWord_1301069, baseEnd_1301069] using wordTrace_append hprefix tailTrace_1301069
  have hstable : (prefixWord ++ tailWord_1301069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301069).length < 2 ^ (prefixWord ++ tailWord_1301069).sum := by decide
  have hdescent : baseEnd_1301069 < baseStart_1301069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301090 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 1, 5]
def baseStart_1301090 : Nat := 118140960795 + 1301090 * 2 ^ 59
def prefixEnd_1301090 : Nat := 4983230072969 + 3 ^ 40 * 1301090 * 2
def baseEnd_1301090 : Nat := 445389696505613142060935

theorem tailTrace_1301090 : CollatzResearch.WordTrace tailWord_1301090 prefixEnd_1301090 445389696505613142060935 := by
  unfold tailWord_1301090
  simp only [CollatzResearch.WordTrace]
  refine ⟨11863662714095153331547181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31636433904253742217459149 11863662714095153331547181)
  ·
    refine ⟨4448873517785682499330193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11863662714095153331547181 4448873517785682499330193)
    ·
      refine ⟨3336655138339261874497645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4448873517785682499330193 3336655138339261874497645)
      ·
        refine ⟨1251245676877223202936617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3336655138339261874497645 1251245676877223202936617)
        ·
          refine ⟨938434257657917402202463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1251245676877223202936617 938434257657917402202463)
          ·
            refine ⟨1407651386486876103303695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 938434257657917402202463 1407651386486876103303695)
            ·
              refine ⟨2111477079730314154955543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1407651386486876103303695 2111477079730314154955543)
              ·
                refine ⟨3167215619595471232433315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111477079730314154955543 3167215619595471232433315)
                ·
                  refine ⟨4750823429393206848649973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3167215619595471232433315 4750823429393206848649973)
                  ·
                    refine ⟨445389696505613142060935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4750823429393206848649973 445389696505613142060935)
                    ·
                      rfl

theorem cell22_1301090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_1301090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301090 prefixEnd_1301090 := by exact prefixLift 1301090
  have htrace : WordTrace (prefixWord ++ tailWord_1301090) baseStart_1301090 baseEnd_1301090 := by
    simpa [prefixWord, tailWord_1301090, baseEnd_1301090] using wordTrace_append hprefix tailTrace_1301090
  have hstable : (prefixWord ++ tailWord_1301090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301090).length < 2 ^ (prefixWord ++ tailWord_1301090).sum := by decide
  have hdescent : baseEnd_1301090 < baseStart_1301090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301101 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 3, 3]
def baseStart_1301101 : Nat := 118140960795 + 1301101 * 2 ^ 59
def prefixEnd_1301101 : Nat := 4983230072969 + 3 ^ 40 * 1301101 * 2
def baseEnd_1301101 : Nat := 445393462030412780035901

theorem tailTrace_1301101 : CollatzResearch.WordTrace tailWord_1301101 prefixEnd_1301101 445393462030412780035901 := by
  unfold tailWord_1301101
  simp only [CollatzResearch.WordTrace]
  refine ⟨47455052059340762204839157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31636701372893841469892771 47455052059340762204839157)
  ·
    refine ⟨4448911130563196456703671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47455052059340762204839157 4448911130563196456703671)
    ·
      refine ⟨6673366695844794685055507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4448911130563196456703671 6673366695844794685055507)
      ·
        refine ⟨10010050043767192027583261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6673366695844794685055507 10010050043767192027583261)
        ·
          refine ⟨3753768766412697010343723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10010050043767192027583261 3753768766412697010343723)
          ·
            refine ⟨5630653149619045515515585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3753768766412697010343723 5630653149619045515515585)
            ·
              refine ⟨4222989862214284136636689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5630653149619045515515585 4222989862214284136636689)
              ·
                refine ⟨3167242396660713102477517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4222989862214284136636689 3167242396660713102477517)
                ·
                  refine ⟨1187715898747767413429069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3167242396660713102477517 1187715898747767413429069)
                  ·
                    refine ⟨445393462030412780035901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1187715898747767413429069 445393462030412780035901)
                    ·
                      rfl

theorem cell22_1301101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_1301101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301101 prefixEnd_1301101 := by exact prefixLift 1301101
  have htrace : WordTrace (prefixWord ++ tailWord_1301101) baseStart_1301101 baseEnd_1301101 := by
    simpa [prefixWord, tailWord_1301101, baseEnd_1301101] using wordTrace_append hprefix tailTrace_1301101
  have hstable : (prefixWord ++ tailWord_1301101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301101).length < 2 ^ (prefixWord ++ tailWord_1301101).sum := by decide
  have hdescent : baseEnd_1301101 < baseStart_1301101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301144 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 3, 4]
def baseStart_1301144 : Nat := 118140960795 + 1301144 * 2 ^ 59
def prefixEnd_1301144 : Nat := 4983230072969 + 3 ^ 40 * 1301144 * 2
def baseEnd_1301144 : Nat := 445408181809175001210769

theorem tailTrace_1301144 : CollatzResearch.WordTrace tailWord_1301144 prefixEnd_1301144 445408181809175001210769 := by
  unfold tailWord_1301144
  simp only [CollatzResearch.WordTrace]
  refine ⟨23728310199092490274327243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31637746932123320365769657 23728310199092490274327243)
  ·
    refine ⟨35592465298638735411490865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23728310199092490274327243 35592465298638735411490865)
    ·
      refine ⟨26694348973979051558618149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35592465298638735411490865 26694348973979051558618149)
      ·
        refine ⟨5005190432621072167240903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26694348973979051558618149 5005190432621072167240903)
        ·
          refine ⟨7507785648931608250861355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5005190432621072167240903 7507785648931608250861355)
          ·
            refine ⟨11261678473397412376292033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7507785648931608250861355 11261678473397412376292033)
            ·
              refine ⟨8446258855048059282219025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11261678473397412376292033 8446258855048059282219025)
              ·
                refine ⟨6334694141286044461664269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8446258855048059282219025 6334694141286044461664269)
                ·
                  refine ⟨2375510302982266673124101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6334694141286044461664269 2375510302982266673124101)
                  ·
                    refine ⟨445408181809175001210769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2375510302982266673124101 445408181809175001210769)
                    ·
                      rfl

theorem cell22_1301144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 3, 4].length) (baseStart_1301144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301144 prefixEnd_1301144 := by exact prefixLift 1301144
  have htrace : WordTrace (prefixWord ++ tailWord_1301144) baseStart_1301144 baseEnd_1301144 := by
    simpa [prefixWord, tailWord_1301144, baseEnd_1301144] using wordTrace_append hprefix tailTrace_1301144
  have hstable : (prefixWord ++ tailWord_1301144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301144).length < 2 ^ (prefixWord ++ tailWord_1301144).sum := by decide
  have hdescent : baseEnd_1301144 < baseStart_1301144 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301148 : List Nat := [2, 2, 3, 2, 2, 3, 2, 1, 5]
def baseStart_1301148 : Nat := 118140960795 + 1301148 * 2 ^ 59
def prefixEnd_1301148 : Nat := 4983230072969 + 3 ^ 40 * 1301148 * 2
def baseEnd_1301148 : Nat := 148469850363640108036919

theorem tailTrace_1301148 : CollatzResearch.WordTrace tailWord_1301148 prefixEnd_1301148 148469850363640108036919 := by
  unfold tailWord_1301148
  simp only [CollatzResearch.WordTrace]
  refine ⟨23728383145085244615900049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31637844193446992821200065 23728383145085244615900049)
  ·
    refine ⟨17796287358813933461925037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23728383145085244615900049 17796287358813933461925037)
    ·
      refine ⟨6673607759555225048221889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17796287358813933461925037 6673607759555225048221889)
      ·
        refine ⟨5005205819666418786166417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6673607759555225048221889 5005205819666418786166417)
        ·
          refine ⟨3753904364749814089624813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5005205819666418786166417 3753904364749814089624813)
          ·
            refine ⟨1407714136781180283609305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3753904364749814089624813 1407714136781180283609305)
            ·
              refine ⟨1055785602585885212706979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1407714136781180283609305 1055785602585885212706979)
              ·
                refine ⟨1583678403878827819060469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1055785602585885212706979 1583678403878827819060469)
                ·
                  refine ⟨148469850363640108036919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1583678403878827819060469 148469850363640108036919)
                  ·
                    rfl

theorem cell22_1301148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_1301148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301148 prefixEnd_1301148 := by exact prefixLift 1301148
  have htrace : WordTrace (prefixWord ++ tailWord_1301148) baseStart_1301148 baseEnd_1301148 := by
    simpa [prefixWord, tailWord_1301148, baseEnd_1301148] using wordTrace_append hprefix tailTrace_1301148
  have hstable : (prefixWord ++ tailWord_1301148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301148).length < 2 ^ (prefixWord ++ tailWord_1301148).sum := by decide
  have hdescent : baseEnd_1301148 < baseStart_1301148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301221 : List Nat := [1, 3, 1, 4, 1, 3, 3, 6]
def baseStart_1301221 : Nat := 118140960795 + 1301221 * 2 ^ 59
def prefixEnd_1301221 : Nat := 4983230072969 + 3 ^ 40 * 1301221 * 2
def baseEnd_1301221 : Nat := 49492726720308051892837

theorem tailTrace_1301221 : CollatzResearch.WordTrace tailWord_1301221 prefixEnd_1301221 49492726720308051892837 := by
  unfold tailWord_1301221
  simp only [CollatzResearch.WordTrace]
  refine ⟨47459428818906022699207517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31639619212604015132805011 47459428818906022699207517)
  ·
    refine ⟨17797285807089758512202819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47459428818906022699207517 17797285807089758512202819)
    ·
      refine ⟨26695928710634637768304229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17797285807089758512202819 26695928710634637768304229)
      ·
        refine ⟨5005486633243994581557043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26695928710634637768304229 5005486633243994581557043)
        ·
          refine ⟨7508229949865991872335565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5005486633243994581557043 7508229949865991872335565)
          ·
            refine ⟨2815586231199746952125837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7508229949865991872335565 2815586231199746952125837)
            ·
              refine ⟨1055844836699905107047189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2815586231199746952125837 1055844836699905107047189)
              ·
                refine ⟨49492726720308051892837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1055844836699905107047189 49492726720308051892837)
                ·
                  rfl

theorem cell22_1301221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 6].length) (baseStart_1301221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301221 prefixEnd_1301221 := by exact prefixLift 1301221
  have htrace : WordTrace (prefixWord ++ tailWord_1301221) baseStart_1301221 baseEnd_1301221 := by
    simpa [prefixWord, tailWord_1301221, baseEnd_1301221] using wordTrace_append hprefix tailTrace_1301221
  have hstable : (prefixWord ++ tailWord_1301221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301221).length < 2 ^ (prefixWord ++ tailWord_1301221).sum := by decide
  have hdescent : baseEnd_1301221 < baseStart_1301221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301311 : List Nat := [1, 1, 2, 2, 5, 1, 3, 1, 6]
def baseStart_1301311 : Nat := 118140960795 + 1301311 * 2 ^ 59
def prefixEnd_1301311 : Nat := 4983230072969 + 3 ^ 40 * 1301311 * 2
def baseEnd_1301311 : Nat := 148488449774014077428419

theorem tailTrace_1301311 : CollatzResearch.WordTrace tailWord_1301311 prefixEnd_1301311 148488449774014077428419 := by
  unfold tailWord_1301311
  simp only [CollatzResearch.WordTrace]
  refine ⟨47462711388579968069983787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31641807592386645379989191 47462711388579968069983787)
  ·
    refine ⟨71194067082869952104975681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47462711388579968069983787 71194067082869952104975681)
    ·
      refine ⟨53395550312152464078731761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71194067082869952104975681 53395550312152464078731761)
      ·
        refine ⟨40046662734114348059048821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53395550312152464078731761 40046662734114348059048821)
        ·
          refine ⟨3754374631323220130535827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 40046662734114348059048821 3754374631323220130535827)
          ·
            refine ⟨5631561946984830195803741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3754374631323220130535827 5631561946984830195803741)
            ·
              refine ⟨2111835730119311323426403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5631561946984830195803741 2111835730119311323426403)
              ·
                refine ⟨3167753595178966985139605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2111835730119311323426403 3167753595178966985139605)
                ·
                  refine ⟨148488449774014077428419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3167753595178966985139605 148488449774014077428419)
                  ·
                    rfl

theorem cell22_1301311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 3, 1, 6].length) (baseStart_1301311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301311 prefixEnd_1301311 := by exact prefixLift 1301311
  have htrace : WordTrace (prefixWord ++ tailWord_1301311) baseStart_1301311 baseEnd_1301311 := by
    simpa [prefixWord, tailWord_1301311, baseEnd_1301311] using wordTrace_append hprefix tailTrace_1301311
  have hstable : (prefixWord ++ tailWord_1301311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301311).length < 2 ^ (prefixWord ++ tailWord_1301311).sum := by decide
  have hdescent : baseEnd_1301311 < baseStart_1301311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301431 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 5, 4]
def baseStart_1301431 : Nat := 118140960795 + 1301431 * 2 ^ 59
def prefixEnd_1301431 : Nat := 4983230072969 + 3 ^ 40 * 1301431 * 2
def baseEnd_1301431 : Nat := 445506427774401919284889

theorem tailTrace_1301431 : CollatzResearch.WordTrace tailWord_1301431 prefixEnd_1301431 445506427774401919284889 := by
  unfold tailWord_1301431
  simp only [CollatzResearch.WordTrace]
  refine ⟨47467088148145228564352147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31644725432096819042901431 47467088148145228564352147)
  ·
    refine ⟨71200632222217842846528221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47467088148145228564352147 71200632222217842846528221)
    ·
      refine ⟨26700237083331691067448083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71200632222217842846528221 26700237083331691067448083)
      ·
        refine ⟨40050355624997536601172125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26700237083331691067448083 40050355624997536601172125)
        ·
          refine ⟨15018883359374076225439547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40050355624997536601172125 15018883359374076225439547)
          ·
            refine ⟨22528325039061114338159321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15018883359374076225439547 22528325039061114338159321)
            ·
              refine ⟨16896243779295835753619491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22528325039061114338159321 16896243779295835753619491)
              ·
                refine ⟨25344365668943753630429237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16896243779295835753619491 25344365668943753630429237)
                ·
                  refine ⟨2376034281463476902852741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 25344365668943753630429237 2376034281463476902852741)
                  ·
                    refine ⟨445506427774401919284889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2376034281463476902852741 445506427774401919284889)
                    ·
                      rfl

theorem cell22_1301431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 5, 4].length) (baseStart_1301431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301431 prefixEnd_1301431 := by exact prefixLift 1301431
  have htrace : WordTrace (prefixWord ++ tailWord_1301431) baseStart_1301431 baseEnd_1301431 := by
    simpa [prefixWord, tailWord_1301431, baseEnd_1301431] using wordTrace_append hprefix tailTrace_1301431
  have hstable : (prefixWord ++ tailWord_1301431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301431).length < 2 ^ (prefixWord ++ tailWord_1301431).sum := by decide
  have hdescent : baseEnd_1301431 < baseStart_1301431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301463 : List Nat := [1, 1, 3, 2, 1, 1, 2, 7, 4]
def baseStart_1301463 : Nat := 118140960795 + 1301463 * 2 ^ 59
def prefixEnd_1301463 : Nat := 4983230072969 + 3 ^ 40 * 1301463 * 2
def baseEnd_1301463 : Nat := 148505794009454834161597

theorem tailTrace_1301463 : CollatzResearch.WordTrace tailWord_1301463 prefixEnd_1301463 148505794009454834161597 := by
  unfold tailWord_1301463
  simp only [CollatzResearch.WordTrace]
  refine ⟨47468255284029298029517043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31645503522686198686344695 47468255284029298029517043)
  ·
    refine ⟨71202382926043947044275565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47468255284029298029517043 71202382926043947044275565)
    ·
      refine ⟨26700893597266480141603337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71202382926043947044275565 26700893597266480141603337)
      ·
        refine ⟨20025670197949860106202503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26700893597266480141603337 20025670197949860106202503)
        ·
          refine ⟨30038505296924790159303755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20025670197949860106202503 30038505296924790159303755)
          ·
            refine ⟨45057757945387185238955633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30038505296924790159303755 45057757945387185238955633)
            ·
              refine ⟨33793318459040388929216725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45057757945387185238955633 33793318459040388929216725)
              ·
                refine ⟨792030901383759115528517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33793318459040388929216725 792030901383759115528517)
                ·
                  refine ⟨148505794009454834161597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 792030901383759115528517 148505794009454834161597)
                  ·
                    rfl

theorem cell22_1301463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 7, 4].length) (baseStart_1301463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301463 prefixEnd_1301463 := by exact prefixLift 1301463
  have htrace : WordTrace (prefixWord ++ tailWord_1301463) baseStart_1301463 baseEnd_1301463 := by
    simpa [prefixWord, tailWord_1301463, baseEnd_1301463] using wordTrace_append hprefix tailTrace_1301463
  have hstable : (prefixWord ++ tailWord_1301463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301463).length < 2 ^ (prefixWord ++ tailWord_1301463).sum := by decide
  have hdescent : baseEnd_1301463 < baseStart_1301463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301476 : List Nat := [2, 3, 1, 1, 1, 1, 2, 2, 3, 6]
def baseStart_1301476 : Nat := 118140960795 + 1301476 * 2 ^ 59
def prefixEnd_1301476 : Nat := 4983230072969 + 3 ^ 40 * 1301476 * 2
def baseEnd_1301476 : Nat := 445521832194036801909751

theorem tailTrace_1301476 : CollatzResearch.WordTrace tailWord_1301476 prefixEnd_1301476 445521832194036801909751 := by
  unfold tailWord_1301476
  simp only [CollatzResearch.WordTrace]
  refine ⟨23734364716491100624870141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31645819621988134166493521 23734364716491100624870141)
  ·
    refine ⟨8900386768684162734326303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23734364716491100624870141 8900386768684162734326303)
    ·
      refine ⟨13350580153026244101489455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8900386768684162734326303 13350580153026244101489455)
      ·
        refine ⟨20025870229539366152234183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13350580153026244101489455 20025870229539366152234183)
        ·
          refine ⟨30038805344309049228351275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20025870229539366152234183 30038805344309049228351275)
          ·
            refine ⟨45058208016463573842526913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30038805344309049228351275 45058208016463573842526913)
            ·
              refine ⟨33793656012347680381895185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45058208016463573842526913 33793656012347680381895185)
              ·
                refine ⟨25345242009260760286421389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33793656012347680381895185 25345242009260760286421389)
                ·
                  refine ⟨9504465753472785107408021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25345242009260760286421389 9504465753472785107408021)
                  ·
                    refine ⟨445521832194036801909751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9504465753472785107408021 445521832194036801909751)
                    ·
                      rfl

theorem cell22_1301476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_1301476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301476 prefixEnd_1301476 := by exact prefixLift 1301476
  have htrace : WordTrace (prefixWord ++ tailWord_1301476) baseStart_1301476 baseEnd_1301476 := by
    simpa [prefixWord, tailWord_1301476, baseEnd_1301476] using wordTrace_append hprefix tailTrace_1301476
  have hstable : (prefixWord ++ tailWord_1301476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301476).length < 2 ^ (prefixWord ++ tailWord_1301476).sum := by decide
  have hdescent : baseEnd_1301476 < baseStart_1301476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301521 : List Nat := [1, 2, 2, 1, 1, 2, 1, 2, 4, 6]
def baseStart_1301521 : Nat := 118140960795 + 1301521 * 2 ^ 59
def prefixEnd_1301521 : Nat := 4983230072969 + 3 ^ 40 * 1301521 * 2
def baseEnd_1301521 : Nat := 445537236613671684534613

theorem tailTrace_1301521 : CollatzResearch.WordTrace tailWord_1301521 prefixEnd_1301521 445537236613671684534613 := by
  unfold tailWord_1301521
  simp only [CollatzResearch.WordTrace]
  refine ⟨47470370717819173935128417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31646913811879449290085611 47470370717819173935128417)
  ·
    refine ⟨35602778038364380451346313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47470370717819173935128417 35602778038364380451346313)
    ·
      refine ⟨26702083528773285338509735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35602778038364380451346313 26702083528773285338509735)
      ·
        refine ⟨40053125293159928007764603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26702083528773285338509735 40053125293159928007764603)
        ·
          refine ⟨60079687939739892011646905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40053125293159928007764603 60079687939739892011646905)
          ·
            refine ⟨45059765954804919008735179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60079687939739892011646905 45059765954804919008735179)
            ·
              refine ⟨67589648932207378513102769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45059765954804919008735179 67589648932207378513102769)
              ·
                refine ⟨50692236699155533884827077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67589648932207378513102769 50692236699155533884827077)
                ·
                  refine ⟨9504794381091662603405077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50692236699155533884827077 9504794381091662603405077)
                  ·
                    refine ⟨445537236613671684534613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9504794381091662603405077 445537236613671684534613)
                    ·
                      rfl

theorem cell22_1301521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_1301521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301521 prefixEnd_1301521 := by exact prefixLift 1301521
  have htrace : WordTrace (prefixWord ++ tailWord_1301521) baseStart_1301521 baseEnd_1301521 := by
    simpa [prefixWord, tailWord_1301521, baseEnd_1301521] using wordTrace_append hprefix tailTrace_1301521
  have hstable : (prefixWord ++ tailWord_1301521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301521).length < 2 ^ (prefixWord ++ tailWord_1301521).sum := by decide
  have hdescent : baseEnd_1301521 < baseStart_1301521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301538 : List Nat := [3, 3, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1301538 : Nat := 118140960795 + 1301538 * 2 ^ 59
def prefixEnd_1301538 : Nat := 4983230072969 + 3 ^ 40 * 1301538 * 2
def baseEnd_1301538 : Nat := 445543056061089306859561

theorem tailTrace_1301538 : CollatzResearch.WordTrace tailWord_1301538 prefixEnd_1301538 445543056061089306859561 := by
  unfold tailWord_1301538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11867747689689396459624317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31647327172505057225664845 11867747689689396459624317)
  ·
    refine ⟨4450405383633523672359119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11867747689689396459624317 4450405383633523672359119)
    ·
      refine ⟨6675608075450285508538679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4450405383633523672359119 6675608075450285508538679)
      ·
        refine ⟨10013412113175428262808019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6675608075450285508538679 10013412113175428262808019)
        ·
          refine ⟨15020118169763142394212029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10013412113175428262808019 15020118169763142394212029)
          ·
            refine ⟨5632544313661178397829511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15020118169763142394212029 5632544313661178397829511)
            ·
              refine ⟨8448816470491767596744267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5632544313661178397829511 8448816470491767596744267)
              ·
                refine ⟨12673224705737651395116401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8448816470491767596744267 12673224705737651395116401)
                ·
                  refine ⟨9504918529303238546337301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12673224705737651395116401 9504918529303238546337301)
                  ·
                    refine ⟨445543056061089306859561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9504918529303238546337301 445543056061089306859561)
                    ·
                      rfl

theorem cell22_1301538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1301538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301538 prefixEnd_1301538 := by exact prefixLift 1301538
  have htrace : WordTrace (prefixWord ++ tailWord_1301538) baseStart_1301538 baseEnd_1301538 := by
    simpa [prefixWord, tailWord_1301538, baseEnd_1301538] using wordTrace_append hprefix tailTrace_1301538
  have hstable : (prefixWord ++ tailWord_1301538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301538).length < 2 ^ (prefixWord ++ tailWord_1301538).sum := by decide
  have hdescent : baseEnd_1301538 < baseStart_1301538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301553 : List Nat := [1, 2, 2, 3, 1, 2, 1, 5, 5]
def baseStart_1301553 : Nat := 118140960795 + 1301553 * 2 ^ 59
def prefixEnd_1301553 : Nat := 4983230072969 + 3 ^ 40 * 1301553 * 2
def baseEnd_1301553 : Nat := 148516063622544755911505

theorem tailTrace_1301553 : CollatzResearch.WordTrace tailWord_1301553 prefixEnd_1301553 148516063622544755911505 := by
  unfold tailWord_1301553
  simp only [CollatzResearch.WordTrace]
  refine ⟨47471537853703243400293313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31647691902468828933528875 47471537853703243400293313)
  ·
    refine ⟨35603653390277432550219985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47471537853703243400293313 35603653390277432550219985)
    ·
      refine ⟨26702740042708074412664989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35603653390277432550219985 26702740042708074412664989)
      ·
        refine ⟨10013527516015527904749371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26702740042708074412664989 10013527516015527904749371)
        ·
          refine ⟨15020291274023291857124057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10013527516015527904749371 15020291274023291857124057)
          ·
            refine ⟨11265218455517468892843043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15020291274023291857124057 11265218455517468892843043)
            ·
              refine ⟨16897827683276203339264565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11265218455517468892843043 16897827683276203339264565)
              ·
                refine ⟨1584171345307144063056053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16897827683276203339264565 1584171345307144063056053)
                ·
                  refine ⟨148516063622544755911505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1584171345307144063056053 148516063622544755911505)
                  ·
                    rfl

theorem cell22_1301553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 5, 5].length) (baseStart_1301553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301553 prefixEnd_1301553 := by exact prefixLift 1301553
  have htrace : WordTrace (prefixWord ++ tailWord_1301553) baseStart_1301553 baseEnd_1301553 := by
    simpa [prefixWord, tailWord_1301553, baseEnd_1301553] using wordTrace_append hprefix tailTrace_1301553
  have hstable : (prefixWord ++ tailWord_1301553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301553).length < 2 ^ (prefixWord ++ tailWord_1301553).sum := by decide
  have hdescent : baseEnd_1301553 < baseStart_1301553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301628 : List Nat := [2, 2, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_1301628 : Nat := 118140960795 + 1301628 * 2 ^ 59
def prefixEnd_1301628 : Nat := 4983230072969 + 3 ^ 40 * 1301628 * 2
def baseEnd_1301628 : Nat := 445573864900359072109285

theorem tailTrace_1301628 : CollatzResearch.WordTrace tailWord_1301628 prefixEnd_1301628 445573864900359072109285 := by
  unfold tailWord_1301628
  simp only [CollatzResearch.WordTrace]
  refine ⟨23737136664215765604636769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31649515552287687472849025 23737136664215765604636769)
  ·
    refine ⟨17802852498161824203477577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23737136664215765604636769 17802852498161824203477577)
    ·
      refine ⟨13352139373621368152608183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17802852498161824203477577 13352139373621368152608183)
      ·
        refine ⟨20028209060432052228912275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13352139373621368152608183 20028209060432052228912275)
        ·
          refine ⟨30042313590648078343368413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20028209060432052228912275 30042313590648078343368413)
          ·
            refine ⟨11265867596493029378763155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30042313590648078343368413 11265867596493029378763155)
            ·
              refine ⟨16898801394739544068144733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11265867596493029378763155 16898801394739544068144733)
              ·
                refine ⟨6337050523027329025554275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16898801394739544068144733 6337050523027329025554275)
                ·
                  refine ⟨9505575784540993538331413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6337050523027329025554275 9505575784540993538331413)
                  ·
                    refine ⟨445573864900359072109285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9505575784540993538331413 445573864900359072109285)
                    ·
                      rfl

theorem cell22_1301628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_1301628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301628 prefixEnd_1301628 := by exact prefixLift 1301628
  have htrace : WordTrace (prefixWord ++ tailWord_1301628) baseStart_1301628 baseEnd_1301628 := by
    simpa [prefixWord, tailWord_1301628, baseEnd_1301628] using wordTrace_append hprefix tailTrace_1301628
  have hstable : (prefixWord ++ tailWord_1301628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301628).length < 2 ^ (prefixWord ++ tailWord_1301628).sum := by decide
  have hdescent : baseEnd_1301628 < baseStart_1301628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301660 : List Nat := [2, 2, 3, 2, 1, 3, 2, 7]
def baseStart_1301660 : Nat := 118140960795 + 1301660 * 2 ^ 59
def prefixEnd_1301660 : Nat := 4983230072969 + 3 ^ 40 * 1301660 * 2
def baseEnd_1301660 : Nat := 49509424350480183923243

theorem tailTrace_1301660 : CollatzResearch.WordTrace tailWord_1301660 prefixEnd_1301660 49509424350480183923243 := by
  unfold tailWord_1301660
  simp only [CollatzResearch.WordTrace]
  refine ⟨23737720232157800337219217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31650293642877067116292289 23737720232157800337219217)
  ·
    refine ⟨17803290174118350252914413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23737720232157800337219217 17803290174118350252914413)
    ·
      refine ⟨6676233815294381344842905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17803290174118350252914413 6676233815294381344842905)
      ·
        refine ⟨5007175361470786008632179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6676233815294381344842905 5007175361470786008632179)
        ·
          refine ⟨7510763042206179012948269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5007175361470786008632179 7510763042206179012948269)
          ·
            refine ⟨2816536140827317129855601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7510763042206179012948269 2816536140827317129855601)
            ·
              refine ⟨2112402105620487847391701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2816536140827317129855601 2112402105620487847391701)
              ·
                refine ⟨49509424350480183923243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2112402105620487847391701 49509424350480183923243)
                ·
                  rfl

theorem cell22_1301660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 7].length) (baseStart_1301660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301660 prefixEnd_1301660 := by exact prefixLift 1301660
  have htrace : WordTrace (prefixWord ++ tailWord_1301660) baseStart_1301660 baseEnd_1301660 := by
    simpa [prefixWord, tailWord_1301660, baseEnd_1301660] using wordTrace_append hprefix tailTrace_1301660
  have hstable : (prefixWord ++ tailWord_1301660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301660).length < 2 ^ (prefixWord ++ tailWord_1301660).sum := by decide
  have hdescent : baseEnd_1301660 < baseStart_1301660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301688 : List Nat := [2, 1, 2, 1, 2, 1, 2, 4, 7]
def baseStart_1301688 : Nat := 118140960795 + 1301688 * 2 ^ 59
def prefixEnd_1301688 : Nat := 4983230072969 + 3 ^ 40 * 1301688 * 2
def baseEnd_1301688 : Nat := 148531468042179638536367

theorem tailTrace_1301688 : CollatzResearch.WordTrace tailWord_1301688 prefixEnd_1301688 148531468042179638536367 := by
  unfold tailWord_1301688
  simp only [CollatzResearch.WordTrace]
  refine ⟨23738230854107080728228859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31650974472142774304305145 23738230854107080728228859)
  ·
    refine ⟨35607346281160621092343289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23738230854107080728228859 35607346281160621092343289)
    ·
      refine ⟨26705509710870465819257467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35607346281160621092343289 26705509710870465819257467)
      ·
        refine ⟨40058264566305698728886201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26705509710870465819257467 40058264566305698728886201)
        ·
          refine ⟨30043698424729274046664651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40058264566305698728886201 30043698424729274046664651)
          ·
            refine ⟨45065547637093911069996977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30043698424729274046664651 45065547637093911069996977)
            ·
              refine ⟨33799160727820433302497733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45065547637093911069996977 33799160727820433302497733)
              ·
                refine ⟨6337342636466331244218325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33799160727820433302497733 6337342636466331244218325)
                ·
                  refine ⟨148531468042179638536367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6337342636466331244218325 148531468042179638536367)
                  ·
                    rfl

theorem cell22_1301688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4, 7].length) (baseStart_1301688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301688 prefixEnd_1301688 := by exact prefixLift 1301688
  have htrace : WordTrace (prefixWord ++ tailWord_1301688) baseStart_1301688 baseEnd_1301688 := by
    simpa [prefixWord, tailWord_1301688, baseEnd_1301688] using wordTrace_append hprefix tailTrace_1301688
  have hstable : (prefixWord ++ tailWord_1301688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301688).length < 2 ^ (prefixWord ++ tailWord_1301688).sum := by decide
  have hdescent : baseEnd_1301688 < baseStart_1301688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301698 : List Nat := [3, 5, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_1301698 : Nat := 118140960795 + 1301698 * 2 ^ 59
def prefixEnd_1301698 : Nat := 4983230072969 + 3 ^ 40 * 1301698 * 2
def baseEnd_1301698 : Nat := 445597827330902222859071

theorem tailTrace_1301698 : CollatzResearch.WordTrace tailWord_1301698 prefixEnd_1301698 445597827330902222859071 := by
  unfold tailWord_1301698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11869206609544483291080437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31651217625451955442881165 11869206609544483291080437)
  ·
    refine ⟨1112738119644795308538791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11869206609544483291080437 1112738119644795308538791)
    ·
      refine ⟨1669107179467192962808187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1112738119644795308538791 1669107179467192962808187)
      ·
        refine ⟨2503660769200789444212281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1669107179467192962808187 2503660769200789444212281)
        ·
          refine ⟨1877745576900592083159211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2503660769200789444212281 1877745576900592083159211)
          ·
            refine ⟨2816618365350888124738817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1877745576900592083159211 2816618365350888124738817)
            ·
              refine ⟨2112463774013166093554113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2816618365350888124738817 2112463774013166093554113)
              ·
                refine ⟨1584347830509874570165585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2112463774013166093554113 1584347830509874570165585)
                ·
                  refine ⟨1188260872882405927624189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1584347830509874570165585 1188260872882405927624189)
                  ·
                    refine ⟨445597827330902222859071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1188260872882405927624189 445597827330902222859071)
                    ·
                      rfl

theorem cell22_1301698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_1301698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301698 prefixEnd_1301698 := by exact prefixLift 1301698
  have htrace : WordTrace (prefixWord ++ tailWord_1301698) baseStart_1301698 baseEnd_1301698 := by
    simpa [prefixWord, tailWord_1301698, baseEnd_1301698] using wordTrace_append hprefix tailTrace_1301698
  have hstable : (prefixWord ++ tailWord_1301698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301698).length < 2 ^ (prefixWord ++ tailWord_1301698).sum := by decide
  have hdescent : baseEnd_1301698 < baseStart_1301698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301703 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 3, 7]
def baseStart_1301703 : Nat := 118140960795 + 1301703 * 2 ^ 59
def prefixEnd_1301703 : Nat := 4983230072969 + 3 ^ 40 * 1301703 * 2
def baseEnd_1301703 : Nat := 445599538933083876484055

theorem tailTrace_1301703 : CollatzResearch.WordTrace tailWord_1301703 prefixEnd_1301703 445599538933083876484055 := by
  unfold tailWord_1301703
  simp only [CollatzResearch.WordTrace]
  refine ⟨47477008803159819018253763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31651339202106546012169175 47477008803159819018253763)
  ·
    refine ⟨71215513204739728527380645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47477008803159819018253763 71215513204739728527380645)
    ·
      refine ⟨13352908725888699098883871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71215513204739728527380645 13352908725888699098883871)
      ·
        refine ⟨20029363088833048648325807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13352908725888699098883871 20029363088833048648325807)
        ·
          refine ⟨30044044633249572972488711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20029363088833048648325807 30044044633249572972488711)
          ·
            refine ⟨45066066949874359458733067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30044044633249572972488711 45066066949874359458733067)
            ·
              refine ⟨67599100424811539188099601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45066066949874359458733067 67599100424811539188099601)
              ·
                refine ⟨50699325318608654391074701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67599100424811539188099601 50699325318608654391074701)
                ·
                  refine ⟨19012246994478245396653013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 50699325318608654391074701 19012246994478245396653013)
                  ·
                    refine ⟨445599538933083876484055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 19012246994478245396653013 445599538933083876484055)
                    ·
                      rfl

theorem cell22_1301703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 3, 7].length) (baseStart_1301703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301703 prefixEnd_1301703 := by exact prefixLift 1301703
  have htrace : WordTrace (prefixWord ++ tailWord_1301703) baseStart_1301703 baseEnd_1301703 := by
    simpa [prefixWord, tailWord_1301703, baseEnd_1301703] using wordTrace_append hprefix tailTrace_1301703
  have hstable : (prefixWord ++ tailWord_1301703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301703).length < 2 ^ (prefixWord ++ tailWord_1301703).sum := by decide
  have hdescent : baseEnd_1301703 < baseStart_1301703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301750 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_1301750 : Nat := 118140960795 + 1301750 * 2 ^ 59
def prefixEnd_1301750 : Nat := 4983230072969 + 3 ^ 40 * 1301750 * 2
def baseEnd_1301750 : Nat := 148538542664530473519637

theorem tailTrace_1301750 : CollatzResearch.WordTrace tailWord_1301750 prefixEnd_1301750 148538542664530473519637 := by
  unfold tailWord_1301750
  simp only [CollatzResearch.WordTrace]
  refine ⟨2967420189624346627825919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31652482022659697363476469 2967420189624346627825919)
  ·
    refine ⟨4451130284436519941738879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2967420189624346627825919 4451130284436519941738879)
    ·
      refine ⟨6676695426654779912608319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4451130284436519941738879 6676695426654779912608319)
      ·
        refine ⟨10015043139982169868912479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6676695426654779912608319 10015043139982169868912479)
        ·
          refine ⟨15022564709973254803368719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10015043139982169868912479 15022564709973254803368719)
          ·
            refine ⟨22533847064959882205053079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15022564709973254803368719 22533847064959882205053079)
            ·
              refine ⟨33800770597439823307579619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22533847064959882205053079 33800770597439823307579619)
              ·
                refine ⟨50701155896159734961369429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33800770597439823307579619 50701155896159734961369429)
                ·
                  refine ⟨148538542664530473519637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 50701155896159734961369429 148538542664530473519637)
                  ·
                    rfl

theorem cell22_1301750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_1301750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301750 prefixEnd_1301750 := by exact prefixLift 1301750
  have htrace : WordTrace (prefixWord ++ tailWord_1301750) baseStart_1301750 baseEnd_1301750 := by
    simpa [prefixWord, tailWord_1301750, baseEnd_1301750] using wordTrace_append hprefix tailTrace_1301750
  have hstable : (prefixWord ++ tailWord_1301750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301750).length < 2 ^ (prefixWord ++ tailWord_1301750).sum := by decide
  have hdescent : baseEnd_1301750 < baseStart_1301750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301795 : List Nat := [1, 1, 1, 4, 2, 4, 1, 8]
def baseStart_1301795 : Nat := 118140960795 + 1301795 * 2 ^ 59
def prefixEnd_1301795 : Nat := 4983230072969 + 3 ^ 40 * 1301795 * 2
def baseEnd_1301795 : Nat := 49514559157025144798197

theorem tailTrace_1301795 : CollatzResearch.WordTrace tailWord_1301795 prefixEnd_1301795 49514559157025144798197 := by
  unfold tailWord_1301795
  simp only [CollatzResearch.WordTrace]
  refine ⟨47480364318826518730602839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31653576212551012487068559 47480364318826518730602839)
  ·
    refine ⟨71220546478239778095904259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47480364318826518730602839 71220546478239778095904259)
    ·
      refine ⟨106830819717359667143856389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71220546478239778095904259 106830819717359667143856389)
      ·
        refine ⟨20030778697004937589473073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 106830819717359667143856389 20030778697004937589473073)
        ·
          refine ⟨15023084022753703192104805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20030778697004937589473073 15023084022753703192104805)
          ·
            refine ⟨2816828254266319348519651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15023084022753703192104805 2816828254266319348519651)
            ·
              refine ⟨4225242381399479022779477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2816828254266319348519651 4225242381399479022779477)
              ·
                refine ⟨49514559157025144798197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4225242381399479022779477 49514559157025144798197)
                ·
                  rfl

theorem cell22_1301795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 8].length) (baseStart_1301795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301795 prefixEnd_1301795 := by exact prefixLift 1301795
  have htrace : WordTrace (prefixWord ++ tailWord_1301795) baseStart_1301795 baseEnd_1301795 := by
    simpa [prefixWord, tailWord_1301795, baseEnd_1301795] using wordTrace_append hprefix tailTrace_1301795
  have hstable : (prefixWord ++ tailWord_1301795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301795).length < 2 ^ (prefixWord ++ tailWord_1301795).sum := by decide
  have hdescent : baseEnd_1301795 < baseStart_1301795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301855 : List Nat := [1, 1, 2, 3, 1, 2, 1, 2, 4, 5]
def baseStart_1301855 : Nat := 118140960795 + 1301855 * 2 ^ 59
def prefixEnd_1301855 : Nat := 4983230072969 + 3 ^ 40 * 1301855 * 2
def baseEnd_1301855 : Nat := 445651571639406146683589

theorem tailTrace_1301855 : CollatzResearch.WordTrace tailWord_1301855 prefixEnd_1301855 445651571639406146683589 := by
  unfold tailWord_1301855
  simp only [CollatzResearch.WordTrace]
  refine ⟨47482552698609148977787019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31655035132406099318524679 47482552698609148977787019)
  ·
    refine ⟨71223829047913723466680529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47482552698609148977787019 71223829047913723466680529)
    ·
      refine ⟨53417871785935292600010397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71223829047913723466680529 53417871785935292600010397)
      ·
        refine ⟨20031701919725734725003899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53417871785935292600010397 20031701919725734725003899)
        ·
          refine ⟨30047552879588602087505849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20031701919725734725003899 30047552879588602087505849)
          ·
            refine ⟨22535664659691451565629387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30047552879588602087505849 22535664659691451565629387)
            ·
              refine ⟨33803496989537177348444081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22535664659691451565629387 33803496989537177348444081)
              ·
                refine ⟨25352622742152883011333061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33803496989537177348444081 25352622742152883011333061)
                ·
                  refine ⟨4753616764153665564624949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25352622742152883011333061 4753616764153665564624949)
                  ·
                    refine ⟨445651571639406146683589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4753616764153665564624949 445651571639406146683589)
                    ·
                      rfl

theorem cell22_1301855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 2, 4, 5].length) (baseStart_1301855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301855 prefixEnd_1301855 := by exact prefixLift 1301855
  have htrace : WordTrace (prefixWord ++ tailWord_1301855) baseStart_1301855 baseEnd_1301855 := by
    simpa [prefixWord, tailWord_1301855, baseEnd_1301855] using wordTrace_append hprefix tailTrace_1301855
  have hstable : (prefixWord ++ tailWord_1301855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301855).length < 2 ^ (prefixWord ++ tailWord_1301855).sum := by decide
  have hdescent : baseEnd_1301855 < baseStart_1301855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301889 : List Nat := [1, 2, 4, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1301889 : Nat := 118140960795 + 1301889 * 2 ^ 59
def prefixEnd_1301889 : Nat := 4983230072969 + 3 ^ 40 * 1301889 * 2
def baseEnd_1301889 : Nat := 445663210534241391333485

theorem tailTrace_1301889 : CollatzResearch.WordTrace tailWord_1301889 prefixEnd_1301889 445663210534241391333485 := by
  unfold tailWord_1301889
  simp only [CollatzResearch.WordTrace]
  refine ⟨47483792780485972784524721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31655861853657315189683147 47483792780485972784524721)
  ·
    refine ⟨35612844585364479588393541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47483792780485972784524721 35612844585364479588393541)
    ·
      refine ⟨6677408359755839922823789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35612844585364479588393541 6677408359755839922823789)
      ·
        refine ⟨2504028134908439971058921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6677408359755839922823789 2504028134908439971058921)
        ·
          refine ⟨1878021101181329978294191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2504028134908439971058921 1878021101181329978294191)
          ·
            refine ⟨2817031651771994967441287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1878021101181329978294191 2817031651771994967441287)
            ·
              refine ⟨4225547477657992451161931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2817031651771994967441287 4225547477657992451161931)
              ·
                refine ⟨6338321216486988676742897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4225547477657992451161931 6338321216486988676742897)
                ·
                  refine ⟨4753740912365241507557173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6338321216486988676742897 4753740912365241507557173)
                  ·
                    refine ⟨445663210534241391333485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4753740912365241507557173 445663210534241391333485)
                    ·
                      rfl

theorem cell22_1301889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1301889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301889 prefixEnd_1301889 := by exact prefixLift 1301889
  have htrace : WordTrace (prefixWord ++ tailWord_1301889) baseStart_1301889 baseEnd_1301889 := by
    simpa [prefixWord, tailWord_1301889, baseEnd_1301889] using wordTrace_append hprefix tailTrace_1301889
  have hstable : (prefixWord ++ tailWord_1301889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301889).length < 2 ^ (prefixWord ++ tailWord_1301889).sum := by decide
  have hdescent : baseEnd_1301889 < baseStart_1301889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301915 : List Nat := [1, 1, 1, 1, 1, 1, 2, 1, 7, 6]
def baseStart_1301915 : Nat := 118140960795 + 1301915 * 2 ^ 59
def prefixEnd_1301915 : Nat := 4983230072969 + 3 ^ 40 * 1301915 * 2
def baseEnd_1301915 : Nat := 445672110865585990183405

theorem tailTrace_1301915 : CollatzResearch.WordTrace tailWord_1301915 prefixEnd_1301915 445672110865585990183405 := by
  unfold tailWord_1301915
  simp only [CollatzResearch.WordTrace]
  refine ⟨47484741078391779224971199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31656494052261186149980799 47484741078391779224971199)
  ·
    refine ⟨71227111617587668837456799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47484741078391779224971199 71227111617587668837456799)
    ·
      refine ⟨106840667426381503256185199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71227111617587668837456799 106840667426381503256185199)
      ·
        refine ⟨160261001139572254884277799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106840667426381503256185199 160261001139572254884277799)
        ·
          refine ⟨240391501709358382326416699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160261001139572254884277799 240391501709358382326416699)
          ·
            refine ⟨360587252564037573489625049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240391501709358382326416699 360587252564037573489625049)
            ·
              refine ⟨270440439423028180117218787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 360587252564037573489625049 270440439423028180117218787)
              ·
                refine ⟨405660659134542270175828181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270440439423028180117218787 405660659134542270175828181)
                ·
                  refine ⟨9507671698465834457245973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 405660659134542270175828181 9507671698465834457245973)
                  ·
                    refine ⟨445672110865585990183405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9507671698465834457245973 445672110865585990183405)
                    ·
                      rfl

theorem cell22_1301915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 7, 6].length) (baseStart_1301915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301915 prefixEnd_1301915 := by exact prefixLift 1301915
  have htrace : WordTrace (prefixWord ++ tailWord_1301915) baseStart_1301915 baseEnd_1301915 := by
    simpa [prefixWord, tailWord_1301915, baseEnd_1301915] using wordTrace_append hprefix tailTrace_1301915
  have hstable : (prefixWord ++ tailWord_1301915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301915).length < 2 ^ (prefixWord ++ tailWord_1301915).sum := by decide
  have hdescent : baseEnd_1301915 < baseStart_1301915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301919 : List Nat := [1, 1, 2, 5, 1, 2, 1, 5, 4]
def baseStart_1301919 : Nat := 118140960795 + 1301919 * 2 ^ 59
def prefixEnd_1301919 : Nat := 4983230072969 + 3 ^ 40 * 1301919 * 2
def baseEnd_1301919 : Nat := 148557826715777104361131

theorem tailTrace_1301919 : CollatzResearch.WordTrace tailWord_1301919 prefixEnd_1301919 148557826715777104361131 := by
  unfold tailWord_1301919
  simp only [CollatzResearch.WordTrace]
  refine ⟨47484886970377287908116811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31656591313584858605411207 47484886970377287908116811)
  ·
    refine ⟨71227330455565931862175217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47484886970377287908116811 71227330455565931862175217)
    ·
      refine ⟨53420497841674448896631413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71227330455565931862175217 53420497841674448896631413)
      ·
        refine ⟨5008171672656979584059195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53420497841674448896631413 5008171672656979584059195)
        ·
          refine ⟨7512257508985469376088793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5008171672656979584059195 7512257508985469376088793)
          ·
            refine ⟨5634193131739102032066595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7512257508985469376088793 5634193131739102032066595)
            ·
              refine ⟨8451289697608653048099893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5634193131739102032066595 8451289697608653048099893)
              ·
                refine ⟨792308409150811223259365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8451289697608653048099893 792308409150811223259365)
                ·
                  refine ⟨148557826715777104361131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 792308409150811223259365 148557826715777104361131)
                  ·
                    rfl

theorem cell22_1301919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 5, 4].length) (baseStart_1301919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301919 prefixEnd_1301919 := by exact prefixLift 1301919
  have htrace : WordTrace (prefixWord ++ tailWord_1301919) baseStart_1301919 baseEnd_1301919 := by
    simpa [prefixWord, tailWord_1301919, baseEnd_1301919] using wordTrace_append hprefix tailTrace_1301919
  have hstable : (prefixWord ++ tailWord_1301919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301919).length < 2 ^ (prefixWord ++ tailWord_1301919).sum := by decide
  have hdescent : baseEnd_1301919 < baseStart_1301919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301932 : List Nat := [2, 2, 1, 1, 1, 1, 4, 4, 2, 4]
def baseStart_1301932 : Nat := 118140960795 + 1301932 * 2 ^ 59
def prefixEnd_1301932 : Nat := 4983230072969 + 3 ^ 40 * 1301932 * 2
def baseEnd_1301932 : Nat := 445677930313003612508353

theorem tailTrace_1301932 : CollatzResearch.WordTrace tailWord_1301932 prefixEnd_1301932 445677930313003612508353 := by
  unfold tailWord_1301932
  simp only [CollatzResearch.WordTrace]
  refine ⟨23742680559665095564170025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31656907412886794085560033 23742680559665095564170025)
  ·
    refine ⟨17807010419748821673127519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23742680559665095564170025 17807010419748821673127519)
    ·
      refine ⟨26710515629623232509691279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17807010419748821673127519 26710515629623232509691279)
      ·
        refine ⟨40065773444434848764536919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26710515629623232509691279 40065773444434848764536919)
        ·
          refine ⟨60098660166652273146805379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40065773444434848764536919 60098660166652273146805379)
          ·
            refine ⟨90147990249978409720208069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60098660166652273146805379 90147990249978409720208069)
            ·
              refine ⟨16902748171870951822539013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90147990249978409720208069 16902748171870951822539013)
              ·
                refine ⟨3169265282225803466726065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16902748171870951822539013 3169265282225803466726065)
                ·
                  refine ⟨2376948961669352600044549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3169265282225803466726065 2376948961669352600044549)
                  ·
                    refine ⟨445677930313003612508353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2376948961669352600044549 445677930313003612508353)
                    ·
                      rfl

theorem cell22_1301932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 4].length) (baseStart_1301932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301932 prefixEnd_1301932 := by exact prefixLift 1301932
  have htrace : WordTrace (prefixWord ++ tailWord_1301932) baseStart_1301932 baseEnd_1301932 := by
    simpa [prefixWord, tailWord_1301932, baseEnd_1301932] using wordTrace_append hprefix tailTrace_1301932
  have hstable : (prefixWord ++ tailWord_1301932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301932).length < 2 ^ (prefixWord ++ tailWord_1301932).sum := by decide
  have hdescent : baseEnd_1301932 < baseStart_1301932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301964 : List Nat := [2, 2, 1, 4, 2, 1, 4, 6]
def baseStart_1301964 : Nat := 118140960795 + 1301964 * 2 ^ 59
def prefixEnd_1301964 : Nat := 4983230072969 + 3 ^ 40 * 1301964 * 2
def baseEnd_1301964 : Nat := 49520987174107355078695

theorem tailTrace_1301964 : CollatzResearch.WordTrace tailWord_1301964 prefixEnd_1301964 49520987174107355078695 := by
  unfold tailWord_1301964
  simp only [CollatzResearch.WordTrace]
  refine ⟨23743264127607130296752473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31657685503476173729003297 23743264127607130296752473)
  ·
    refine ⟨17807448095705347722564355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23743264127607130296752473 17807448095705347722564355)
    ·
      refine ⟨26711172143558021583846533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17807448095705347722564355 26711172143558021583846533)
      ·
        refine ⟨5008344776917129046971225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26711172143558021583846533 5008344776917129046971225)
        ·
          refine ⟨3756258582687846785228419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5008344776917129046971225 3756258582687846785228419)
          ·
            refine ⟨5634387874031770177842629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3756258582687846785228419 5634387874031770177842629)
            ·
              refine ⟨1056447726380956908345493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5634387874031770177842629 1056447726380956908345493)
              ·
                refine ⟨49520987174107355078695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1056447726380956908345493 49520987174107355078695)
                ·
                  rfl

theorem cell22_1301964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 6].length) (baseStart_1301964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301964 prefixEnd_1301964 := by exact prefixLift 1301964
  have htrace : WordTrace (prefixWord ++ tailWord_1301964) baseStart_1301964 baseEnd_1301964 := by
    simpa [prefixWord, tailWord_1301964, baseEnd_1301964] using wordTrace_append hprefix tailTrace_1301964
  have hstable : (prefixWord ++ tailWord_1301964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301964).length < 2 ^ (prefixWord ++ tailWord_1301964).sum := by decide
  have hdescent : baseEnd_1301964 < baseStart_1301964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1301992 : List Nat := [2, 1, 4, 1, 1, 2, 1, 3, 7]
def baseStart_1301992 : Nat := 118140960795 + 1301992 * 2 ^ 59
def prefixEnd_1301992 : Nat := 4983230072969 + 3 ^ 40 * 1301992 * 2
def baseEnd_1301992 : Nat := 148566156513061152002723

theorem tailTrace_1301992 : CollatzResearch.WordTrace tailWord_1301992 prefixEnd_1301992 148566156513061152002723 := by
  unfold tailWord_1301992
  simp only [CollatzResearch.WordTrace]
  refine ⟨23743774749556410687762115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31658366332741880917016153 23743774749556410687762115)
  ·
    refine ⟨35615662124334616031643173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23743774749556410687762115 35615662124334616031643173)
    ·
      refine ⟨6677936648312740505933095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35615662124334616031643173 6677936648312740505933095)
      ·
        refine ⟨10016904972469110758899643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6677936648312740505933095 10016904972469110758899643)
        ·
          refine ⟨15025357458703666138349465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10016904972469110758899643 15025357458703666138349465)
          ·
            refine ⟨11269018094027749603762099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15025357458703666138349465 11269018094027749603762099)
            ·
              refine ⟨16903527141041624405643149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11269018094027749603762099 16903527141041624405643149)
              ·
                refine ⟨6338822677890609152116181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16903527141041624405643149 6338822677890609152116181)
                ·
                  refine ⟨148566156513061152002723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6338822677890609152116181 148566156513061152002723)
                  ·
                    rfl

theorem cell22_1301992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 3, 7].length) (baseStart_1301992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1301992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1301992 prefixEnd_1301992 := by exact prefixLift 1301992
  have htrace : WordTrace (prefixWord ++ tailWord_1301992) baseStart_1301992 baseEnd_1301992 := by
    simpa [prefixWord, tailWord_1301992, baseEnd_1301992] using wordTrace_append hprefix tailTrace_1301992
  have hstable : (prefixWord ++ tailWord_1301992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1301992).length < 2 ^ (prefixWord ++ tailWord_1301992).sum := by decide
  have hdescent : baseEnd_1301992 < baseStart_1301992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1301992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302069 : List Nat := [1, 3, 3, 1, 1, 3, 1, 3, 1, 5]
def baseStart_1302069 : Nat := 118140960795 + 1302069 * 2 ^ 59
def prefixEnd_1302069 : Nat := 4983230072969 + 3 ^ 40 * 1302069 * 2
def baseEnd_1302069 : Nat := 445724828212780921832933

theorem tailTrace_1302069 : CollatzResearch.WordTrace tailWord_1302069 prefixEnd_1302069 445724828212780921832933 := by
  unfold tailWord_1302069
  simp only [CollatzResearch.WordTrace]
  refine ⟨47490357919833863526077261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31660238613222575684051507 47490357919833863526077261)
  ·
    refine ⟨17808884219937698822278973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47490357919833863526077261 17808884219937698822278973)
    ·
      refine ⟨6678331582476637058354615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17808884219937698822278973 6678331582476637058354615)
      ·
        refine ⟨10017497373714955587531923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6678331582476637058354615 10017497373714955587531923)
        ·
          refine ⟨15026246060572433381297885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10017497373714955587531923 15026246060572433381297885)
          ·
            refine ⟨5634842272714662517986707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15026246060572433381297885 5634842272714662517986707)
            ·
              refine ⟨8452263409071993776980061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5634842272714662517986707 8452263409071993776980061)
              ·
                refine ⟨3169598778401997666367523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8452263409071993776980061 3169598778401997666367523)
                ·
                  refine ⟨4754398167602996499551285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3169598778401997666367523 4754398167602996499551285)
                  ·
                    refine ⟨445724828212780921832933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4754398167602996499551285 445724828212780921832933)
                    ·
                      rfl

theorem cell22_1302069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 3, 1, 5].length) (baseStart_1302069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302069 prefixEnd_1302069 := by exact prefixLift 1302069
  have htrace : WordTrace (prefixWord ++ tailWord_1302069) baseStart_1302069 baseEnd_1302069 := by
    simpa [prefixWord, tailWord_1302069, baseEnd_1302069] using wordTrace_append hprefix tailTrace_1302069
  have hstable : (prefixWord ++ tailWord_1302069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302069).length < 2 ^ (prefixWord ++ tailWord_1302069).sum := by decide
  have hdescent : baseEnd_1302069 < baseStart_1302069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302103 : List Nat := [1, 1, 3, 2, 2, 5, 1, 2, 2, 3]
def baseStart_1302103 : Nat := 118140960795 + 1302103 * 2 ^ 59
def prefixEnd_1302103 : Nat := 4983230072969 + 3 ^ 40 * 1302103 * 2
def baseEnd_1302103 : Nat := 445736467107616166482829

theorem tailTrace_1302103 : CollatzResearch.WordTrace tailWord_1302103 prefixEnd_1302103 445736467107616166482829 := by
  unfold tailWord_1302103
  simp only [CollatzResearch.WordTrace]
  refine ⟨47491598001710687332814963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31661065334473791555209975 47491598001710687332814963)
  ·
    refine ⟨71237397002566030999222445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47491598001710687332814963 71237397002566030999222445)
    ·
      refine ⟨26714023875962261624708417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71237397002566030999222445 26714023875962261624708417)
      ·
        refine ⟨20035517906971696218531313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26714023875962261624708417 20035517906971696218531313)
        ·
          refine ⟨15026638430228772163898485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20035517906971696218531313 15026638430228772163898485)
          ·
            refine ⟨1408747352833947390365483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15026638430228772163898485 1408747352833947390365483)
            ·
              refine ⟨2113121029250921085548225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1408747352833947390365483 2113121029250921085548225)
              ·
                refine ⟨1584840771938190814161169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2113121029250921085548225 1584840771938190814161169)
                ·
                  refine ⟨1188630578953643110620877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1584840771938190814161169 1188630578953643110620877)
                  ·
                    refine ⟨445736467107616166482829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1188630578953643110620877 445736467107616166482829)
                    ·
                      rfl

theorem cell22_1302103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 2, 2, 3].length) (baseStart_1302103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302103 prefixEnd_1302103 := by exact prefixLift 1302103
  have htrace : WordTrace (prefixWord ++ tailWord_1302103) baseStart_1302103 baseEnd_1302103 := by
    simpa [prefixWord, tailWord_1302103, baseEnd_1302103] using wordTrace_append hprefix tailTrace_1302103
  have hstable : (prefixWord ++ tailWord_1302103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302103).length < 2 ^ (prefixWord ++ tailWord_1302103).sum := by decide
  have hdescent : baseEnd_1302103 < baseStart_1302103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302120 : List Nat := [2, 1, 4, 3, 1, 2, 3, 1, 2, 3]
def baseStart_1302120 : Nat := 118140960795 + 1302120 * 2 ^ 59
def prefixEnd_1302120 : Nat := 4983230072969 + 3 ^ 40 * 1302120 * 2
def baseEnd_1302120 : Nat := 445742286555033788807777

theorem tailTrace_1302120 : CollatzResearch.WordTrace tailWord_1302120 prefixEnd_1302120 445742286555033788807777 := by
  unfold tailWord_1302120
  simp only [CollatzResearch.WordTrace]
  refine ⟨23746109021324549618091907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31661478695099399490789209 23746109021324549618091907)
  ·
    refine ⟨35619163531986824427137861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23746109021324549618091907 35619163531986824427137861)
    ·
      refine ⟨6678593162247529580088349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35619163531986824427137861 6678593162247529580088349)
      ·
        refine ⟨2504472435842823592533131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6678593162247529580088349 2504472435842823592533131)
        ·
          refine ⟨3756708653764235388799697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504472435842823592533131 3756708653764235388799697)
          ·
            refine ⟨2817531490323176541599773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3756708653764235388799697 2817531490323176541599773)
            ·
              refine ⟨1056574308871191203099915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2817531490323176541599773 1056574308871191203099915)
              ·
                refine ⟨1584861463306786804649873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056574308871191203099915 1584861463306786804649873)
                ·
                  refine ⟨1188646097480090103487405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1584861463306786804649873 1188646097480090103487405)
                  ·
                    refine ⟨445742286555033788807777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1188646097480090103487405 445742286555033788807777)
                    ·
                      rfl

theorem cell22_1302120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 1, 2, 3].length) (baseStart_1302120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302120 prefixEnd_1302120 := by exact prefixLift 1302120
  have htrace : WordTrace (prefixWord ++ tailWord_1302120) baseStart_1302120 baseEnd_1302120 := by
    simpa [prefixWord, tailWord_1302120, baseEnd_1302120] using wordTrace_append hprefix tailTrace_1302120
  have hstable : (prefixWord ++ tailWord_1302120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302120).length < 2 ^ (prefixWord ++ tailWord_1302120).sum := by decide
  have hdescent : baseEnd_1302120 < baseStart_1302120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302133 : List Nat := [1, 3, 4, 2, 1, 3, 2, 6]
def baseStart_1302133 : Nat := 118140960795 + 1302133 * 2 ^ 59
def prefixEnd_1302133 : Nat := 4983230072969 + 3 ^ 40 * 1302133 * 2
def baseEnd_1302133 : Nat := 49527415191189565359193

theorem tailTrace_1302133 : CollatzResearch.WordTrace tailWord_1302133 prefixEnd_1302133 49527415191189565359193 := by
  unfold tailWord_1302133
  simp only [CollatzResearch.WordTrace]
  refine ⟨47492692191602002456407053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31661794794401334970938035 47492692191602002456407053)
  ·
    refine ⟨17809759571850750921152645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47492692191602002456407053 17809759571850750921152645)
    ·
      refine ⟨3339329919722015797716121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17809759571850750921152645 3339329919722015797716121)
      ·
        refine ⟨2504497439791511848287091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3339329919722015797716121 2504497439791511848287091)
        ·
          refine ⟨3756746159687267772430637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2504497439791511848287091 3756746159687267772430637)
          ·
            refine ⟨1408779809882725414661489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3756746159687267772430637 1408779809882725414661489)
            ·
              refine ⟨1056584857412044060996117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1408779809882725414661489 1056584857412044060996117)
              ·
                refine ⟨49527415191189565359193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1056584857412044060996117 49527415191189565359193)
                ·
                  rfl

theorem cell22_1302133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 6].length) (baseStart_1302133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302133 prefixEnd_1302133 := by exact prefixLift 1302133
  have htrace : WordTrace (prefixWord ++ tailWord_1302133) baseStart_1302133 baseEnd_1302133 := by
    simpa [prefixWord, tailWord_1302133, baseEnd_1302133] using wordTrace_append hprefix tailTrace_1302133
  have hstable : (prefixWord ++ tailWord_1302133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302133).length < 2 ^ (prefixWord ++ tailWord_1302133).sum := by decide
  have hdescent : baseEnd_1302133 < baseStart_1302133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302208 : List Nat := [2, 1, 1, 2, 4, 1, 5, 1, 1, 4]
def baseStart_1302208 : Nat := 118140960795 + 1302208 * 2 ^ 59
def prefixEnd_1302208 : Nat := 4983230072969 + 3 ^ 40 * 1302208 * 2
def baseEnd_1302208 : Nat := 445772410753430892607507

theorem tailTrace_1302208 : CollatzResearch.WordTrace tailWord_1302208 prefixEnd_1302208 445772410753430892607507 := by
  unfold tailWord_1302208
  simp only [CollatzResearch.WordTrace]
  refine ⟨23747713833165145132693639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31663618444220193510258185 23747713833165145132693639)
  ·
    refine ⟨35621570749747717699040459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23747713833165145132693639 35621570749747717699040459)
    ·
      refine ⟨53432356124621576548560689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35621570749747717699040459 53432356124621576548560689)
      ·
        refine ⟨40074267093466182411420517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53432356124621576548560689 40074267093466182411420517)
        ·
          refine ⟨7513925080024909202141347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40074267093466182411420517 7513925080024909202141347)
          ·
            refine ⟨11270887620037363803212021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7513925080024909202141347 11270887620037363803212021)
            ·
              refine ⟨1056645714378502856551127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11270887620037363803212021 1056645714378502856551127)
              ·
                refine ⟨1584968571567754284826691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056645714378502856551127 1584968571567754284826691)
                ·
                  refine ⟨2377452857351631427240037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1584968571567754284826691 2377452857351631427240037)
                  ·
                    refine ⟨445772410753430892607507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2377452857351631427240037 445772410753430892607507)
                    ·
                      rfl

theorem cell22_1302208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 5, 1, 1, 4].length) (baseStart_1302208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302208 prefixEnd_1302208 := by exact prefixLift 1302208
  have htrace : WordTrace (prefixWord ++ tailWord_1302208) baseStart_1302208 baseEnd_1302208 := by
    simpa [prefixWord, tailWord_1302208, baseEnd_1302208] using wordTrace_append hprefix tailTrace_1302208
  have hstable : (prefixWord ++ tailWord_1302208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302208).length < 2 ^ (prefixWord ++ tailWord_1302208).sum := by decide
  have hdescent : baseEnd_1302208 < baseStart_1302208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302253 : List Nat := [1, 5, 1, 2, 1, 2, 3, 1, 2, 4]
def baseStart_1302253 : Nat := 118140960795 + 1302253 * 2 ^ 59
def prefixEnd_1302253 : Nat := 4983230072969 + 3 ^ 40 * 1302253 * 2
def baseEnd_1302253 : Nat := 445787815173065775232369

theorem tailTrace_1302253 : CollatzResearch.WordTrace tailWord_1302253 prefixEnd_1302253 445787815173065775232369 := by
  unfold tailWord_1302253
  simp only [CollatzResearch.WordTrace]
  refine ⟨47497068951167262950775413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31664712634111508633850275 47497068951167262950775413)
  ·
    refine ⟨4452850214171930901635195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47497068951167262950775413 4452850214171930901635195)
    ·
      refine ⟨6679275321257896352452793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4452850214171930901635195 6679275321257896352452793)
      ·
        refine ⟨5009456490943422264339595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6679275321257896352452793 5009456490943422264339595)
        ·
          refine ⟨7514184736415133396509393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5009456490943422264339595 7514184736415133396509393)
          ·
            refine ⟨5635638552311350047382045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7514184736415133396509393 5635638552311350047382045)
            ·
              refine ⟨2113364457116756267768267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5635638552311350047382045 2113364457116756267768267)
              ·
                refine ⟨3170046685675134401652401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113364457116756267768267 3170046685675134401652401)
                ·
                  refine ⟨2377535014256350801239301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3170046685675134401652401 2377535014256350801239301)
                  ·
                    refine ⟨445787815173065775232369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2377535014256350801239301 445787815173065775232369)
                    ·
                      rfl

theorem cell22_1302253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_1302253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302253 prefixEnd_1302253 := by exact prefixLift 1302253
  have htrace : WordTrace (prefixWord ++ tailWord_1302253) baseStart_1302253 baseEnd_1302253 := by
    simpa [prefixWord, tailWord_1302253, baseEnd_1302253] using wordTrace_append hprefix tailTrace_1302253
  have hstable : (prefixWord ++ tailWord_1302253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302253).length < 2 ^ (prefixWord ++ tailWord_1302253).sum := by decide
  have hdescent : baseEnd_1302253 < baseStart_1302253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302264 : List Nat := [2, 1, 2, 1, 1, 2, 2, 2, 1, 8]
def baseStart_1302264 : Nat := 118140960795 + 1302264 * 2 ^ 59
def prefixEnd_1302264 : Nat := 4983230072969 + 3 ^ 40 * 1302264 * 2
def baseEnd_1302264 : Nat := 445791580697865413207335

theorem tailTrace_1302264 : CollatzResearch.WordTrace tailWord_1302264 prefixEnd_1302264 445791580697865413207335 := by
  unfold tailWord_1302264
  simp only [CollatzResearch.WordTrace]
  refine ⟨23748735077063705914712923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31664980102751607886283897 23748735077063705914712923)
  ·
    refine ⟨35623102615595558872069385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23748735077063705914712923 35623102615595558872069385)
    ·
      refine ⟨26717326961696669154052039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35623102615595558872069385 26717326961696669154052039)
      ·
        refine ⟨40075990442545003731078059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26717326961696669154052039 40075990442545003731078059)
        ·
          refine ⟨60113985663817505596617089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40075990442545003731078059 60113985663817505596617089)
          ·
            refine ⟨45085489247863129197462817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60113985663817505596617089 45085489247863129197462817)
            ·
              refine ⟨33814116935897346898097113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45085489247863129197462817 33814116935897346898097113)
              ·
                refine ⟨25360587701923010173572835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33814116935897346898097113 25360587701923010173572835)
                ·
                  refine ⟨38040881552884515260359253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25360587701923010173572835 38040881552884515260359253)
                  ·
                    refine ⟨445791580697865413207335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 38040881552884515260359253 445791580697865413207335)
                    ·
                      rfl

theorem cell22_1302264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 2, 1, 8].length) (baseStart_1302264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302264 prefixEnd_1302264 := by exact prefixLift 1302264
  have htrace : WordTrace (prefixWord ++ tailWord_1302264) baseStart_1302264 baseEnd_1302264 := by
    simpa [prefixWord, tailWord_1302264, baseEnd_1302264] using wordTrace_append hprefix tailTrace_1302264
  have hstable : (prefixWord ++ tailWord_1302264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302264).length < 2 ^ (prefixWord ++ tailWord_1302264).sum := by decide
  have hdescent : baseEnd_1302264 < baseStart_1302264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302266 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 7, 3]
def baseStart_1302266 : Nat := 118140960795 + 1302266 * 2 ^ 59
def prefixEnd_1302266 : Nat := 4983230072969 + 3 ^ 40 * 1302266 * 2
def baseEnd_1302266 : Nat := 445792265338738074657329

theorem tailTrace_1302266 : CollatzResearch.WordTrace tailWord_1302266 prefixEnd_1302266 445792265338738074657329 := by
  unfold tailWord_1302266
  simp only [CollatzResearch.WordTrace]
  refine ⟨11874385775030041542749663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31665028733413444113999101 11874385775030041542749663)
  ·
    refine ⟨17811578662545062314124495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11874385775030041542749663 17811578662545062314124495)
    ·
      refine ⟨26717367993817593471186743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17811578662545062314124495 26717367993817593471186743)
      ·
        refine ⟨40076051990726390206780115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26717367993817593471186743 40076051990726390206780115)
        ·
          refine ⟨60114077986089585310170173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40076051990726390206780115 60114077986089585310170173)
          ·
            refine ⟨22542779244783594491313815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60114077986089585310170173 22542779244783594491313815)
            ·
              refine ⟨33814168867175391736970723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22542779244783594491313815 33814168867175391736970723)
              ·
                refine ⟨50721253300763087605456085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33814168867175391736970723 50721253300763087605456085)
                ·
                  refine ⟨1188779374236634865752877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 50721253300763087605456085 1188779374236634865752877)
                  ·
                    refine ⟨445792265338738074657329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1188779374236634865752877 445792265338738074657329)
                    ·
                      rfl

theorem cell22_1302266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 7, 3].length) (baseStart_1302266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302266 prefixEnd_1302266 := by exact prefixLift 1302266
  have htrace : WordTrace (prefixWord ++ tailWord_1302266) baseStart_1302266 baseEnd_1302266 := by
    simpa [prefixWord, tailWord_1302266, baseEnd_1302266] using wordTrace_append hprefix tailTrace_1302266
  have hstable : (prefixWord ++ tailWord_1302266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302266).length < 2 ^ (prefixWord ++ tailWord_1302266).sum := by decide
  have hdescent : baseEnd_1302266 < baseStart_1302266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302296 : List Nat := [2, 1, 2, 3, 1, 1, 2, 5, 5]
def baseStart_1302296 : Nat := 118140960795 + 1302296 * 2 ^ 59
def prefixEnd_1302296 : Nat := 4983230072969 + 3 ^ 40 * 1302296 * 2
def baseEnd_1302296 : Nat := 148600844983942665469079

theorem tailTrace_1302296 : CollatzResearch.WordTrace tailWord_1302296 prefixEnd_1302296 148600844983942665469079 := by
  unfold tailWord_1302296
  simp only [CollatzResearch.WordTrace]
  refine ⟨23749318645005740647295371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31665758193340987529727161 23749318645005740647295371)
  ·
    refine ⟨35623977967508610970943057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23749318645005740647295371 35623977967508610970943057)
    ·
      refine ⟨26717983475631458228207293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35623977967508610970943057 26717983475631458228207293)
      ·
        refine ⟨10019243803361796835577735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26717983475631458228207293 10019243803361796835577735)
        ·
          refine ⟨15028865705042695253366603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10019243803361796835577735 15028865705042695253366603)
          ·
            refine ⟨22543298557564042880049905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15028865705042695253366603 22543298557564042880049905)
            ·
              refine ⟨16907473918173032160037429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22543298557564042880049905 16907473918173032160037429)
              ·
                refine ⟨1585075679828721765003509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16907473918173032160037429 1585075679828721765003509)
                ·
                  refine ⟨148600844983942665469079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1585075679828721765003509 148600844983942665469079)
                  ·
                    rfl

theorem cell22_1302296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 5, 5].length) (baseStart_1302296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302296 prefixEnd_1302296 := by exact prefixLift 1302296
  have htrace : WordTrace (prefixWord ++ tailWord_1302296) baseStart_1302296 baseEnd_1302296 := by
    simpa [prefixWord, tailWord_1302296, baseEnd_1302296] using wordTrace_append hprefix tailTrace_1302296
  have hstable : (prefixWord ++ tailWord_1302296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302296).length < 2 ^ (prefixWord ++ tailWord_1302296).sum := by decide
  have hdescent : baseEnd_1302296 < baseStart_1302296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302334 : List Nat := [4, 2, 1, 2, 2, 2, 3, 2, 1, 3]
def baseStart_1302334 : Nat := 118140960795 + 1302334 * 2 ^ 59
def prefixEnd_1302334 : Nat := 4983230072969 + 3 ^ 40 * 1302334 * 2
def baseEnd_1302334 : Nat := 445815543128408563957121

theorem tailTrace_1302334 : CollatzResearch.WordTrace tailWord_1302334 prefixEnd_1302334 445815543128408563957121 := by
  unfold tailWord_1302334
  simp only [CollatzResearch.WordTrace]
  refine ⟨5937502907984226723059257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31666682175915875856316037 5937502907984226723059257)
  ·
    refine ⟨4453127180988170042294443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5937502907984226723059257 4453127180988170042294443)
    ·
      refine ⟨6679690771482255063441665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4453127180988170042294443 6679690771482255063441665)
      ·
        refine ⟨5009768078611691297581249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6679690771482255063441665 5009768078611691297581249)
        ·
          refine ⟨3757326058958768473185937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5009768078611691297581249 3757326058958768473185937)
          ·
            refine ⟨2817994544219076354889453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3757326058958768473185937 2817994544219076354889453)
            ·
              refine ⟨1056747954082153633083545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2817994544219076354889453 1056747954082153633083545)
              ·
                refine ⟨792560965561615224812659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1056747954082153633083545 792560965561615224812659)
                ·
                  refine ⟨1188841448342422837218989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792560965561615224812659 1188841448342422837218989)
                  ·
                    refine ⟨445815543128408563957121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1188841448342422837218989 445815543128408563957121)
                    ·
                      rfl

theorem cell22_1302334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_1302334 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302334 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302334 prefixEnd_1302334 := by exact prefixLift 1302334
  have htrace : WordTrace (prefixWord ++ tailWord_1302334) baseStart_1302334 baseEnd_1302334 := by
    simpa [prefixWord, tailWord_1302334, baseEnd_1302334] using wordTrace_append hprefix tailTrace_1302334
  have hstable : (prefixWord ++ tailWord_1302334).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302334).length < 2 ^ (prefixWord ++ tailWord_1302334).sum := by decide
  have hdescent : baseEnd_1302334 < baseStart_1302334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302403 : List Nat := [1, 1, 1, 3, 4, 4, 1, 7]
def baseStart_1302403 : Nat := 118140960795 + 1302403 * 2 ^ 59
def prefixEnd_1302403 : Nat := 4983230072969 + 3 ^ 40 * 1302403 * 2
def baseEnd_1302403 : Nat := 49537684804279487109101

theorem tailTrace_1302403 : CollatzResearch.WordTrace tailWord_1302403 prefixEnd_1302403 49537684804279487109101 := by
  unfold tailWord_1302403
  simp only [CollatzResearch.WordTrace]
  refine ⟨47502539900623838568735863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31668359933749225712490575 47502539900623838568735863)
  ·
    refine ⟨71253809850935757853103795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47502539900623838568735863 71253809850935757853103795)
    ·
      refine ⟨106880714776403636779655693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71253809850935757853103795 106880714776403636779655693)
      ·
        refine ⟨40080268041151363792370885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 106880714776403636779655693 40080268041151363792370885)
        ·
          refine ⟨7515050257715880711069541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40080268041151363792370885 7515050257715880711069541)
          ·
            refine ⟨1409071923321727633325539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7515050257715880711069541 1409071923321727633325539)
            ·
              refine ⟨2113607884982591449988309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409071923321727633325539 2113607884982591449988309)
              ·
                refine ⟨49537684804279487109101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2113607884982591449988309 49537684804279487109101)
                ·
                  rfl

theorem cell22_1302403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 7].length) (baseStart_1302403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302403 prefixEnd_1302403 := by exact prefixLift 1302403
  have htrace : WordTrace (prefixWord ++ tailWord_1302403) baseStart_1302403 baseEnd_1302403 := by
    simpa [prefixWord, tailWord_1302403, baseEnd_1302403] using wordTrace_append hprefix tailTrace_1302403
  have hstable : (prefixWord ++ tailWord_1302403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302403).length < 2 ^ (prefixWord ++ tailWord_1302403).sum := by decide
  have hdescent : baseEnd_1302403 < baseStart_1302403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302420 : List Nat := [2, 4, 2, 1, 1, 3, 3, 6]
def baseStart_1302420 : Nat := 118140960795 + 1302420 * 2 ^ 59
def prefixEnd_1302420 : Nat := 4983230072969 + 3 ^ 40 * 1302420 * 2
def baseEnd_1302420 : Nat := 49538331409548111811873

theorem tailTrace_1302420 : CollatzResearch.WordTrace tailWord_1302420 prefixEnd_1302420 49538331409548111811873 := by
  unfold tailWord_1302420
  simp only [CollatzResearch.WordTrace]
  refine ⟨23751579970781125236052357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31668773294374833648069809 23751579970781125236052357)
  ·
    refine ⟨4453421244521460981759817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23751579970781125236052357 4453421244521460981759817)
    ·
      refine ⟨3340065933391095736319863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4453421244521460981759817 3340065933391095736319863)
      ·
        refine ⟨5010098900086643604479795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3340065933391095736319863 5010098900086643604479795)
        ·
          refine ⟨7515148350129965406719693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5010098900086643604479795 7515148350129965406719693)
          ·
            refine ⟨2818180631298737027519885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7515148350129965406719693 2818180631298737027519885)
            ·
              refine ⟨1056817736737026385319957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2818180631298737027519885 1056817736737026385319957)
              ·
                refine ⟨49538331409548111811873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1056817736737026385319957 49538331409548111811873)
                ·
                  rfl

theorem cell22_1302420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 6].length) (baseStart_1302420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302420 prefixEnd_1302420 := by exact prefixLift 1302420
  have htrace : WordTrace (prefixWord ++ tailWord_1302420) baseStart_1302420 baseEnd_1302420 := by
    simpa [prefixWord, tailWord_1302420, baseEnd_1302420] using wordTrace_append hprefix tailTrace_1302420
  have hstable : (prefixWord ++ tailWord_1302420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302420).length < 2 ^ (prefixWord ++ tailWord_1302420).sum := by decide
  have hdescent : baseEnd_1302420 < baseStart_1302420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302495 : List Nat := [1, 1, 2, 3, 4, 1, 2, 3, 1, 4]
def baseStart_1302495 : Nat := 118140960795 + 1302495 * 2 ^ 59
def prefixEnd_1302495 : Nat := 4983230072969 + 3 ^ 40 * 1302495 * 2
def baseEnd_1302495 : Nat := 445870656718657810681627

theorem tailTrace_1302495 : CollatzResearch.WordTrace tailWord_1302495 prefixEnd_1302495 445870656718657810681627 := by
  unfold tailWord_1302495
  simp only [CollatzResearch.WordTrace]
  refine ⟨47505895416290538281084939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31670596944193692187389959 47505895416290538281084939)
  ·
    refine ⟨71258843124435807421627409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47505895416290538281084939 71258843124435807421627409)
    ·
      refine ⟨53444132343326855566220557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71258843124435807421627409 53444132343326855566220557)
      ·
        refine ⟨20041549628747570837332709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53444132343326855566220557 20041549628747570837332709)
        ·
          refine ⟨3757790555390169531999883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20041549628747570837332709 3757790555390169531999883)
          ·
            refine ⟨5636685833085254297999825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757790555390169531999883 5636685833085254297999825)
            ·
              refine ⟨4227514374813940723499869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5636685833085254297999825 4227514374813940723499869)
              ·
                refine ⟨1585317890555227771312451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4227514374813940723499869 1585317890555227771312451)
                ·
                  refine ⟨2377976835832841656968677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585317890555227771312451 2377976835832841656968677)
                  ·
                    refine ⟨445870656718657810681627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2377976835832841656968677 445870656718657810681627)
                    ·
                      rfl

theorem cell22_1302495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 3, 1, 4].length) (baseStart_1302495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302495 prefixEnd_1302495 := by exact prefixLift 1302495
  have htrace : WordTrace (prefixWord ++ tailWord_1302495) baseStart_1302495 baseEnd_1302495 := by
    simpa [prefixWord, tailWord_1302495, baseEnd_1302495] using wordTrace_append hprefix tailTrace_1302495
  have hstable : (prefixWord ++ tailWord_1302495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302495).length < 2 ^ (prefixWord ++ tailWord_1302495).sum := by decide
  have hdescent : baseEnd_1302495 < baseStart_1302495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302510 : List Nat := [4, 1, 2, 1, 3, 1, 3, 1, 6]
def baseStart_1302510 : Nat := 118140960795 + 1302510 * 2 ^ 59
def prefixEnd_1302510 : Nat := 4983230072969 + 3 ^ 40 * 1302510 * 2
def baseEnd_1302510 : Nat := 148625263841734257185527

theorem tailTrace_1302510 : CollatzResearch.WordTrace tailWord_1302510 prefixEnd_1302510 148625263841734257185527 := by
  unfold tailWord_1302510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5938305313904524480360123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31670961674157463895253989 5938305313904524480360123)
  ·
    refine ⟨8907457970856786720540185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5938305313904524480360123 8907457970856786720540185)
    ·
      refine ⟨6680593478142590040405139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8907457970856786720540185 6680593478142590040405139)
      ·
        refine ⟨10020890217213885060607709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6680593478142590040405139 10020890217213885060607709)
        ·
          refine ⟨3757833831455206897727891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10020890217213885060607709 3757833831455206897727891)
          ·
            refine ⟨5636750747182810346591837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3757833831455206897727891 5636750747182810346591837)
            ·
              refine ⟨2113781530193553879971939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5636750747182810346591837 2113781530193553879971939)
              ·
                refine ⟨3170672295290330819957909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113781530193553879971939 3170672295290330819957909)
                ·
                  refine ⟨148625263841734257185527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3170672295290330819957909 148625263841734257185527)
                  ·
                    rfl

theorem cell22_1302510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_1302510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302510 prefixEnd_1302510 := by exact prefixLift 1302510
  have htrace : WordTrace (prefixWord ++ tailWord_1302510) baseStart_1302510 baseEnd_1302510 := by
    simpa [prefixWord, tailWord_1302510, baseEnd_1302510] using wordTrace_append hprefix tailTrace_1302510
  have hstable : (prefixWord ++ tailWord_1302510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302510).length < 2 ^ (prefixWord ++ tailWord_1302510).sum := by decide
  have hdescent : baseEnd_1302510 < baseStart_1302510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302540 : List Nat := [2, 2, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_1302540 : Nat := 118140960795 + 1302540 * 2 ^ 59
def prefixEnd_1302540 : Nat := 4983230072969 + 3 ^ 40 * 1302540 * 2
def baseEnd_1302540 : Nat := 445886061138292693306489

theorem tailTrace_1302540 : CollatzResearch.WordTrace tailWord_1302540 prefixEnd_1302540 445886061138292693306489 := by
  unfold tailWord_1302540
  simp only [CollatzResearch.WordTrace]
  refine ⟨23753768350563755483236537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31671691134085007310982049 23753768350563755483236537)
  ·
    refine ⟨17815326262922816612427403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23753768350563755483236537 17815326262922816612427403)
    ·
      refine ⟨26722989394384224918641105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17815326262922816612427403 26722989394384224918641105)
      ·
        refine ⟨20042242045788168688980829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26722989394384224918641105 20042242045788168688980829)
        ·
          refine ⟨7515840767170563258367811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20042242045788168688980829 7515840767170563258367811)
          ·
            refine ⟨11273761150755844887551717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7515840767170563258367811 11273761150755844887551717)
            ·
              refine ⟨2113830215766720916415947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11273761150755844887551717 2113830215766720916415947)
              ·
                refine ⟨3170745323650081374623921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2113830215766720916415947 3170745323650081374623921)
                ·
                  refine ⟨2378058992737561030967941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3170745323650081374623921 2378058992737561030967941)
                  ·
                    refine ⟨445886061138292693306489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2378058992737561030967941 445886061138292693306489)
                    ·
                      rfl

theorem cell22_1302540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_1302540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302540 prefixEnd_1302540 := by exact prefixLift 1302540
  have htrace : WordTrace (prefixWord ++ tailWord_1302540) baseStart_1302540 baseEnd_1302540 := by
    simpa [prefixWord, tailWord_1302540, baseEnd_1302540] using wordTrace_append hprefix tailTrace_1302540
  have hstable : (prefixWord ++ tailWord_1302540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302540).length < 2 ^ (prefixWord ++ tailWord_1302540).sum := by decide
  have hdescent : baseEnd_1302540 < baseStart_1302540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302561 : List Nat := [1, 2, 3, 2, 5, 1, 2, 2, 4]
def baseStart_1302561 : Nat := 118140960795 + 1302561 * 2 ^ 59
def prefixEnd_1302561 : Nat := 4983230072969 + 3 ^ 40 * 1302561 * 2
def baseEnd_1302561 : Nat := 148631083289151879510475

theorem tailTrace_1302561 : CollatzResearch.WordTrace tailWord_1302561 prefixEnd_1302561 148631083289151879510475 := by
  unfold tailWord_1302561
  simp only [CollatzResearch.WordTrace]
  refine ⟨47508302634051431552987537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31672201756034287701991691 47508302634051431552987537)
  ·
    refine ⟨35631226975538573664740653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47508302634051431552987537 35631226975538573664740653)
    ·
      refine ⟨13361710115826965124277745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35631226975538573664740653 13361710115826965124277745)
      ·
        refine ⟨10021282586870223843208309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13361710115826965124277745 10021282586870223843208309)
        ·
          refine ⟨939495242519083485300779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10021282586870223843208309 939495242519083485300779)
          ·
            refine ⟨1409242863778625227951169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939495242519083485300779 1409242863778625227951169)
            ·
              refine ⟨1056932147833968920963377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1409242863778625227951169 1056932147833968920963377)
              ·
                refine ⟨792699110875476690722533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1056932147833968920963377 792699110875476690722533)
                ·
                  refine ⟨148631083289151879510475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 792699110875476690722533 148631083289151879510475)
                  ·
                    rfl

theorem cell22_1302561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 2, 2, 4].length) (baseStart_1302561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302561 prefixEnd_1302561 := by exact prefixLift 1302561
  have htrace : WordTrace (prefixWord ++ tailWord_1302561) baseStart_1302561 baseEnd_1302561 := by
    simpa [prefixWord, tailWord_1302561, baseEnd_1302561] using wordTrace_append hprefix tailTrace_1302561
  have hstable : (prefixWord ++ tailWord_1302561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302561).length < 2 ^ (prefixWord ++ tailWord_1302561).sum := by decide
  have hdescent : baseEnd_1302561 < baseStart_1302561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302621 : List Nat := [1, 4, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_1302621 : Nat := 118140960795 + 1302621 * 2 ^ 59
def prefixEnd_1302621 : Nat := 4983230072969 + 3 ^ 40 * 1302621 * 2
def baseEnd_1302621 : Nat := 445913789093635482031241

theorem tailTrace_1302621 : CollatzResearch.WordTrace tailWord_1302621 prefixEnd_1302621 445913789093635482031241 := by
  unfold tailWord_1302621
  simp only [CollatzResearch.WordTrace]
  refine ⟨47510491013834061800171717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31673660675889374533447811 47510491013834061800171717)
  ·
    refine ⟨8908217065093886587532197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47510491013834061800171717 8908217065093886587532197)
    ·
      refine ⟨1670290699705103735162287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8908217065093886587532197 1670290699705103735162287)
      ·
        refine ⟨2505436049557655602743431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670290699705103735162287 2505436049557655602743431)
        ·
          refine ⟨3758154074336483404115147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2505436049557655602743431 3758154074336483404115147)
          ·
            refine ⟨5637231111504725106172721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3758154074336483404115147 5637231111504725106172721)
            ·
              refine ⟨4227923333628543829629541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5637231111504725106172721 4227923333628543829629541)
              ·
                refine ⟨792735625055351968055539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4227923333628543829629541 792735625055351968055539)
                ·
                  refine ⟨1189103437583027952083309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792735625055351968055539 1189103437583027952083309)
                  ·
                    refine ⟨445913789093635482031241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1189103437583027952083309 445913789093635482031241)
                    ·
                      rfl

theorem cell22_1302621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_1302621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302621 prefixEnd_1302621 := by exact prefixLift 1302621
  have htrace : WordTrace (prefixWord ++ tailWord_1302621) baseStart_1302621 baseEnd_1302621 := by
    simpa [prefixWord, tailWord_1302621, baseEnd_1302621] using wordTrace_append hprefix tailTrace_1302621
  have hstable : (prefixWord ++ tailWord_1302621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302621).length < 2 ^ (prefixWord ++ tailWord_1302621).sum := by decide
  have hdescent : baseEnd_1302621 < baseStart_1302621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302634 : List Nat := [3, 1, 3, 2, 3, 1, 3, 1, 5]
def baseStart_1302634 : Nat := 118140960795 + 1302634 * 2 ^ 59
def prefixEnd_1302634 : Nat := 4983230072969 + 3 ^ 40 * 1302634 * 2
def baseEnd_1302634 : Nat := 148639413086435927152067

theorem tailTrace_1302634 : CollatzResearch.WordTrace tailWord_1302634 prefixEnd_1302634 148639413086435927152067 := by
  unfold tailWord_1302634
  simp only [CollatzResearch.WordTrace]
  refine ⟨11877741290696741255098739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31673976775191310013596637 11877741290696741255098739)
  ·
    refine ⟨17816611936045111882648109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11877741290696741255098739 17816611936045111882648109)
    ·
      refine ⟨6681229476016916955993041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17816611936045111882648109 6681229476016916955993041)
      ·
        refine ⟨5010922107012687716994781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6681229476016916955993041 5010922107012687716994781)
        ·
          refine ⟨1879095790129757893873043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5010922107012687716994781 1879095790129757893873043)
          ·
            refine ⟨2818643685194636840809565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1879095790129757893873043 2818643685194636840809565)
            ·
              refine ⟨1056991381947988815303587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2818643685194636840809565 1056991381947988815303587)
              ·
                refine ⟨1585487072921983222955381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1056991381947988815303587 1585487072921983222955381)
                ·
                  refine ⟨148639413086435927152067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1585487072921983222955381 148639413086435927152067)
                  ·
                    rfl

theorem cell22_1302634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 3, 1, 5].length) (baseStart_1302634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302634 prefixEnd_1302634 := by exact prefixLift 1302634
  have htrace : WordTrace (prefixWord ++ tailWord_1302634) baseStart_1302634 baseEnd_1302634 := by
    simpa [prefixWord, tailWord_1302634, baseEnd_1302634] using wordTrace_append hprefix tailTrace_1302634
  have hstable : (prefixWord ++ tailWord_1302634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302634).length < 2 ^ (prefixWord ++ tailWord_1302634).sum := by decide
  have hdescent : baseEnd_1302634 < baseStart_1302634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302647 : List Nat := [1, 1, 3, 1, 1, 6, 2, 2, 1, 4]
def baseStart_1302647 : Nat := 118140960795 + 1302647 * 2 ^ 59
def prefixEnd_1302647 : Nat := 4983230072969 + 3 ^ 40 * 1302647 * 2
def baseEnd_1302647 : Nat := 445922689424980080881161

theorem tailTrace_1302647 : CollatzResearch.WordTrace tailWord_1302647 prefixEnd_1302647 445922689424980080881161 := by
  unfold tailWord_1302647
  simp only [CollatzResearch.WordTrace]
  refine ⟨47511439311739868240618195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31674292874493245493745463 47511439311739868240618195)
  ·
    refine ⟨71267158967609802360927293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47511439311739868240618195 71267158967609802360927293)
    ·
      refine ⟨26725184612853675885347735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71267158967609802360927293 26725184612853675885347735)
      ·
        refine ⟨40087776919280513828021603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26725184612853675885347735 40087776919280513828021603)
        ·
          refine ⟨60131665378920770742032405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40087776919280513828021603 60131665378920770742032405)
          ·
            refine ⟨2818671814636911128532769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 60131665378920770742032405 2818671814636911128532769)
            ·
              refine ⟨2114003860977683346399577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2818671814636911128532769 2114003860977683346399577)
              ·
                refine ⟨1585502895733262509799683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2114003860977683346399577 1585502895733262509799683)
                ·
                  refine ⟨2378254343599893764699525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585502895733262509799683 2378254343599893764699525)
                  ·
                    refine ⟨445922689424980080881161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2378254343599893764699525 445922689424980080881161)
                    ·
                      rfl

theorem cell22_1302647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 2, 1, 4].length) (baseStart_1302647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302647 prefixEnd_1302647 := by exact prefixLift 1302647
  have htrace : WordTrace (prefixWord ++ tailWord_1302647) baseStart_1302647 baseEnd_1302647 := by
    simpa [prefixWord, tailWord_1302647, baseEnd_1302647] using wordTrace_append hprefix tailTrace_1302647
  have hstable : (prefixWord ++ tailWord_1302647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302647).length < 2 ^ (prefixWord ++ tailWord_1302647).sum := by decide
  have hdescent : baseEnd_1302647 < baseStart_1302647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302660 : List Nat := [2, 3, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_1302660 : Nat := 118140960795 + 1302660 * 2 ^ 59
def prefixEnd_1302660 : Nat := 4983230072969 + 3 ^ 40 * 1302660 * 2
def baseEnd_1302660 : Nat := 445927139590652380306121

theorem tailTrace_1302660 : CollatzResearch.WordTrace tailWord_1302660 prefixEnd_1302660 445927139590652380306121 := by
  unfold tailWord_1302660
  simp only [CollatzResearch.WordTrace]
  refine ⟨23755956730346385730420717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31674608973795180973894289 23755956730346385730420717)
  ·
    refine ⟨8908483773879894648907769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23755956730346385730420717 8908483773879894648907769)
    ·
      refine ⟨6681362830409920986680827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8908483773879894648907769 6681362830409920986680827)
      ·
        refine ⟨10022044245614881480021241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6681362830409920986680827 10022044245614881480021241)
        ·
          refine ⟨7516533184211161110015931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10022044245614881480021241 7516533184211161110015931)
          ·
            refine ⟨11274799776316741665023897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7516533184211161110015931 11274799776316741665023897)
            ·
              refine ⟨8456099832237556248767923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11274799776316741665023897 8456099832237556248767923)
              ·
                refine ⟨12684149748356334373151885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8456099832237556248767923 12684149748356334373151885)
                ·
                  refine ⟨4756556155633625389931957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12684149748356334373151885 4756556155633625389931957)
                  ·
                    refine ⟨445927139590652380306121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4756556155633625389931957 445927139590652380306121)
                    ·
                      rfl

theorem cell22_1302660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_1302660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302660 prefixEnd_1302660 := by exact prefixLift 1302660
  have htrace : WordTrace (prefixWord ++ tailWord_1302660) baseStart_1302660 baseEnd_1302660 := by
    simpa [prefixWord, tailWord_1302660, baseEnd_1302660] using wordTrace_append hprefix tailTrace_1302660
  have hstable : (prefixWord ++ tailWord_1302660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302660).length < 2 ^ (prefixWord ++ tailWord_1302660).sum := by decide
  have hdescent : baseEnd_1302660 < baseStart_1302660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302677 : List Nat := [1, 3, 2, 1, 1, 1, 4, 4, 2, 3]
def baseStart_1302677 : Nat := 118140960795 + 1302677 * 2 ^ 59
def prefixEnd_1302677 : Nat := 4983230072969 + 3 ^ 40 * 1302677 * 2
def baseEnd_1302677 : Nat := 445932959038070002631069

theorem tailTrace_1302677 : CollatzResearch.WordTrace tailWord_1302677 prefixEnd_1302677 445932959038070002631069 := by
  unfold tailWord_1302677
  simp only [CollatzResearch.WordTrace]
  refine ⟨47512533501631183364210285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31675022334420788909473523 47512533501631183364210285)
  ·
    refine ⟨17817200063111693761578857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47512533501631183364210285 17817200063111693761578857)
    ·
      refine ⟨13362900047333770321184143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17817200063111693761578857 13362900047333770321184143)
      ·
        refine ⟨20044350071000655481776215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13362900047333770321184143 20044350071000655481776215)
        ·
          refine ⟨30066525106500983222664323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20044350071000655481776215 30066525106500983222664323)
          ·
            refine ⟨45099787659751474833996485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30066525106500983222664323 45099787659751474833996485)
            ·
              refine ⟨8456210186203401531374341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45099787659751474833996485 8456210186203401531374341)
              ·
                refine ⟨1585539409913137787132689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8456210186203401531374341 1585539409913137787132689)
                ·
                  refine ⟨1189154557434853340349517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1585539409913137787132689 1189154557434853340349517)
                  ·
                    refine ⟨445932959038070002631069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1189154557434853340349517 445932959038070002631069)
                    ·
                      rfl

theorem cell22_1302677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 4, 2, 3].length) (baseStart_1302677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302677 prefixEnd_1302677 := by exact prefixLift 1302677
  have htrace : WordTrace (prefixWord ++ tailWord_1302677) baseStart_1302677 baseEnd_1302677 := by
    simpa [prefixWord, tailWord_1302677, baseEnd_1302677] using wordTrace_append hprefix tailTrace_1302677
  have hstable : (prefixWord ++ tailWord_1302677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302677).length < 2 ^ (prefixWord ++ tailWord_1302677).sum := by decide
  have hdescent : baseEnd_1302677 < baseStart_1302677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302679 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 6]
def baseStart_1302679 : Nat := 118140960795 + 1302679 * 2 ^ 59
def prefixEnd_1302679 : Nat := 4983230072969 + 3 ^ 40 * 1302679 * 2
def baseEnd_1302679 : Nat := 148644547892980888027021

theorem tailTrace_1302679 : CollatzResearch.WordTrace tailWord_1302679 prefixEnd_1302679 148644547892980888027021 := by
  unfold tailWord_1302679
  simp only [CollatzResearch.WordTrace]
  refine ⟨47512606447623937705783091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31675070965082625137188727 47512606447623937705783091)
  ·
    refine ⟨71268909671435906558674637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47512606447623937705783091 71268909671435906558674637)
    ·
      refine ⟨26725841126788464959502989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71268909671435906558674637 26725841126788464959502989)
      ·
        refine ⟨10022190422545674359813621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26725841126788464959502989 10022190422545674359813621)
        ·
          refine ⟨939580352113656971232527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10022190422545674359813621 939580352113656971232527)
          ·
            refine ⟨1409370528170485456848791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939580352113656971232527 1409370528170485456848791)
            ·
              refine ⟨2114055792255728185273187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409370528170485456848791 2114055792255728185273187)
              ·
                refine ⟨3171083688383592277909781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2114055792255728185273187 3171083688383592277909781)
                ·
                  refine ⟨148644547892980888027021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3171083688383592277909781 148644547892980888027021)
                  ·
                    rfl

theorem cell22_1302679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 6].length) (baseStart_1302679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302679 prefixEnd_1302679 := by exact prefixLift 1302679
  have htrace : WordTrace (prefixWord ++ tailWord_1302679) baseStart_1302679 baseEnd_1302679 := by
    simpa [prefixWord, tailWord_1302679, baseEnd_1302679] using wordTrace_append hprefix tailTrace_1302679
  have hstable : (prefixWord ++ tailWord_1302679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302679).length < 2 ^ (prefixWord ++ tailWord_1302679).sum := by decide
  have hdescent : baseEnd_1302679 < baseStart_1302679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302698 : List Nat := [3, 1, 5, 1, 3, 1, 1, 2, 1, 4]
def baseStart_1302698 : Nat := 118140960795 + 1302698 * 2 ^ 59
def prefixEnd_1302698 : Nat := 4983230072969 + 3 ^ 40 * 1302698 * 2
def baseEnd_1302698 : Nat := 445940147767232947856005

theorem tailTrace_1302698 : CollatzResearch.WordTrace tailWord_1302698 prefixEnd_1302698 445940147767232947856005 := by
  unfold tailWord_1302698
  simp only [CollatzResearch.WordTrace]
  refine ⟨11878324858638775987681187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31675532956370069300483165 11878324858638775987681187)
  ·
    refine ⟨17817487287958163981521781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11878324858638775987681187 17817487287958163981521781)
    ·
      refine ⟨1670389433246077873267667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17817487287958163981521781 1670389433246077873267667)
      ·
        refine ⟨2505584149869116809901501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1670389433246077873267667 2505584149869116809901501)
        ·
          refine ⟨939594056200918803713063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2505584149869116809901501 939594056200918803713063)
          ·
            refine ⟨1409391084301378205569595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939594056200918803713063 1409391084301378205569595)
            ·
              refine ⟨2114086626452067308354393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409391084301378205569595 2114086626452067308354393)
              ·
                refine ⟨1585564969839050481265795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2114086626452067308354393 1585564969839050481265795)
                ·
                  refine ⟨2378347454758575721898693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585564969839050481265795 2378347454758575721898693)
                  ·
                    refine ⟨445940147767232947856005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2378347454758575721898693 445940147767232947856005)
                    ·
                      rfl

theorem cell22_1302698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 2, 1, 4].length) (baseStart_1302698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302698 prefixEnd_1302698 := by exact prefixLift 1302698
  have htrace : WordTrace (prefixWord ++ tailWord_1302698) baseStart_1302698 baseEnd_1302698 := by
    simpa [prefixWord, tailWord_1302698, baseEnd_1302698] using wordTrace_append hprefix tailTrace_1302698
  have hstable : (prefixWord ++ tailWord_1302698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302698).length < 2 ^ (prefixWord ++ tailWord_1302698).sum := by decide
  have hdescent : baseEnd_1302698 < baseStart_1302698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302786 : List Nat := [3, 4, 1, 1, 2, 3, 1, 2, 5]
def baseStart_1302786 : Nat := 118140960795 + 1302786 * 2 ^ 59
def prefixEnd_1302786 : Nat := 4983230072969 + 3 ^ 40 * 1302786 * 2
def baseEnd_1302786 : Nat := 148656757321876683885245

theorem tailTrace_1302786 : CollatzResearch.WordTrace tailWord_1302786 prefixEnd_1302786 148656757321876683885245 := by
  unfold tailWord_1302786
  simp only [CollatzResearch.WordTrace]
  refine ⟨11879127264559073744982053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31677672705490863319952141 11879127264559073744982053)
  ·
    refine ⟨2227336362104826327184135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11879127264559073744982053 2227336362104826327184135)
    ·
      refine ⟨3341004543157239490776203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2227336362104826327184135 3341004543157239490776203)
      ·
        refine ⟨5011506814735859236164305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3341004543157239490776203 5011506814735859236164305)
        ·
          refine ⟨3758630111051894427123229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5011506814735859236164305 3758630111051894427123229)
          ·
            refine ⟨1409486291644460410171211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3758630111051894427123229 1409486291644460410171211)
            ·
              refine ⟨2114229437466690615256817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1409486291644460410171211 2114229437466690615256817)
              ·
                refine ⟨1585672078100017961442613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2114229437466690615256817 1585672078100017961442613)
                ·
                  refine ⟨148656757321876683885245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1585672078100017961442613 148656757321876683885245)
                  ·
                    rfl

theorem cell22_1302786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_1302786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302786 prefixEnd_1302786 := by exact prefixLift 1302786
  have htrace : WordTrace (prefixWord ++ tailWord_1302786) baseStart_1302786 baseEnd_1302786 := by
    simpa [prefixWord, tailWord_1302786, baseEnd_1302786] using wordTrace_append hprefix tailTrace_1302786
  have hstable : (prefixWord ++ tailWord_1302786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302786).length < 2 ^ (prefixWord ++ tailWord_1302786).sum := by decide
  have hdescent : baseEnd_1302786 < baseStart_1302786 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302842 : List Nat := [3, 1, 1, 1, 4, 4, 8]
def baseStart_1302842 : Nat := 118140960795 + 1302842 * 2 ^ 59
def prefixEnd_1302842 : Nat := 4983230072969 + 3 ^ 40 * 1302842 * 2
def baseEnd_1302842 : Nat := 16518127478150539713169

theorem tailTrace_1302842 : CollatzResearch.WordTrace tailWord_1302842 prefixEnd_1302842 16518127478150539713169 := by
  unfold tailWord_1302842
  simp only [CollatzResearch.WordTrace]
  refine ⟨11879637886508354135991695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31679034364022277695977853 11879637886508354135991695)
  ·
    refine ⟨17819456829762531203987543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11879637886508354135991695 17819456829762531203987543)
    ·
      refine ⟨26729185244643796805981315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17819456829762531203987543 26729185244643796805981315)
      ·
        refine ⟨40093777866965695208971973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26729185244643796805981315 40093777866965695208971973)
        ·
          refine ⟨7517583350056067851682245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 40093777866965695208971973 7517583350056067851682245)
          ·
            refine ⟨1409546878135512722190421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7517583350056067851682245 1409546878135512722190421)
            ·
              refine ⟨16518127478150539713169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1409546878135512722190421 16518127478150539713169)
              ·
                rfl

theorem cell22_1302842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 8].length) (baseStart_1302842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302842 prefixEnd_1302842 := by exact prefixLift 1302842
  have htrace : WordTrace (prefixWord ++ tailWord_1302842) baseStart_1302842 baseEnd_1302842 := by
    simpa [prefixWord, tailWord_1302842, baseEnd_1302842] using wordTrace_append hprefix tailTrace_1302842
  have hstable : (prefixWord ++ tailWord_1302842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302842).length < 2 ^ (prefixWord ++ tailWord_1302842).sum := by decide
  have hdescent : baseEnd_1302842 < baseStart_1302842 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1302951 : List Nat := [1, 1, 6, 1, 1, 3, 1, 3, 1, 4]
def baseStart_1302951 : Nat := 118140960795 + 1302951 * 2 ^ 59
def prefixEnd_1302951 : Nat := 4983230072969 + 3 ^ 40 * 1302951 * 2
def baseEnd_1302951 : Nat := 446026754837624621280229

theorem tailTrace_1302951 : CollatzResearch.WordTrace tailWord_1302951 prefixEnd_1302951 446026754837624621280229 := by
  unfold tailWord_1302951
  simp only [CollatzResearch.WordTrace]
  refine ⟨47522527102638528159684707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31681684735092352106456471 47522527102638528159684707)
  ·
    refine ⟨71283790653957792239527061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47522527102638528159684707 71283790653957792239527061)
    ·
      refine ⟨3341427686904271511227831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 71283790653957792239527061 3341427686904271511227831)
      ·
        refine ⟨5012141530356407266841747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3341427686904271511227831 5012141530356407266841747)
        ·
          refine ⟨7518212295534610900262621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5012141530356407266841747 7518212295534610900262621)
          ·
            refine ⟨2819329610825479087598483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7518212295534610900262621 2819329610825479087598483)
            ·
              refine ⟨4228994416238218631397725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819329610825479087598483 4228994416238218631397725)
              ·
                refine ⟨1585872906089331986774147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4228994416238218631397725 1585872906089331986774147)
                ·
                  refine ⟨2378809359133997980161221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1585872906089331986774147 2378809359133997980161221)
                  ·
                    refine ⟨446026754837624621280229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2378809359133997980161221 446026754837624621280229)
                    ·
                      rfl

theorem cell22_1302951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_1302951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1302951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1302951 prefixEnd_1302951 := by exact prefixLift 1302951
  have htrace : WordTrace (prefixWord ++ tailWord_1302951) baseStart_1302951 baseEnd_1302951 := by
    simpa [prefixWord, tailWord_1302951, baseEnd_1302951] using wordTrace_append hprefix tailTrace_1302951
  have hstable : (prefixWord ++ tailWord_1302951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1302951).length < 2 ^ (prefixWord ++ tailWord_1302951).sum := by decide
  have hdescent : baseEnd_1302951 < baseStart_1302951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1302951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303011 : List Nat := [1, 1, 1, 6, 4, 1, 8]
def baseStart_1303011 : Nat := 118140960795 + 1303011 * 2 ^ 59
def prefixEnd_1303011 : Nat := 4983230072969 + 3 ^ 40 * 1303011 * 2
def baseEnd_1303011 : Nat := 16520270150511276473335

theorem tailTrace_1303011 : CollatzResearch.WordTrace tailWord_1303011 prefixEnd_1303011 16520270150511276473335 := by
  unfold tailWord_1303011
  simp only [CollatzResearch.WordTrace]
  refine ⟨47524715482421158406868887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31683143654947438937912591 47524715482421158406868887)
  ·
    refine ⟨71287073223631737610303331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47524715482421158406868887 71287073223631737610303331)
    ·
      refine ⟨106930609835447606415454997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71287073223631737610303331 106930609835447606415454997)
      ·
        refine ⟨5012372336036606550724453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 106930609835447606415454997 5012372336036606550724453)
        ·
          refine ⟨939819813006863728260835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5012372336036606550724453 939819813006863728260835)
          ·
            refine ⟨1409729719510295592391253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 939819813006863728260835 1409729719510295592391253)
            ·
              refine ⟨16520270150511276473335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1409729719510295592391253 16520270150511276473335)
              ·
                rfl

theorem cell22_1303011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 8].length) (baseStart_1303011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303011 prefixEnd_1303011 := by exact prefixLift 1303011
  have htrace : WordTrace (prefixWord ++ tailWord_1303011) baseStart_1303011 baseEnd_1303011 := by
    simpa [prefixWord, tailWord_1303011, baseEnd_1303011] using wordTrace_append hprefix tailTrace_1303011
  have hstable : (prefixWord ++ tailWord_1303011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303011).length < 2 ^ (prefixWord ++ tailWord_1303011).sum := by decide
  have hdescent : baseEnd_1303011 < baseStart_1303011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303039 : List Nat := [1, 1, 2, 2, 1, 2, 5, 3, 5]
def baseStart_1303039 : Nat := 118140960795 + 1303039 * 2 ^ 59
def prefixEnd_1303039 : Nat := 4983230072969 + 3 ^ 40 * 1303039 * 2
def baseEnd_1303039 : Nat := 148685626345340575026653

theorem tailTrace_1303039 : CollatzResearch.WordTrace tailWord_1303039 prefixEnd_1303039 148685626345340575026653 := by
  unfold tailWord_1303039
  simp only [CollatzResearch.WordTrace]
  refine ⟨47525736726319719188888171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31683824484213146125925447 47525736726319719188888171)
  ·
    refine ⟨71288605089479578783332257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47525736726319719188888171 71288605089479578783332257)
    ·
      refine ⟨53466453817109684087499193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71288605089479578783332257 53466453817109684087499193)
      ·
        refine ⟨40099840362832263065624395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53466453817109684087499193 40099840362832263065624395)
        ·
          refine ⟨60149760544248394598436593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40099840362832263065624395 60149760544248394598436593)
          ·
            refine ⟨45112320408186295948827445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60149760544248394598436593 45112320408186295948827445)
            ·
              refine ⟨4229280038267465245202573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45112320408186295948827445 4229280038267465245202573)
              ·
                refine ⟨1585980014350299466950965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4229280038267465245202573 1585980014350299466950965)
                ·
                  refine ⟨148685626345340575026653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1585980014350299466950965 148685626345340575026653)
                  ·
                    rfl

theorem cell22_1303039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 3, 5].length) (baseStart_1303039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303039 prefixEnd_1303039 := by exact prefixLift 1303039
  have htrace : WordTrace (prefixWord ++ tailWord_1303039) baseStart_1303039 baseEnd_1303039 := by
    simpa [prefixWord, tailWord_1303039, baseEnd_1303039] using wordTrace_append hprefix tailTrace_1303039
  have hstable : (prefixWord ++ tailWord_1303039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303039).length < 2 ^ (prefixWord ++ tailWord_1303039).sum := by decide
  have hdescent : baseEnd_1303039 < baseStart_1303039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303101 : List Nat := [1, 4, 1, 3, 2, 2, 1, 2, 6]
def baseStart_1303101 : Nat := 118140960795 + 1303101 * 2 ^ 59
def prefixEnd_1303101 : Nat := 4983230072969 + 3 ^ 40 * 1303101 * 2
def baseEnd_1303101 : Nat := 148692700967691410009923

theorem tailTrace_1303101 : CollatzResearch.WordTrace tailWord_1303101 prefixEnd_1303101 148692700967691410009923 := by
  unfold tailWord_1303101
  simp only [CollatzResearch.WordTrace]
  refine ⟨47527998052095103777645157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31685332034730069185096771 47527998052095103777645157)
  ·
    refine ⟨8911499634767831958308467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47527998052095103777645157 8911499634767831958308467)
    ·
      refine ⟨13367249452151747937462701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8911499634767831958308467 13367249452151747937462701)
      ·
        refine ⟨5012718544556905476548513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13367249452151747937462701 5012718544556905476548513)
        ·
          refine ⟨3759538908417679107411385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5012718544556905476548513 3759538908417679107411385)
          ·
            refine ⟨2819654181313259330558539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3759538908417679107411385 2819654181313259330558539)
            ·
              refine ⟨4229481271969888995837809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2819654181313259330558539 4229481271969888995837809)
              ·
                refine ⟨3172110953977416746878357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4229481271969888995837809 3172110953977416746878357)
                ·
                  refine ⟨148692700967691410009923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3172110953977416746878357 148692700967691410009923)
                  ·
                    rfl

theorem cell22_1303101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_1303101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303101 prefixEnd_1303101 := by exact prefixLift 1303101
  have htrace : WordTrace (prefixWord ++ tailWord_1303101) baseStart_1303101 baseEnd_1303101 := by
    simpa [prefixWord, tailWord_1303101, baseEnd_1303101] using wordTrace_append hprefix tailTrace_1303101
  have hstable : (prefixWord ++ tailWord_1303101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303101).length < 2 ^ (prefixWord ++ tailWord_1303101).sum := by decide
  have hdescent : baseEnd_1303101 < baseStart_1303101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303116 : List Nat := [2, 2, 1, 3, 1, 2, 2, 2, 4, 3]
def baseStart_1303116 : Nat := 118140960795 + 1303116 * 2 ^ 59
def prefixEnd_1303116 : Nat := 4983230072969 + 3 ^ 40 * 1303116 * 2
def baseEnd_1303116 : Nat := 446083237709619190904723

theorem tailTrace_1303116 : CollatzResearch.WordTrace tailWord_1303116 prefixEnd_1303116 446083237709619190904723 := by
  unfold tailWord_1303116
  simp only [CollatzResearch.WordTrace]
  refine ⟨23764272573520380669720601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31685696764693840892960801 23764272573520380669720601)
  ·
    refine ⟨17823204430140285502290451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23764272573520380669720601 17823204430140285502290451)
    ·
      refine ⟨26734806645210428253435677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17823204430140285502290451 26734806645210428253435677)
      ·
        refine ⟨10025552491953910595038379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26734806645210428253435677 10025552491953910595038379)
        ·
          refine ⟨15038328737930865892557569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10025552491953910595038379 15038328737930865892557569)
          ·
            refine ⟨11278746553448149419418177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15038328737930865892557569 11278746553448149419418177)
            ·
              refine ⟨8459059915086112064563633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11278746553448149419418177 8459059915086112064563633)
              ·
                refine ⟨6344294936314584048422725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8459059915086112064563633 6344294936314584048422725)
                ·
                  refine ⟨1189555300558984509079261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6344294936314584048422725 1189555300558984509079261)
                  ·
                    refine ⟨446083237709619190904723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1189555300558984509079261 446083237709619190904723)
                    ·
                      rfl

theorem cell22_1303116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_1303116 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303116 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303116 prefixEnd_1303116 := by exact prefixLift 1303116
  have htrace : WordTrace (prefixWord ++ tailWord_1303116) baseStart_1303116 baseEnd_1303116 := by
    simpa [prefixWord, tailWord_1303116, baseEnd_1303116] using wordTrace_append hprefix tailTrace_1303116
  have hstable : (prefixWord ++ tailWord_1303116).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303116).length < 2 ^ (prefixWord ++ tailWord_1303116).sum := by decide
  have hdescent : baseEnd_1303116 < baseStart_1303116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303159 : List Nat := [1, 1, 3, 1, 1, 3, 2, 2, 2, 6]
def baseStart_1303159 : Nat := 118140960795 + 1303159 * 2 ^ 59
def prefixEnd_1303159 : Nat := 4983230072969 + 3 ^ 40 * 1303159 * 2
def baseEnd_1303159 : Nat := 446097957488381412079591

theorem tailTrace_1303159 : CollatzResearch.WordTrace tailWord_1303159 prefixEnd_1303159 446097957488381412079591 := by
  unfold tailWord_1303159
  simp only [CollatzResearch.WordTrace]
  refine ⟨47530113485884979683256531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31686742323923319788837687 47530113485884979683256531)
  ·
    refine ⟨71295170228827469524884797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47530113485884979683256531 71295170228827469524884797)
    ·
      refine ⟨26735688835810301071831799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71295170228827469524884797 26735688835810301071831799)
      ·
        refine ⟨40103533253715451607747699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26735688835810301071831799 40103533253715451607747699)
        ·
          refine ⟨60155299880573177411621549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40103533253715451607747699 60155299880573177411621549)
          ·
            refine ⟨22558237455214941529358081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60155299880573177411621549 22558237455214941529358081)
            ·
              refine ⟨16918678091411206147018561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22558237455214941529358081 16918678091411206147018561)
              ·
                refine ⟨12689008568558404610263921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16918678091411206147018561 12689008568558404610263921)
                ·
                  refine ⟨9516756426418803457697941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12689008568558404610263921 9516756426418803457697941)
                  ·
                    refine ⟨446097957488381412079591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9516756426418803457697941 446097957488381412079591)
                    ·
                      rfl

theorem cell22_1303159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 6].length) (baseStart_1303159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303159 prefixEnd_1303159 := by exact prefixLift 1303159
  have htrace : WordTrace (prefixWord ++ tailWord_1303159) baseStart_1303159 baseEnd_1303159 := by
    simpa [prefixWord, tailWord_1303159, baseEnd_1303159] using wordTrace_append hprefix tailTrace_1303159
  have hstable : (prefixWord ++ tailWord_1303159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303159).length < 2 ^ (prefixWord ++ tailWord_1303159).sum := by decide
  have hdescent : baseEnd_1303159 < baseStart_1303159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303191 : List Nat := [1, 1, 3, 3, 2, 1, 2, 4, 5]
def baseStart_1303191 : Nat := 118140960795 + 1303191 * 2 ^ 59
def prefixEnd_1303191 : Nat := 4983230072969 + 3 ^ 40 * 1303191 * 2
def baseEnd_1303191 : Nat := 148702970580781331759831

theorem tailTrace_1303191 : CollatzResearch.WordTrace tailWord_1303191 prefixEnd_1303191 148702970580781331759831 := by
  unfold tailWord_1303191
  simp only [CollatzResearch.WordTrace]
  refine ⟨47531280621769049148421427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31687520414512699432280951 47531280621769049148421427)
  ·
    refine ⟨71296920932653573722632141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47531280621769049148421427 71296920932653573722632141)
    ·
      refine ⟨26736345349745090145987053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71296920932653573722632141 26736345349745090145987053)
      ·
        refine ⟨10026129506154408804745145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26736345349745090145987053 10026129506154408804745145)
        ·
          refine ⟨7519597129615806603558859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10026129506154408804745145 7519597129615806603558859)
          ·
            refine ⟨11279395694423709905338289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7519597129615806603558859 11279395694423709905338289)
            ·
              refine ⟨8459546770817782429003717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11279395694423709905338289 8459546770817782429003717)
              ·
                refine ⟨1586165019528334205438197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8459546770817782429003717 1586165019528334205438197)
                ·
                  refine ⟨148702970580781331759831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1586165019528334205438197 148702970580781331759831)
                  ·
                    rfl

theorem cell22_1303191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 4, 5].length) (baseStart_1303191 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303191 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303191 prefixEnd_1303191 := by exact prefixLift 1303191
  have htrace : WordTrace (prefixWord ++ tailWord_1303191) baseStart_1303191 baseEnd_1303191 := by
    simpa [prefixWord, tailWord_1303191, baseEnd_1303191] using wordTrace_append hprefix tailTrace_1303191
  have hstable : (prefixWord ++ tailWord_1303191).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303191).length < 2 ^ (prefixWord ++ tailWord_1303191).sum := by decide
  have hdescent : baseEnd_1303191 < baseStart_1303191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303268 : List Nat := [2, 3, 1, 1, 1, 5, 2, 1, 1, 5]
def baseStart_1303268 : Nat := 118140960795 + 1303268 * 2 ^ 59
def prefixEnd_1303268 : Nat := 4983230072969 + 3 ^ 40 * 1303268 * 2
def baseEnd_1303268 : Nat := 446135270415941461104257

theorem tailTrace_1303268 : CollatzResearch.WordTrace tailWord_1303268 prefixEnd_1303268 446135270415941461104257 := by
  unfold tailWord_1303268
  simp only [CollatzResearch.WordTrace]
  refine ⟨23767044521245045649487229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31689392694993394199316305 23767044521245045649487229)
  ·
    refine ⟨8912641695466892118557711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23767044521245045649487229 8912641695466892118557711)
    ·
      refine ⟨13368962543200338177836567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8912641695466892118557711 13368962543200338177836567)
      ·
        refine ⟨20053443814800507266754851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13368962543200338177836567 20053443814800507266754851)
        ·
          refine ⟨30080165722200760900132277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20053443814800507266754851 30080165722200760900132277)
          ·
            refine ⟨2820015536456321334387401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30080165722200760900132277 2820015536456321334387401)
            ·
              refine ⟨2115011652342241000790551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2820015536456321334387401 2115011652342241000790551)
              ·
                refine ⟨3172517478513361501185827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2115011652342241000790551 3172517478513361501185827)
                ·
                  refine ⟨4758776217770042251778741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3172517478513361501185827 4758776217770042251778741)
                  ·
                    refine ⟨446135270415941461104257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4758776217770042251778741 446135270415941461104257)
                    ·
                      rfl

theorem cell22_1303268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_1303268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303268 prefixEnd_1303268 := by exact prefixLift 1303268
  have htrace : WordTrace (prefixWord ++ tailWord_1303268) baseStart_1303268 baseEnd_1303268 := by
    simpa [prefixWord, tailWord_1303268, baseEnd_1303268] using wordTrace_append hprefix tailTrace_1303268
  have hstable : (prefixWord ++ tailWord_1303268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303268).length < 2 ^ (prefixWord ++ tailWord_1303268).sum := by decide
  have hdescent : baseEnd_1303268 < baseStart_1303268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303298 : List Nat := [3, 4, 1, 1, 1, 3, 9]
def baseStart_1303298 : Nat := 118140960795 + 1303298 * 2 ^ 59
def prefixEnd_1303298 : Nat := 4983230072969 + 3 ^ 40 * 1303298 * 2
def baseEnd_1303298 : Nat := 16523908889964125290895

theorem tailTrace_1303298 : CollatzResearch.WordTrace tailWord_1303298 prefixEnd_1303298 16523908889964125290895 := by
  unfold tailWord_1303298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11883795808095351605641637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31690122154920937615044365 11883795808095351605641637)
  ·
    refine ⟨2228211714017878426057807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11883795808095351605641637 2228211714017878426057807)
    ·
      refine ⟨3342317571026817639086711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2228211714017878426057807 3342317571026817639086711)
      ·
        refine ⟨5013476356540226458630067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3342317571026817639086711 5013476356540226458630067)
        ·
          refine ⟨7520214534810339687945101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5013476356540226458630067 7520214534810339687945101)
          ·
            refine ⟨2820080450553877382979413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7520214534810339687945101 2820080450553877382979413)
            ·
              refine ⟨16523908889964125290895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2820080450553877382979413 16523908889964125290895)
              ·
                rfl

theorem cell22_1303298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 9].length) (baseStart_1303298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303298 prefixEnd_1303298 := by exact prefixLift 1303298
  have htrace : WordTrace (prefixWord ++ tailWord_1303298) baseStart_1303298 baseEnd_1303298 := by
    simpa [prefixWord, tailWord_1303298, baseEnd_1303298] using wordTrace_append hprefix tailTrace_1303298
  have hstable : (prefixWord ++ tailWord_1303298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303298).length < 2 ^ (prefixWord ++ tailWord_1303298).sum := by decide
  have hdescent : baseEnd_1303298 < baseStart_1303298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303313 : List Nat := [1, 2, 2, 1, 1, 3, 3, 3, 3, 3]
def baseStart_1303313 : Nat := 118140960795 + 1303313 * 2 ^ 59
def prefixEnd_1303313 : Nat := 4983230072969 + 3 ^ 40 * 1303313 * 2
def baseEnd_1303313 : Nat := 446150674835576343729119

theorem tailTrace_1303313 : CollatzResearch.WordTrace tailWord_1303313 prefixEnd_1303313 446150674835576343729119 := by
  unfold tailWord_1303313
  simp only [CollatzResearch.WordTrace]
  refine ⟨47535730327327063984362593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31690486884884709322908395 47535730327327063984362593)
  ·
    refine ⟨35651797745495297988271945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47535730327327063984362593 35651797745495297988271945)
    ·
      refine ⟨26738848309121473491203959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35651797745495297988271945 26738848309121473491203959)
      ·
        refine ⟨40108272463682210236805939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26738848309121473491203959 40108272463682210236805939)
        ·
          refine ⟨60162408695523315355208909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40108272463682210236805939 60162408695523315355208909)
          ·
            refine ⟨22560903260821243258203341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60162408695523315355208909 22560903260821243258203341)
            ·
              refine ⟨8460338722807966221826253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22560903260821243258203341 8460338722807966221826253)
              ·
                refine ⟨3172627021052987333184845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8460338722807966221826253 3172627021052987333184845)
                ·
                  refine ⟨1189735132894870249944317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3172627021052987333184845 1189735132894870249944317)
                  ·
                    refine ⟨446150674835576343729119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1189735132894870249944317 446150674835576343729119)
                    ·
                      rfl

theorem cell22_1303313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 3, 3, 3].length) (baseStart_1303313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303313 prefixEnd_1303313 := by exact prefixLift 1303313
  have htrace : WordTrace (prefixWord ++ tailWord_1303313) baseStart_1303313 baseEnd_1303313 := by
    simpa [prefixWord, tailWord_1303313, baseEnd_1303313] using wordTrace_append hprefix tailTrace_1303313
  have hstable : (prefixWord ++ tailWord_1303313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303313).length < 2 ^ (prefixWord ++ tailWord_1303313).sum := by decide
  have hdescent : baseEnd_1303313 < baseStart_1303313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303330 : List Nat := [3, 3, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_1303330 : Nat := 118140960795 + 1303330 * 2 ^ 59
def prefixEnd_1303330 : Nat := 4983230072969 + 3 ^ 40 * 1303330 * 2
def baseEnd_1303330 : Nat := 446156494282993966054067

theorem tailTrace_1303330 : CollatzResearch.WordTrace tailWord_1303330 prefixEnd_1303330 446156494282993966054067 := by
  unfold tailWord_1303330
  simp only [CollatzResearch.WordTrace]
  refine ⟨11884087592066368971932861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31690900245510317258487629 11884087592066368971932861)
  ·
    refine ⟨4456532847024888364474823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11884087592066368971932861 4456532847024888364474823)
    ·
      refine ⟨6684799270537332546712235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4456532847024888364474823 6684799270537332546712235)
      ·
        refine ⟨10027198905805998820068353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6684799270537332546712235 10027198905805998820068353)
        ·
          refine ⟨7520399179354499115051265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10027198905805998820068353 7520399179354499115051265)
          ·
            refine ⟨5640299384515874336288449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7520399179354499115051265 5640299384515874336288449)
            ·
              refine ⟨4230224538386905752216337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5640299384515874336288449 4230224538386905752216337)
              ·
                refine ⟨3172668403790179314162253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4230224538386905752216337 3172668403790179314162253)
                ·
                  refine ⟨1189750651421317242810845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3172668403790179314162253 1189750651421317242810845)
                  ·
                    refine ⟨446156494282993966054067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1189750651421317242810845 446156494282993966054067)
                    ·
                      rfl

theorem cell22_1303330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_1303330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303330 prefixEnd_1303330 := by exact prefixLift 1303330
  have htrace : WordTrace (prefixWord ++ tailWord_1303330) baseStart_1303330 baseEnd_1303330 := by
    simpa [prefixWord, tailWord_1303330, baseEnd_1303330] using wordTrace_append hprefix tailTrace_1303330
  have hstable : (prefixWord ++ tailWord_1303330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303330).length < 2 ^ (prefixWord ++ tailWord_1303330).sum := by decide
  have hdescent : baseEnd_1303330 < baseStart_1303330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303332 : List Nat := [2, 3, 1, 3, 4, 1, 2, 6]
def baseStart_1303332 : Nat := 118140960795 + 1303332 * 2 ^ 59
def prefixEnd_1303332 : Nat := 4983230072969 + 3 ^ 40 * 1303332 * 2
def baseEnd_1303332 : Nat := 49573019880429625278229

theorem tailTrace_1303332 : CollatzResearch.WordTrace tailWord_1303332 prefixEnd_1303332 49573019880429625278229 := by
  unfold tailWord_1303332
  simp only [CollatzResearch.WordTrace]
  refine ⟨23768211657129115114652125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31690948876172153486202833 23768211657129115114652125)
  ·
    refine ⟨8913079371423418167994547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23768211657129115114652125 8913079371423418167994547)
    ·
      refine ⟨13369619057135127251991821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8913079371423418167994547 13369619057135127251991821)
      ·
        refine ⟨5013607146425672719496933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13369619057135127251991821 5013607146425672719496933)
        ·
          refine ⟨940051339954813634905675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5013607146425672719496933 940051339954813634905675)
          ·
            refine ⟨1410077009932220452358513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940051339954813634905675 1410077009932220452358513)
            ·
              refine ⟨1057557757449165339268885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410077009932220452358513 1057557757449165339268885)
              ·
                refine ⟨49573019880429625278229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1057557757449165339268885 49573019880429625278229)
                ·
                  rfl

theorem cell22_1303332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 4, 1, 2, 6].length) (baseStart_1303332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303332 prefixEnd_1303332 := by exact prefixLift 1303332
  have htrace : WordTrace (prefixWord ++ tailWord_1303332) baseStart_1303332 baseEnd_1303332 := by
    simpa [prefixWord, tailWord_1303332, baseEnd_1303332] using wordTrace_append hprefix tailTrace_1303332
  have hstable : (prefixWord ++ tailWord_1303332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303332).length < 2 ^ (prefixWord ++ tailWord_1303332).sum := by decide
  have hdescent : baseEnd_1303332 < baseStart_1303332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303347 : List Nat := [1, 1, 1, 2, 6, 1, 3, 3, 1, 3]
def baseStart_1303347 : Nat := 118140960795 + 1303347 * 2 ^ 59
def prefixEnd_1303347 : Nat := 4983230072969 + 3 ^ 40 * 1303347 * 2
def baseEnd_1303347 : Nat := 446162313730411588379015

theorem tailTrace_1303347 : CollatzResearch.WordTrace tailWord_1303347 prefixEnd_1303347 446162313730411588379015 := by
  unfold tailWord_1303347
  simp only [CollatzResearch.WordTrace]
  refine ⟨47536970409203887791100295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31691313606135925194066863 47536970409203887791100295)
  ·
    refine ⟨71305455613805831686650443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47536970409203887791100295 71305455613805831686650443)
    ·
      refine ⟨106958183420708747529975665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71305455613805831686650443 106958183420708747529975665)
      ·
        refine ⟨80218637565531560647481749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 106958183420708747529975665 80218637565531560647481749)
        ·
          refine ⟨3760248635884291905350707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 80218637565531560647481749 3760248635884291905350707)
          ·
            refine ⟨5640372953826437858026061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3760248635884291905350707 5640372953826437858026061)
            ·
              refine ⟨2115139857684914196759773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5640372953826437858026061 2115139857684914196759773)
              ·
                refine ⟨793177446631842823784915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2115139857684914196759773 793177446631842823784915)
                ·
                  refine ⟨1189766169947764235677373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793177446631842823784915 1189766169947764235677373)
                  ·
                    refine ⟨446162313730411588379015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1189766169947764235677373 446162313730411588379015)
                    ·
                      rfl

theorem cell22_1303347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 3, 1, 3].length) (baseStart_1303347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303347 prefixEnd_1303347 := by exact prefixLift 1303347
  have htrace : WordTrace (prefixWord ++ tailWord_1303347) baseStart_1303347 baseEnd_1303347 := by
    simpa [prefixWord, tailWord_1303347, baseEnd_1303347] using wordTrace_append hprefix tailTrace_1303347
  have hstable : (prefixWord ++ tailWord_1303347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303347).length < 2 ^ (prefixWord ++ tailWord_1303347).sum := by decide
  have hdescent : baseEnd_1303347 < baseStart_1303347 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303377 : List Nat := [1, 2, 2, 1, 6, 2, 2, 1, 5]
def baseStart_1303377 : Nat := 118140960795 + 1303377 * 2 ^ 59
def prefixEnd_1303377 : Nat := 4983230072969 + 3 ^ 40 * 1303377 * 2
def baseEnd_1303377 : Nat := 148724194447833836709641

theorem tailTrace_1303377 : CollatzResearch.WordTrace tailWord_1303377 prefixEnd_1303377 148724194447833836709641 := by
  unfold tailWord_1303377
  simp only [CollatzResearch.WordTrace]
  refine ⟨47538064599095202914692385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31692043066063468609794923 47538064599095202914692385)
  ·
    refine ⟨35653548449321402186019289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47538064599095202914692385 35653548449321402186019289)
    ·
      refine ⟨26740161336991051639514467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35653548449321402186019289 26740161336991051639514467)
      ·
        refine ⟨40110242005486577459271701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26740161336991051639514467 40110242005486577459271701)
        ·
          refine ⟨1880167594007183318403361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 40110242005486577459271701 1880167594007183318403361)
          ·
            refine ⟨1410125695505387488802521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1880167594007183318403361 1410125695505387488802521)
            ·
              refine ⟨1057594271629040616601891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1410125695505387488802521 1057594271629040616601891)
              ·
                refine ⟨1586391407443560924902837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1057594271629040616601891 1586391407443560924902837)
                ·
                  refine ⟨148724194447833836709641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1586391407443560924902837 148724194447833836709641)
                  ·
                    rfl

theorem cell22_1303377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 6, 2, 2, 1, 5].length) (baseStart_1303377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303377 prefixEnd_1303377 := by exact prefixLift 1303377
  have htrace : WordTrace (prefixWord ++ tailWord_1303377) baseStart_1303377 baseEnd_1303377 := by
    simpa [prefixWord, tailWord_1303377, baseEnd_1303377] using wordTrace_append hprefix tailTrace_1303377
  have hstable : (prefixWord ++ tailWord_1303377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303377).length < 2 ^ (prefixWord ++ tailWord_1303377).sum := by decide
  have hdescent : baseEnd_1303377 < baseStart_1303377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303403 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 6, 3]
def baseStart_1303403 : Nat := 118140960795 + 1303403 * 2 ^ 59
def prefixEnd_1303403 : Nat := 4983230072969 + 3 ^ 40 * 1303403 * 2
def baseEnd_1303403 : Nat := 446181483674846108978843

theorem tailTrace_1303403 : CollatzResearch.WordTrace tailWord_1303403 prefixEnd_1303403 446181483674846108978843 := by
  unfold tailWord_1303403
  simp only [CollatzResearch.WordTrace]
  refine ⟨47539012897001009355138863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31692675264667339570092575 47539012897001009355138863)
  ·
    refine ⟨71308519345501514032708295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47539012897001009355138863 71308519345501514032708295)
    ·
      refine ⟨106962779018252271049062443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71308519345501514032708295 106962779018252271049062443)
      ·
        refine ⟨160444168527378406573593665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106962779018252271049062443 160444168527378406573593665)
        ·
          refine ⟨120333126395533804930195249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 160444168527378406573593665 120333126395533804930195249)
          ·
            refine ⟨90249844796650353697646437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120333126395533804930195249 90249844796650353697646437)
            ·
              refine ⟨16921845899371941318308707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90249844796650353697646437 16921845899371941318308707)
              ·
                refine ⟨25382768849057911977463061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16921845899371941318308707 25382768849057911977463061)
                ·
                  refine ⟨1189817289799589623943581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25382768849057911977463061 1189817289799589623943581)
                  ·
                    refine ⟨446181483674846108978843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1189817289799589623943581 446181483674846108978843)
                    ·
                      rfl

theorem cell22_1303403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 6, 3].length) (baseStart_1303403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303403 prefixEnd_1303403 := by exact prefixLift 1303403
  have htrace : WordTrace (prefixWord ++ tailWord_1303403) baseStart_1303403 baseEnd_1303403 := by
    simpa [prefixWord, tailWord_1303403, baseEnd_1303403] using wordTrace_append hprefix tailTrace_1303403
  have hstable : (prefixWord ++ tailWord_1303403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303403).length < 2 ^ (prefixWord ++ tailWord_1303403).sum := by decide
  have hdescent : baseEnd_1303403 < baseStart_1303403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303405 : List Nat := [1, 5, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1303405 : Nat := 118140960795 + 1303405 * 2 ^ 59
def prefixEnd_1303405 : Nat := 4983230072969 + 3 ^ 40 * 1303405 * 2
def baseEnd_1303405 : Nat := 148727389438572923476279

theorem tailTrace_1303405 : CollatzResearch.WordTrace tailWord_1303405 prefixEnd_1303405 148727389438572923476279 := by
  unfold tailWord_1303405
  simp only [CollatzResearch.WordTrace]
  refine ⟨47539085842993763696711669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31692723895329175797807779 47539085842993763696711669)
  ·
    refine ⟨4456789297780665346566719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47539085842993763696711669 4456789297780665346566719)
    ·
      refine ⟨6685183946670998019850079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4456789297780665346566719 6685183946670998019850079)
      ·
        refine ⟨10027775920006497029775119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6685183946670998019850079 10027775920006497029775119)
        ·
          refine ⟨15041663880009745544662679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10027775920006497029775119 15041663880009745544662679)
          ·
            refine ⟨22562495820014618316994019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15041663880009745544662679 22562495820014618316994019)
            ·
              refine ⟨33843743730021927475491029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22562495820014618316994019 33843743730021927475491029)
              ·
                refine ⟨793212743672388925206821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33843743730021927475491029 793212743672388925206821)
                ·
                  refine ⟨148727389438572923476279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 793212743672388925206821 148727389438572923476279)
                  ·
                    rfl

theorem cell22_1303405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1303405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303405 prefixEnd_1303405 := by exact prefixLift 1303405
  have htrace : WordTrace (prefixWord ++ tailWord_1303405) baseStart_1303405 baseEnd_1303405 := by
    simpa [prefixWord, tailWord_1303405, baseEnd_1303405] using wordTrace_append hprefix tailTrace_1303405
  have hstable : (prefixWord ++ tailWord_1303405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303405).length < 2 ^ (prefixWord ++ tailWord_1303405).sum := by decide
  have hdescent : baseEnd_1303405 < baseStart_1303405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303433 : List Nat := [1, 2, 1, 1, 5, 2, 3, 7]
def baseStart_1303433 : Nat := 118140960795 + 1303433 * 2 ^ 59
def prefixEnd_1303433 : Nat := 4983230072969 + 3 ^ 40 * 1303433 * 2
def baseEnd_1303433 : Nat := 49576861476437336747639

theorem tailTrace_1303433 : CollatzResearch.WordTrace tailWord_1303433 prefixEnd_1303433 49576861476437336747639 := by
  unfold tailWord_1303433
  simp only [CollatzResearch.WordTrace]
  refine ⟨47540107086892324478730953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31693404724594882985820635 47540107086892324478730953)
  ·
    refine ⟨35655080315169243359048215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47540107086892324478730953 35655080315169243359048215)
    ·
      refine ⟨53482620472753865038572323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35655080315169243359048215 53482620472753865038572323)
      ·
        refine ⟨80223930709130797557858485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53482620472753865038572323 80223930709130797557858485)
        ·
          refine ⟨7520993503981012271049233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80223930709130797557858485 7520993503981012271049233)
          ·
            refine ⟨5640745127985759203286925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7520993503981012271049233 5640745127985759203286925)
            ·
              refine ⟨2115279422994659701232597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5640745127985759203286925 2115279422994659701232597)
              ·
                refine ⟨49576861476437336747639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2115279422994659701232597 49576861476437336747639)
                ·
                  rfl

theorem cell22_1303433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 7].length) (baseStart_1303433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303433 prefixEnd_1303433 := by exact prefixLift 1303433
  have htrace : WordTrace (prefixWord ++ tailWord_1303433) baseStart_1303433 baseEnd_1303433 := by
    simpa [prefixWord, tailWord_1303433, baseEnd_1303433] using wordTrace_append hprefix tailTrace_1303433
  have hstable : (prefixWord ++ tailWord_1303433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303433).length < 2 ^ (prefixWord ++ tailWord_1303433).sum := by decide
  have hdescent : baseEnd_1303433 < baseStart_1303433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303482 : List Nat := [3, 1, 1, 1, 2, 1, 3, 6, 1, 3]
def baseStart_1303482 : Nat := 118140960795 + 1303482 * 2 ^ 59
def prefixEnd_1303482 : Nat := 4983230072969 + 3 ^ 40 * 1303482 * 2
def baseEnd_1303482 : Nat := 446208526989316236253601

theorem tailTrace_1303482 : CollatzResearch.WordTrace tailWord_1303482 prefixEnd_1303482 446208526989316236253601 := by
  unfold tailWord_1303482
  simp only [CollatzResearch.WordTrace]
  refine ⟨11885473565928701461816175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31694596175809870564843133 11885473565928701461816175)
  ·
    refine ⟨17828210348893052192724263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11885473565928701461816175 17828210348893052192724263)
    ·
      refine ⟨26742315523339578289086395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17828210348893052192724263 26742315523339578289086395)
      ·
        refine ⟨40113473285009367433629593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26742315523339578289086395 40113473285009367433629593)
        ·
          refine ⟨30085104963757025575222195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40113473285009367433629593 30085104963757025575222195)
          ·
            refine ⟨45127657445635538362833293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30085104963757025575222195 45127657445635538362833293)
            ·
              refine ⟨16922871542113326886062485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45127657445635538362833293 16922871542113326886062485)
              ·
                refine ⟨793259603536562197784179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16922871542113326886062485 793259603536562197784179)
                ·
                  refine ⟨1189889405304843296676269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793259603536562197784179 1189889405304843296676269)
                  ·
                    refine ⟨446208526989316236253601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1189889405304843296676269 446208526989316236253601)
                    ·
                      rfl

theorem cell22_1303482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 6, 1, 3].length) (baseStart_1303482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303482 prefixEnd_1303482 := by exact prefixLift 1303482
  have htrace : WordTrace (prefixWord ++ tailWord_1303482) baseStart_1303482 baseEnd_1303482 := by
    simpa [prefixWord, tailWord_1303482, baseEnd_1303482] using wordTrace_append hprefix tailTrace_1303482
  have hstable : (prefixWord ++ tailWord_1303482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303482).length < 2 ^ (prefixWord ++ tailWord_1303482).sum := by decide
  have hdescent : baseEnd_1303482 < baseStart_1303482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303591 : List Nat := [1, 1, 7, 1, 1, 1, 4, 2, 4]
def baseStart_1303591 : Nat := 118140960795 + 1303591 * 2 ^ 59
def prefixEnd_1303591 : Nat := 4983230072969 + 3 ^ 40 * 1303591 * 2
def baseEnd_1303591 : Nat := 148748613305625428426089

theorem tailTrace_1303591 : CollatzResearch.WordTrace tailWord_1303591 prefixEnd_1303591 148748613305625428426089 := by
  unfold tailWord_1303591
  simp only [CollatzResearch.WordTrace]
  refine ⟨47545869820319917462982627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31697246546879944975321751 47545869820319917462982627)
  ·
    refine ⟨71318804730479876194473941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47545869820319917462982627 71318804730479876194473941)
    ·
      refine ⟨1671534485870622098307983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 71318804730479876194473941 1671534485870622098307983)
      ·
        refine ⟨2507301728805933147461975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1671534485870622098307983 2507301728805933147461975)
        ·
          refine ⟨3760952593208899721192963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2507301728805933147461975 3760952593208899721192963)
          ·
            refine ⟨5641428889813349581789445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3760952593208899721192963 5641428889813349581789445)
            ·
              refine ⟨1057767916840003046585521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5641428889813349581789445 1057767916840003046585521)
              ·
                refine ⟨793325937630002284939141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1057767916840003046585521 793325937630002284939141)
                ·
                  refine ⟨148748613305625428426089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 793325937630002284939141 148748613305625428426089)
                  ·
                    rfl

theorem cell22_1303591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 2, 4].length) (baseStart_1303591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303591 prefixEnd_1303591 := by exact prefixLift 1303591
  have htrace : WordTrace (prefixWord ++ tailWord_1303591) baseStart_1303591 baseEnd_1303591 := by
    simpa [prefixWord, tailWord_1303591, baseEnd_1303591] using wordTrace_append hprefix tailTrace_1303591
  have hstable : (prefixWord ++ tailWord_1303591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303591).length < 2 ^ (prefixWord ++ tailWord_1303591).sum := by decide
  have hdescent : baseEnd_1303591 < baseStart_1303591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303630 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 7]
def baseStart_1303630 : Nat := 118140960795 + 1303630 * 2 ^ 59
def prefixEnd_1303630 : Nat := 4983230072969 + 3 ^ 40 * 1303630 * 2
def baseEnd_1303630 : Nat := 148753063471297727851049

theorem tailTrace_1303630 : CollatzResearch.WordTrace tailWord_1303630 prefixEnd_1303630 148753063471297727851049 := by
  unfold tailWord_1303630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5943411533397328390456543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31698194844785751415768229 5943411533397328390456543)
  ·
    refine ⟨8915117300095992585684815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5943411533397328390456543 8915117300095992585684815)
    ·
      refine ⟨13372675950143988878527223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8915117300095992585684815 13372675950143988878527223)
      ·
        refine ⟨20059013925215983317790835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13372675950143988878527223 20059013925215983317790835)
        ·
          refine ⟨30088520887823974976686253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20059013925215983317790835 30088520887823974976686253)
          ·
            refine ⟨11283195332933990616257345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30088520887823974976686253 11283195332933990616257345)
            ·
              refine ⟨8462396499700492962193009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11283195332933990616257345 8462396499700492962193009)
              ·
                refine ⟨6346797374775369721644757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8462396499700492962193009 6346797374775369721644757)
                ·
                  refine ⟨148753063471297727851049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6346797374775369721644757 148753063471297727851049)
                  ·
                    rfl

theorem cell22_1303630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_1303630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303630 prefixEnd_1303630 := by exact prefixLift 1303630
  have htrace : WordTrace (prefixWord ++ tailWord_1303630) baseStart_1303630 baseEnd_1303630 := by
    simpa [prefixWord, tailWord_1303630, baseEnd_1303630] using wordTrace_append hprefix tailTrace_1303630
  have hstable : (prefixWord ++ tailWord_1303630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303630).length < 2 ^ (prefixWord ++ tailWord_1303630).sum := by decide
  have hdescent : baseEnd_1303630 < baseStart_1303630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303662 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 2, 5]
def baseStart_1303662 : Nat := 118140960795 + 1303662 * 2 ^ 59
def prefixEnd_1303662 : Nat := 4983230072969 + 3 ^ 40 * 1303662 * 2
def baseEnd_1303662 : Nat := 446270144667855766753049

theorem tailTrace_1303662 : CollatzResearch.WordTrace tailWord_1303662 prefixEnd_1303662 446270144667855766753049 := by
  unfold tailWord_1303662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5943557425382837073602155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31698972935375131059211493 5943557425382837073602155)
  ·
    refine ⟨8915336138074255610403233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5943557425382837073602155 8915336138074255610403233)
    ·
      refine ⟨6686502103555691707802425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8915336138074255610403233 6686502103555691707802425)
      ·
        refine ⟨5014876577666768780851819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6686502103555691707802425 5014876577666768780851819)
        ·
          refine ⟨7522314866500153171277729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5014876577666768780851819 7522314866500153171277729)
          ·
            refine ⟨5641736149875114878458297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7522314866500153171277729 5641736149875114878458297)
            ·
              refine ⟨4231302112406336158843723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5641736149875114878458297 4231302112406336158843723)
              ·
                refine ⟨6346953168609504238265585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4231302112406336158843723 6346953168609504238265585)
                ·
                  refine ⟨4760214876457128178699189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6346953168609504238265585 4760214876457128178699189)
                  ·
                    refine ⟨446270144667855766753049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4760214876457128178699189 446270144667855766753049)
                    ·
                      rfl

theorem cell22_1303662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 2, 5].length) (baseStart_1303662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303662 prefixEnd_1303662 := by exact prefixLift 1303662
  have htrace : WordTrace (prefixWord ++ tailWord_1303662) baseStart_1303662 baseEnd_1303662 := by
    simpa [prefixWord, tailWord_1303662, baseEnd_1303662] using wordTrace_append hprefix tailTrace_1303662
  have hstable : (prefixWord ++ tailWord_1303662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303662).length < 2 ^ (prefixWord ++ tailWord_1303662).sum := by decide
  have hdescent : baseEnd_1303662 < baseStart_1303662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303694 : List Nat := [4, 1, 1, 3, 2, 1, 2, 3, 1, 4]
def baseStart_1303694 : Nat := 118140960795 + 1303694 * 2 ^ 59
def prefixEnd_1303694 : Nat := 4983230072969 + 3 ^ 40 * 1303694 * 2
def baseEnd_1303694 : Nat := 446281098921818349952951

theorem tailTrace_1303694 : CollatzResearch.WordTrace tailWord_1303694 prefixEnd_1303694 446281098921818349952951 := by
  unfold tailWord_1303694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5943703317368345756747767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31699751025964510702654757 5943703317368345756747767)
  ·
    refine ⟨8915554976052518635121651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5943703317368345756747767 8915554976052518635121651)
    ·
      refine ⟨13373332464078777952682477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8915554976052518635121651 13373332464078777952682477)
      ·
        refine ⟨5014999674029541732255929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13373332464078777952682477 5014999674029541732255929)
        ·
          refine ⟨3761249755522156299191947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5014999674029541732255929 3761249755522156299191947)
          ·
            refine ⟨5641874633283234448787921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761249755522156299191947 5641874633283234448787921)
            ·
              refine ⟨4231405974962425836590941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5641874633283234448787921 4231405974962425836590941)
              ·
                refine ⟨1586777240610909688721603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4231405974962425836590941 1586777240610909688721603)
                ·
                  refine ⟨2380165860916364533082405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1586777240610909688721603 2380165860916364533082405)
                  ·
                    refine ⟨446281098921818349952951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2380165860916364533082405 446281098921818349952951)
                    ·
                      rfl

theorem cell22_1303694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 3, 1, 4].length) (baseStart_1303694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303694 prefixEnd_1303694 := by exact prefixLift 1303694
  have htrace : WordTrace (prefixWord ++ tailWord_1303694) baseStart_1303694 baseEnd_1303694 := by
    simpa [prefixWord, tailWord_1303694, baseEnd_1303694] using wordTrace_append hprefix tailTrace_1303694
  have hstable : (prefixWord ++ tailWord_1303694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303694).length < 2 ^ (prefixWord ++ tailWord_1303694).sum := by decide
  have hdescent : baseEnd_1303694 < baseStart_1303694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303816 : List Nat := [2, 1, 3, 2, 4, 2, 1, 2, 5]
def baseStart_1303816 : Nat := 118140960795 + 1303816 * 2 ^ 59
def prefixEnd_1303816 : Nat := 4983230072969 + 3 ^ 40 * 1303816 * 2
def baseEnd_1303816 : Nat := 148774287338350232800859

theorem tailTrace_1303816 : CollatzResearch.WordTrace tailWord_1303816 prefixEnd_1303816 148774287338350232800859 := by
  unfold tailWord_1303816
  simp only [CollatzResearch.WordTrace]
  refine ⟨23777038122252390444961651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31702717496336520593282201 23777038122252390444961651)
  ·
    refine ⟨35665557183378585667442477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23777038122252390444961651 35665557183378585667442477)
    ·
      refine ⟨13374583943766969625290929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35665557183378585667442477 13374583943766969625290929)
      ·
        refine ⟨10030937957825227218968197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13374583943766969625290929 10030937957825227218968197)
        ·
          refine ⟨1880800867092230103556537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10030937957825227218968197 1880800867092230103556537)
          ·
            refine ⟨1410600650319172577667403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1880800867092230103556537 1410600650319172577667403)
            ·
              refine ⟨2115900975478758866501105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410600650319172577667403 2115900975478758866501105)
              ·
                refine ⟨1586925731609069149875829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2115900975478758866501105 1586925731609069149875829)
                ·
                  refine ⟨148774287338350232800859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1586925731609069149875829 148774287338350232800859)
                  ·
                    rfl

theorem cell22_1303816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 2, 5].length) (baseStart_1303816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303816 prefixEnd_1303816 := by exact prefixLift 1303816
  have htrace : WordTrace (prefixWord ++ tailWord_1303816) baseStart_1303816 baseEnd_1303816 := by
    simpa [prefixWord, tailWord_1303816, baseEnd_1303816] using wordTrace_append hprefix tailTrace_1303816
  have hstable : (prefixWord ++ tailWord_1303816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303816).length < 2 ^ (prefixWord ++ tailWord_1303816).sum := by decide
  have hdescent : baseEnd_1303816 < baseStart_1303816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303859 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 4, 3]
def baseStart_1303859 : Nat := 118140960795 + 1303859 * 2 ^ 59
def prefixEnd_1303859 : Nat := 4983230072969 + 3 ^ 40 * 1303859 * 2
def baseEnd_1303859 : Nat := 446337581793812919577445

theorem tailTrace_1303859 : CollatzResearch.WordTrace tailWord_1303859 prefixEnd_1303859 446337581793812919577445 := by
  unfold tailWord_1303859
  simp only [CollatzResearch.WordTrace]
  refine ⟨47555644583348999233738631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31703763055565999489159087 47555644583348999233738631)
  ·
    refine ⟨71333466875023498850607947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47555644583348999233738631 71333466875023498850607947)
    ·
      refine ⟨107000200312535248275911921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71333466875023498850607947 107000200312535248275911921)
      ·
        refine ⟨80250150234401436206933941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107000200312535248275911921 80250150234401436206933941)
        ·
          refine ⟨7523451584475134644400057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 80250150234401436206933941 7523451584475134644400057)
          ·
            refine ⟨5642588688356350983300043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7523451584475134644400057 5642588688356350983300043)
            ·
              refine ⟨8463883032534526474950065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5642588688356350983300043 8463883032534526474950065)
              ·
                refine ⟨6347912274400894856212549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8463883032534526474950065 6347912274400894856212549)
                ·
                  refine ⟨1190233551450167785539853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6347912274400894856212549 1190233551450167785539853)
                  ·
                    refine ⟨446337581793812919577445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1190233551450167785539853 446337581793812919577445)
                    ·
                      rfl

theorem cell22_1303859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 4, 3].length) (baseStart_1303859 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303859 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303859 prefixEnd_1303859 := by exact prefixLift 1303859
  have htrace : WordTrace (prefixWord ++ tailWord_1303859) baseStart_1303859 baseEnd_1303859 := by
    simpa [prefixWord, tailWord_1303859, baseEnd_1303859] using wordTrace_append hprefix tailTrace_1303859
  have hstable : (prefixWord ++ tailWord_1303859).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303859).length < 2 ^ (prefixWord ++ tailWord_1303859).sum := by decide
  have hdescent : baseEnd_1303859 < baseStart_1303859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303861 : List Nat := [1, 3, 3, 1, 2, 2, 3, 3, 4]
def baseStart_1303861 : Nat := 118140960795 + 1303861 * 2 ^ 59
def prefixEnd_1303861 : Nat := 4983230072969 + 3 ^ 40 * 1303861 * 2
def baseEnd_1303861 : Nat := 148779422144895193675813

theorem tailTrace_1303861 : CollatzResearch.WordTrace tailWord_1303861 prefixEnd_1303861 148779422144895193675813 := by
  unfold tailWord_1303861
  simp only [CollatzResearch.WordTrace]
  refine ⟨47555717529341753575311437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31703811686227835716874291 47555717529341753575311437)
  ·
    refine ⟨17833394073503157590741789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47555717529341753575311437 17833394073503157590741789)
    ·
      refine ⟨6687522777563684096528171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17833394073503157590741789 6687522777563684096528171)
      ·
        refine ⟨10031284166345526144792257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6687522777563684096528171 10031284166345526144792257)
        ·
          refine ⟨7523463124759144608594193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10031284166345526144792257 7523463124759144608594193)
          ·
            refine ⟨5642597343569358456445645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7523463124759144608594193 5642597343569358456445645)
            ·
              refine ⟨2115974003838509421167117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5642597343569358456445645 2115974003838509421167117)
              ·
                refine ⟨793490251439441032937669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2115974003838509421167117 793490251439441032937669)
                ·
                  refine ⟨148779422144895193675813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 793490251439441032937669 148779422144895193675813)
                  ·
                    rfl

theorem cell22_1303861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_1303861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303861 prefixEnd_1303861 := by exact prefixLift 1303861
  have htrace : WordTrace (prefixWord ++ tailWord_1303861) baseStart_1303861 baseEnd_1303861 := by
    simpa [prefixWord, tailWord_1303861, baseEnd_1303861] using wordTrace_append hprefix tailTrace_1303861
  have hstable : (prefixWord ++ tailWord_1303861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303861).length < 2 ^ (prefixWord ++ tailWord_1303861).sum := by decide
  have hdescent : baseEnd_1303861 < baseStart_1303861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1303893 : List Nat := [1, 3, 2, 2, 3, 1, 4, 1, 2, 3]
def baseStart_1303893 : Nat := 118140960795 + 1303893 * 2 ^ 59
def prefixEnd_1303893 : Nat := 4983230072969 + 3 ^ 40 * 1303893 * 2
def baseEnd_1303893 : Nat := 446349220688648164227341

theorem tailTrace_1303893 : CollatzResearch.WordTrace tailWord_1303893 prefixEnd_1303893 446349220688648164227341 := by
  unfold tailWord_1303893
  simp only [CollatzResearch.WordTrace]
  refine ⟨47556884665225823040476333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31704589776817215360317555 47556884665225823040476333)
  ·
    refine ⟨17833831749459683640178625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47556884665225823040476333 17833831749459683640178625)
    ·
      refine ⟨13375373812094762730133969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17833831749459683640178625 13375373812094762730133969)
      ·
        refine ⟨10031530359071072047600477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13375373812094762730133969 10031530359071072047600477)
        ·
          refine ⟨3761823884651652017850179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10031530359071072047600477 3761823884651652017850179)
          ·
            refine ⟨5642735826977478026775269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3761823884651652017850179 5642735826977478026775269)
            ·
              refine ⟨1058012967558277130020363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5642735826977478026775269 1058012967558277130020363)
              ·
                refine ⟨1587019451337415695030545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058012967558277130020363 1587019451337415695030545)
                ·
                  refine ⟨1190264588503061771272909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1587019451337415695030545 1190264588503061771272909)
                  ·
                    refine ⟨446349220688648164227341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1190264588503061771272909 446349220688648164227341)
                    ·
                      rfl

theorem cell22_1303893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 1, 2, 3].length) (baseStart_1303893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1303893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1303893 prefixEnd_1303893 := by exact prefixLift 1303893
  have htrace : WordTrace (prefixWord ++ tailWord_1303893) baseStart_1303893 baseEnd_1303893 := by
    simpa [prefixWord, tailWord_1303893, baseEnd_1303893] using wordTrace_append hprefix tailTrace_1303893
  have hstable : (prefixWord ++ tailWord_1303893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1303893).length < 2 ^ (prefixWord ++ tailWord_1303893).sum := by decide
  have hdescent : baseEnd_1303893 < baseStart_1303893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1303893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304011 : List Nat := [1, 1, 1, 1, 3, 3, 2, 5, 2, 3]
def baseStart_1304011 : Nat := 118140960795 + 1304011 * 2 ^ 59
def prefixEnd_1304011 : Nat := 4983230072969 + 3 ^ 40 * 1304011 * 2
def baseEnd_1304011 : Nat := 446389614500135189776979

theorem tailTrace_1304011 : CollatzResearch.WordTrace tailWord_1304011 prefixEnd_1304011 446389614500135189776979 := by
  unfold tailWord_1304011
  simp only [CollatzResearch.WordTrace]
  refine ⟨47561188478798329193271887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31707458985865552795514591 47561188478798329193271887)
  ·
    refine ⟨71341782718197493789907831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47561188478798329193271887 71341782718197493789907831)
    ·
      refine ⟨107012674077296240684861747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71341782718197493789907831 107012674077296240684861747)
      ·
        refine ⟨160519011115944361027292621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107012674077296240684861747 160519011115944361027292621)
        ·
          refine ⟨60194629168479135385234733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160519011115944361027292621 60194629168479135385234733)
          ·
            refine ⟨22572985938179675769463025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60194629168479135385234733 22572985938179675769463025)
            ·
              refine ⟨16929739453634756827097269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22572985938179675769463025 16929739453634756827097269)
              ·
                refine ⟨1587163073778258452540369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16929739453634756827097269 1587163073778258452540369)
                ·
                  refine ⟨1190372305333693839405277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1587163073778258452540369 1190372305333693839405277)
                  ·
                    refine ⟨446389614500135189776979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1190372305333693839405277 446389614500135189776979)
                    ·
                      rfl

theorem cell22_1304011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 5, 2, 3].length) (baseStart_1304011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304011 prefixEnd_1304011 := by exact prefixLift 1304011
  have htrace : WordTrace (prefixWord ++ tailWord_1304011) baseStart_1304011 baseEnd_1304011 := by
    simpa [prefixWord, tailWord_1304011, baseEnd_1304011] using wordTrace_append hprefix tailTrace_1304011
  have hstable : (prefixWord ++ tailWord_1304011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304011).length < 2 ^ (prefixWord ++ tailWord_1304011).sum := by decide
  have hdescent : baseEnd_1304011 < baseStart_1304011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304062 : List Nat := [4, 2, 2, 3, 1, 1, 1, 3, 2, 3]
def baseStart_1304062 : Nat := 118140960795 + 1304062 * 2 ^ 59
def prefixEnd_1304062 : Nat := 4983230072969 + 3 ^ 40 * 1304062 * 2
def baseEnd_1304062 : Nat := 446407072842388056751823

theorem tailTrace_1304062 : CollatzResearch.WordTrace tailWord_1304062 prefixEnd_1304062 446407072842388056751823 := by
  unfold tailWord_1304062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5945381075201695612922305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31708699067742376602252293 5945381075201695612922305)
  ·
    refine ⟨4459035806401271709691729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5945381075201695612922305 4459035806401271709691729)
    ·
      refine ⟨3344276854800953782268797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4459035806401271709691729 3344276854800953782268797)
      ·
        refine ⟨1254103820550357668350799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3344276854800953782268797 1254103820550357668350799)
        ·
          refine ⟨1881155730825536502526199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254103820550357668350799 1881155730825536502526199)
          ·
            refine ⟨2821733596238304753789299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881155730825536502526199 2821733596238304753789299)
            ·
              refine ⟨4232600394357457130683949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821733596238304753789299 4232600394357457130683949)
              ·
                refine ⟨1587225147884046424006481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4232600394357457130683949 1587225147884046424006481)
                ·
                  refine ⟨1190418860913034818004861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1587225147884046424006481 1190418860913034818004861)
                  ·
                    refine ⟨446407072842388056751823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1190418860913034818004861 446407072842388056751823)
                    ·
                      rfl

theorem cell22_1304062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_1304062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304062 prefixEnd_1304062 := by exact prefixLift 1304062
  have htrace : WordTrace (prefixWord ++ tailWord_1304062) baseStart_1304062 baseEnd_1304062 := by
    simpa [prefixWord, tailWord_1304062, baseEnd_1304062] using wordTrace_append hprefix tailTrace_1304062
  have hstable : (prefixWord ++ tailWord_1304062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304062).length < 2 ^ (prefixWord ++ tailWord_1304062).sum := by decide
  have hdescent : baseEnd_1304062 < baseStart_1304062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304077 : List Nat := [1, 7, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_1304077 : Nat := 118140960795 + 1304077 * 2 ^ 59
def prefixEnd_1304077 : Nat := 4983230072969 + 3 ^ 40 * 1304077 * 2
def baseEnd_1304077 : Nat := 446412207648933017626777

theorem tailTrace_1304077 : CollatzResearch.WordTrace tailWord_1304077 prefixEnd_1304077 446412207648933017626777 := by
  unfold tailWord_1304077
  simp only [CollatzResearch.WordTrace]
  refine ⟨47563595696559222465174485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31709063797706148310116323 47563595696559222465174485)
  ·
    refine ⟨1114771774138106776527527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 47563595696559222465174485 1114771774138106776527527)
    ·
      refine ⟨1672157661207160164791291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1114771774138106776527527 1672157661207160164791291)
      ·
        refine ⟨2508236491810740247186937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1672157661207160164791291 2508236491810740247186937)
        ·
          refine ⟨1881177368858055185390203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2508236491810740247186937 1881177368858055185390203)
          ·
            refine ⟨2821766053287082778085305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881177368858055185390203 2821766053287082778085305)
            ·
              refine ⟨2116324539965312083563979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2821766053287082778085305 2116324539965312083563979)
              ·
                refine ⟨3174486809947968125345969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2116324539965312083563979 3174486809947968125345969)
                ·
                  refine ⟨2380865107460976094009477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3174486809947968125345969 2380865107460976094009477)
                  ·
                    refine ⟨446412207648933017626777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2380865107460976094009477 446412207648933017626777)
                    ·
                      rfl

theorem cell22_1304077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_1304077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304077 prefixEnd_1304077 := by exact prefixLift 1304077
  have htrace : WordTrace (prefixWord ++ tailWord_1304077) baseStart_1304077 baseEnd_1304077 := by
    simpa [prefixWord, tailWord_1304077, baseEnd_1304077] using wordTrace_append hprefix tailTrace_1304077
  have hstable : (prefixWord ++ tailWord_1304077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304077).length < 2 ^ (prefixWord ++ tailWord_1304077).sum := by decide
  have hdescent : baseEnd_1304077 < baseStart_1304077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304161 : List Nat := [1, 2, 3, 1, 1, 3, 2, 1, 4, 4]
def baseStart_1304161 : Nat := 118140960795 + 1304161 * 2 ^ 59
def prefixEnd_1304161 : Nat := 4983230072969 + 3 ^ 40 * 1304161 * 2
def baseEnd_1304161 : Nat := 446440962565584798526519

theorem tailTrace_1304161 : CollatzResearch.WordTrace tailWord_1304161 prefixEnd_1304161 446440962565584798526519 := by
  unfold tailWord_1304161
  simp only [CollatzResearch.WordTrace]
  refine ⟨47566659428254904811232337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31711106285503269874154891 47566659428254904811232337)
  ·
    refine ⟨35674994571191178608424253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47566659428254904811232337 35674994571191178608424253)
    ·
      refine ⟨13378122964196691978159095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35674994571191178608424253 13378122964196691978159095)
      ·
        refine ⟨20067184446295037967238643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13378122964196691978159095 20067184446295037967238643)
        ·
          refine ⟨30100776669442556950857965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20067184446295037967238643 30100776669442556950857965)
          ·
            refine ⟨11287791251040958856571737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30100776669442556950857965 11287791251040958856571737)
            ·
              refine ⟨8465843438280719142428803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11287791251040958856571737 8465843438280719142428803)
              ·
                refine ⟨12698765157421078713643205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8465843438280719142428803 12698765157421078713643205)
                ·
                  refine ⟨2381018467016452258808101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12698765157421078713643205 2381018467016452258808101)
                  ·
                    refine ⟨446440962565584798526519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2381018467016452258808101 446440962565584798526519)
                    ·
                      rfl

theorem cell22_1304161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_1304161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304161 prefixEnd_1304161 := by exact prefixLift 1304161
  have htrace : WordTrace (prefixWord ++ tailWord_1304161) baseStart_1304161 baseEnd_1304161 := by
    simpa [prefixWord, tailWord_1304161, baseEnd_1304161] using wordTrace_append hprefix tailTrace_1304161
  have hstable : (prefixWord ++ tailWord_1304161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304161).length < 2 ^ (prefixWord ++ tailWord_1304161).sum := by decide
  have hdescent : baseEnd_1304161 < baseStart_1304161 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304163 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 4, 3]
def baseStart_1304163 : Nat := 118140960795 + 1304163 * 2 ^ 59
def prefixEnd_1304163 : Nat := 4983230072969 + 3 ^ 40 * 1304163 * 2
def baseEnd_1304163 : Nat := 446441647206457459976513

theorem tailTrace_1304163 : CollatzResearch.WordTrace tailWord_1304163 prefixEnd_1304163 446441647206457459976513 := by
  unfold tailWord_1304163
  simp only [CollatzResearch.WordTrace]
  refine ⟨47566732374247659152805143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31711154916165106101870095 47566732374247659152805143)
  ·
    refine ⟨71350098561371488729207715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47566732374247659152805143 71350098561371488729207715)
    ·
      refine ⟨107025147842057233093811573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71350098561371488729207715 107025147842057233093811573)
      ·
        refine ⟨10033607610192865602544835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107025147842057233093811573 10033607610192865602544835)
        ·
          refine ⟨15050411415289298403817253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10033607610192865602544835 15050411415289298403817253)
          ·
            refine ⟨2821952140366743450715735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15050411415289298403817253 2821952140366743450715735)
            ·
              refine ⟨4232928210550115176073603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2821952140366743450715735 4232928210550115176073603)
              ·
                refine ⟨6349392315825172764110405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4232928210550115176073603 6349392315825172764110405)
                ·
                  refine ⟨1190511059217219893270701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6349392315825172764110405 1190511059217219893270701)
                  ·
                    refine ⟨446441647206457459976513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1190511059217219893270701 446441647206457459976513)
                    ·
                      rfl

theorem cell22_1304163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 4, 3].length) (baseStart_1304163 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304163 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304163 prefixEnd_1304163 := by exact prefixLift 1304163
  have htrace : WordTrace (prefixWord ++ tailWord_1304163) baseStart_1304163 baseEnd_1304163 := by
    simpa [prefixWord, tailWord_1304163, baseEnd_1304163] using wordTrace_append hprefix tailTrace_1304163
  have hstable : (prefixWord ++ tailWord_1304163).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304163).length < 2 ^ (prefixWord ++ tailWord_1304163).sum := by decide
  have hdescent : baseEnd_1304163 < baseStart_1304163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304193 : List Nat := [1, 2, 4, 2, 1, 2, 4, 6]
def baseStart_1304193 : Nat := 118140960795 + 1304193 * 2 ^ 59
def prefixEnd_1304193 : Nat := 4983230072969 + 3 ^ 40 * 1304193 * 2
def baseEnd_1304193 : Nat := 49605768535505264636269

theorem tailTrace_1304193 : CollatzResearch.WordTrace tailWord_1304193 prefixEnd_1304193 49605768535505264636269 := by
  unfold tailWord_1304193
  simp only [CollatzResearch.WordTrace]
  refine ⟨47567826564138974276397233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31711884376092649517598155 47567826564138974276397233)
  ·
    refine ⟨35675869923104230707297925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47567826564138974276397233 35675869923104230707297925)
    ·
      refine ⟨6689225610582043257618361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35675869923104230707297925 6689225610582043257618361)
      ·
        refine ⟨5016919207936532443213771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6689225610582043257618361 5016919207936532443213771)
        ·
          refine ⟨7525378811904798664820657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5016919207936532443213771 7525378811904798664820657)
          ·
            refine ⟨5644034108928598998615493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7525378811904798664820657 5644034108928598998615493)
            ·
              refine ⟨1058256395424112312240405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5644034108928598998615493 1058256395424112312240405)
              ·
                refine ⟨49605768535505264636269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1058256395424112312240405 49605768535505264636269)
                ·
                  rfl

theorem cell22_1304193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 4, 6].length) (baseStart_1304193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304193 prefixEnd_1304193 := by exact prefixLift 1304193
  have htrace : WordTrace (prefixWord ++ tailWord_1304193) baseStart_1304193 baseEnd_1304193 := by
    simpa [prefixWord, tailWord_1304193, baseEnd_1304193] using wordTrace_append hprefix tailTrace_1304193
  have hstable : (prefixWord ++ tailWord_1304193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304193).length < 2 ^ (prefixWord ++ tailWord_1304193).sum := by decide
  have hdescent : baseEnd_1304193 < baseStart_1304193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304210 : List Nat := [3, 2, 3, 1, 4, 1, 8]
def baseStart_1304210 : Nat := 118140960795 + 1304210 * 2 ^ 59
def prefixEnd_1304210 : Nat := 4983230072969 + 3 ^ 40 * 1304210 * 2
def baseEnd_1304210 : Nat := 16535471713591296446347

theorem tailTrace_1304210 : CollatzResearch.WordTrace tailWord_1304210 prefixEnd_1304210 16535471713591296446347 := by
  unfold tailWord_1304210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11892111651269346544941521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31712297736718257453177389 11892111651269346544941521)
  ·
    refine ⟨8919083738452009908706141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11892111651269346544941521 8919083738452009908706141)
    ·
      refine ⟨3344656401919503715764803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8919083738452009908706141 3344656401919503715764803)
      ·
        refine ⟨5016984602879255573647205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3344656401919503715764803 5016984602879255573647205)
        ·
          refine ⟨940684613039860420058851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5016984602879255573647205 940684613039860420058851)
          ·
            refine ⟨1411026919559790630088277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 940684613039860420058851 1411026919559790630088277)
            ·
              refine ⟨16535471713591296446347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1411026919559790630088277 16535471713591296446347)
              ·
                rfl

theorem cell22_1304210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 8].length) (baseStart_1304210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304210 prefixEnd_1304210 := by exact prefixLift 1304210
  have htrace : WordTrace (prefixWord ++ tailWord_1304210) baseStart_1304210 baseEnd_1304210 := by
    simpa [prefixWord, tailWord_1304210, baseEnd_1304210] using wordTrace_append hprefix tailTrace_1304210
  have hstable : (prefixWord ++ tailWord_1304210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304210).length < 2 ^ (prefixWord ++ tailWord_1304210).sum := by decide
  have hdescent : baseEnd_1304210 < baseStart_1304210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304225 : List Nat := [1, 2, 3, 3, 2, 1, 3, 1, 3, 3]
def baseStart_1304225 : Nat := 118140960795 + 1304225 * 2 ^ 59
def prefixEnd_1304225 : Nat := 4983230072969 + 3 ^ 40 * 1304225 * 2
def baseEnd_1304225 : Nat := 446462871073509964926323

theorem tailTrace_1304225 : CollatzResearch.WordTrace tailWord_1304225 prefixEnd_1304225 446462871073509964926323 := by
  unfold tailWord_1304225
  simp only [CollatzResearch.WordTrace]
  refine ⟨47568993700023043741562129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31712662466682029161041419 47568993700023043741562129)
  ·
    refine ⟨35676745275017282806171597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47568993700023043741562129 35676745275017282806171597)
    ·
      refine ⟨13378779478131481052314349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35676745275017282806171597 13378779478131481052314349)
      ·
        refine ⟨5017042304299305394617881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13378779478131481052314349 5017042304299305394617881)
        ·
          refine ⟨3762781728224479045963411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5017042304299305394617881 3762781728224479045963411)
          ·
            refine ⟨5644172592336718568945117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3762781728224479045963411 5644172592336718568945117)
            ·
              refine ⟨2116564722126269463354419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5644172592336718568945117 2116564722126269463354419)
              ·
                refine ⟨3174847083189404195031629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2116564722126269463354419 3174847083189404195031629)
                ·
                  refine ⟨1190567656196026573136861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3174847083189404195031629 1190567656196026573136861)
                  ·
                    refine ⟨446462871073509964926323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1190567656196026573136861 446462871073509964926323)
                    ·
                      rfl

theorem cell22_1304225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 3, 1, 3, 3].length) (baseStart_1304225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304225 prefixEnd_1304225 := by exact prefixLift 1304225
  have htrace : WordTrace (prefixWord ++ tailWord_1304225) baseStart_1304225 baseEnd_1304225 := by
    simpa [prefixWord, tailWord_1304225, baseEnd_1304225] using wordTrace_append hprefix tailTrace_1304225
  have hstable : (prefixWord ++ tailWord_1304225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304225).length < 2 ^ (prefixWord ++ tailWord_1304225).sum := by decide
  have hdescent : baseEnd_1304225 < baseStart_1304225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304276 : List Nat := [2, 4, 1, 3, 1, 3, 2, 2, 1, 3]
def baseStart_1304276 : Nat := 118140960795 + 1304276 * 2 ^ 59
def prefixEnd_1304276 : Nat := 4983230072969 + 3 ^ 40 * 1304276 * 2
def baseEnd_1304276 : Nat := 446480329415762831901167

theorem tailTrace_1304276 : CollatzResearch.WordTrace tailWord_1304276 prefixEnd_1304276 446480329415762831901167 := by
  unfold tailWord_1304276
  simp only [CollatzResearch.WordTrace]
  refine ⟨23785426911419139725834341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31713902548558852967779121 23785426911419139725834341)
  ·
    refine ⟨4459767545891088698593939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23785426911419139725834341 4459767545891088698593939)
    ·
      refine ⟨6689651318836633047890909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4459767545891088698593939 6689651318836633047890909)
      ·
        refine ⟨2508619244563737392959091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6689651318836633047890909 2508619244563737392959091)
        ·
          refine ⟨3762928866845606089438637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2508619244563737392959091 3762928866845606089438637)
          ·
            refine ⟨1411098325067102283539489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3762928866845606089438637 1411098325067102283539489)
            ·
              refine ⟨1058323743800326712654617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1411098325067102283539489 1058323743800326712654617)
              ·
                refine ⟨793742807850245034490963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058323743800326712654617 793742807850245034490963)
                ·
                  refine ⟨1190614211775367551736445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793742807850245034490963 1190614211775367551736445)
                  ·
                    refine ⟨446480329415762831901167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1190614211775367551736445 446480329415762831901167)
                    ·
                      rfl

theorem cell22_1304276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_1304276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304276 prefixEnd_1304276 := by exact prefixLift 1304276
  have htrace : WordTrace (prefixWord ++ tailWord_1304276) baseStart_1304276 baseEnd_1304276 := by
    simpa [prefixWord, tailWord_1304276, baseEnd_1304276] using wordTrace_append hprefix tailTrace_1304276
  have hstable : (prefixWord ++ tailWord_1304276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304276).length < 2 ^ (prefixWord ++ tailWord_1304276).sum := by decide
  have hdescent : baseEnd_1304276 < baseStart_1304276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304298 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 1, 5]
def baseStart_1304298 : Nat := 118140960795 + 1304298 * 2 ^ 59
def prefixEnd_1304298 : Nat := 4983230072969 + 3 ^ 40 * 1304298 * 2
def baseEnd_1304298 : Nat := 446487860465362107851099

theorem tailTrace_1304298 : CollatzResearch.WordTrace tailWord_1304298 prefixEnd_1304298 446487860465362107851099 := by
  unfold tailWord_1304298
  simp only [CollatzResearch.WordTrace]
  refine ⟨11892914057189644302242387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31714437485839051472646365 11892914057189644302242387)
  ·
    refine ⟨17839371085784466453363581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11892914057189644302242387 17839371085784466453363581)
    ·
      refine ⟨6689764157169174920011343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17839371085784466453363581 6689764157169174920011343)
      ·
        refine ⟨10034646235753762380017015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6689764157169174920011343 10034646235753762380017015)
        ·
          refine ⟨15051969353630643570025523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10034646235753762380017015 15051969353630643570025523)
          ·
            refine ⟨22577954030445965355038285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15051969353630643570025523 22577954030445965355038285)
            ·
              refine ⟨8466732761417237008139357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22577954030445965355038285 8466732761417237008139357)
              ·
                refine ⟨3175024785531463878052259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8466732761417237008139357 3175024785531463878052259)
                ·
                  refine ⟨4762537178297195817078389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3175024785531463878052259 4762537178297195817078389)
                  ·
                    refine ⟨446487860465362107851099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4762537178297195817078389 446487860465362107851099)
                    ·
                      rfl

theorem cell22_1304298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_1304298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304298 prefixEnd_1304298 := by exact prefixLift 1304298
  have htrace : WordTrace (prefixWord ++ tailWord_1304298) baseStart_1304298 baseEnd_1304298 := by
    simpa [prefixWord, tailWord_1304298, baseEnd_1304298] using wordTrace_append hprefix tailTrace_1304298
  have hstable : (prefixWord ++ tailWord_1304298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304298).length < 2 ^ (prefixWord ++ tailWord_1304298).sum := by decide
  have hdescent : baseEnd_1304298 < baseStart_1304298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304311 : List Nat := [1, 1, 3, 1, 1, 1, 4, 10]
def baseStart_1304311 : Nat := 118140960795 + 1304311 * 2 ^ 59
def prefixEnd_1304311 : Nat := 4983230072969 + 3 ^ 40 * 1304311 * 2
def baseEnd_1304311 : Nat := 49610256736781600808451

theorem tailTrace_1304311 : CollatzResearch.WordTrace tailWord_1304311 prefixEnd_1304311 49610256736781600808451 := by
  unfold tailWord_1304311
  simp only [CollatzResearch.WordTrace]
  refine ⟨47572130377711480429192787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31714753585140986952795191 47572130377711480429192787)
  ·
    refine ⟨71358195566567220643789181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47572130377711480429192787 71358195566567220643789181)
    ·
      refine ⟨26759323337462707741420943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71358195566567220643789181 26759323337462707741420943)
      ·
        refine ⟨40138985006194061612131415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26759323337462707741420943 40138985006194061612131415)
        ·
          refine ⟨60208477509291092418197123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40138985006194061612131415 60208477509291092418197123)
          ·
            refine ⟨90312716263936638627295685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60208477509291092418197123 90312716263936638627295685)
            ·
              refine ⟨16933634299488119742617941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 90312716263936638627295685 16933634299488119742617941)
              ·
                refine ⟨49610256736781600808451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 16933634299488119742617941 49610256736781600808451)
                ·
                  rfl

theorem cell22_1304311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 10].length) (baseStart_1304311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304311 prefixEnd_1304311 := by exact prefixLift 1304311
  have htrace : WordTrace (prefixWord ++ tailWord_1304311) baseStart_1304311 baseEnd_1304311 := by
    simpa [prefixWord, tailWord_1304311, baseEnd_1304311] using wordTrace_append hprefix tailTrace_1304311
  have hstable : (prefixWord ++ tailWord_1304311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304311).length < 2 ^ (prefixWord ++ tailWord_1304311).sum := by decide
  have hdescent : baseEnd_1304311 < baseStart_1304311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304394 : List Nat := [3, 1, 2, 1, 1, 1, 7, 2, 1, 3]
def baseStart_1304394 : Nat := 118140960795 + 1304394 * 2 ^ 59
def prefixEnd_1304394 : Nat := 4983230072969 + 3 ^ 40 * 1304394 * 2
def baseEnd_1304394 : Nat := 446520723227249857450805

theorem tailTrace_1304394 : CollatzResearch.WordTrace tailWord_1304394 prefixEnd_1304394 446520723227249857450805 := by
  unfold tailWord_1304394
  simp only [CollatzResearch.WordTrace]
  refine ⟨11893789409102696401116059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31716771757607190402976157 11893789409102696401116059)
  ·
    refine ⟨17840684113654044601674089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11893789409102696401116059 17840684113654044601674089)
    ·
      refine ⟨13380513085240533451255567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17840684113654044601674089 13380513085240533451255567)
      ·
        refine ⟨20070769627860800176883351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13380513085240533451255567 20070769627860800176883351)
        ·
          refine ⟨30106154441791200265325027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20070769627860800176883351 30106154441791200265325027)
          ·
            refine ⟨45159231662686800397987541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30106154441791200265325027 45159231662686800397987541)
            ·
              refine ⟨1058419492094221884327833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 45159231662686800397987541 1058419492094221884327833)
              ·
                refine ⟨793814619070666413245875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058419492094221884327833 793814619070666413245875)
                ·
                  refine ⟨1190721928605999619868813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 793814619070666413245875 1190721928605999619868813)
                  ·
                    refine ⟨446520723227249857450805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1190721928605999619868813 446520723227249857450805)
                    ·
                      rfl

theorem cell22_1304394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_1304394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304394 prefixEnd_1304394 := by exact prefixLift 1304394
  have htrace : WordTrace (prefixWord ++ tailWord_1304394) baseStart_1304394 baseEnd_1304394 := by
    simpa [prefixWord, tailWord_1304394, baseEnd_1304394] using wordTrace_append hprefix tailTrace_1304394
  have hstable : (prefixWord ++ tailWord_1304394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304394).length < 2 ^ (prefixWord ++ tailWord_1304394).sum := by decide
  have hdescent : baseEnd_1304394 < baseStart_1304394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304435 : List Nat := [1, 1, 1, 2, 2, 1, 3, 7, 4]
def baseStart_1304435 : Nat := 118140960795 + 1304435 * 2 ^ 59
def prefixEnd_1304435 : Nat := 4983230072969 + 3 ^ 40 * 1304435 * 2
def baseEnd_1304435 : Nat := 148844919455046472391893

theorem tailTrace_1304435 : CollatzResearch.WordTrace tailWord_1304435 prefixEnd_1304435 148844919455046472391893 := by
  unfold tailWord_1304435
  simp only [CollatzResearch.WordTrace]
  refine ⟨47576653029262249606706759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31717768686174833071137839 47576653029262249606706759)
  ·
    refine ⟨71364979543893374410060139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47576653029262249606706759 71364979543893374410060139)
    ·
      refine ⟨107047469315840061615090209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71364979543893374410060139 107047469315840061615090209)
      ·
        refine ⟨80285601986880046211317657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107047469315840061615090209 80285601986880046211317657)
        ·
          refine ⟨60214201490160034658488243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80285601986880046211317657 60214201490160034658488243)
          ·
            refine ⟨90321302235240051987732365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60214201490160034658488243 90321302235240051987732365)
            ·
              refine ⟨33870488338215019495399637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 90321302235240051987732365 33870488338215019495399637)
              ·
                refine ⟨793839570426914519423429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 33870488338215019495399637 793839570426914519423429)
                ·
                  refine ⟨148844919455046472391893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 793839570426914519423429 148844919455046472391893)
                  ·
                    rfl

theorem cell22_1304435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 7, 4].length) (baseStart_1304435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304435 prefixEnd_1304435 := by exact prefixLift 1304435
  have htrace : WordTrace (prefixWord ++ tailWord_1304435) baseStart_1304435 baseEnd_1304435 := by
    simpa [prefixWord, tailWord_1304435, baseEnd_1304435] using wordTrace_append hprefix tailTrace_1304435
  have hstable : (prefixWord ++ tailWord_1304435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304435).length < 2 ^ (prefixWord ++ tailWord_1304435).sum := by decide
  have hdescent : baseEnd_1304435 < baseStart_1304435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304482 : List Nat := [3, 3, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_1304482 : Nat := 118140960795 + 1304482 * 2 ^ 59
def prefixEnd_1304482 : Nat := 4983230072969 + 3 ^ 40 * 1304482 * 2
def baseEnd_1304482 : Nat := 446550847425646961250535

theorem tailTrace_1304482 : CollatzResearch.WordTrace tailWord_1304482 prefixEnd_1304482 446550847425646961250535 := by
  unfold tailWord_1304482
  simp only [CollatzResearch.WordTrace]
  refine ⟨11894591815022994158416925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31718911506727984422445133 11894591815022994158416925)
  ·
    refine ⟨4460471930633622809406347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11894591815022994158416925 4460471930633622809406347)
    ·
      refine ⟨6690707895950434214109521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4460471930633622809406347 6690707895950434214109521)
      ·
        refine ⟨5018030921962825660582141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6690707895950434214109521 5018030921962825660582141)
        ·
          refine ⟨1881761595736059622718303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5018030921962825660582141 1881761595736059622718303)
          ·
            refine ⟨2822642393604089434077455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1881761595736059622718303 2822642393604089434077455)
            ·
              refine ⟨4233963590406134151116183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822642393604089434077455 4233963590406134151116183)
              ·
                refine ⟨6350945385609201226674275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4233963590406134151116183 6350945385609201226674275)
                ·
                  refine ⟨9526418078413801840011413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6350945385609201226674275 9526418078413801840011413)
                  ·
                    refine ⟨446550847425646961250535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9526418078413801840011413 446550847425646961250535)
                    ·
                      rfl

theorem cell22_1304482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_1304482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304482 prefixEnd_1304482 := by exact prefixLift 1304482
  have htrace : WordTrace (prefixWord ++ tailWord_1304482) baseStart_1304482 baseEnd_1304482 := by
    simpa [prefixWord, tailWord_1304482, baseEnd_1304482] using wordTrace_append hprefix tailTrace_1304482
  have hstable : (prefixWord ++ tailWord_1304482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304482).length < 2 ^ (prefixWord ++ tailWord_1304482).sum := by decide
  have hdescent : baseEnd_1304482 < baseStart_1304482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304488 : List Nat := [2, 1, 6, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1304488 : Nat := 118140960795 + 1304488 * 2 ^ 59
def prefixEnd_1304488 : Nat := 4983230072969 + 3 ^ 40 * 1304488 * 2
def baseEnd_1304488 : Nat := 446552901348264945600517

theorem tailTrace_1304488 : CollatzResearch.WordTrace tailWord_1304488 prefixEnd_1304488 446552901348264945600517 := by
  unfold tailWord_1304488
  simp only [CollatzResearch.WordTrace]
  refine ⟨23789293049035119829193059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31719057398713493105590745 23789293049035119829193059)
  ·
    refine ⟨35683939573552679743789589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23789293049035119829193059 35683939573552679743789589)
    ·
      refine ⟨1672684667510281862990137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 35683939573552679743789589 1672684667510281862990137)
      ·
        refine ⟨1254513500632711397242603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1672684667510281862990137 1254513500632711397242603)
        ·
          refine ⟨1881770250949067095863905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1254513500632711397242603 1881770250949067095863905)
          ·
            refine ⟨1411327688211800321897929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1881770250949067095863905 1411327688211800321897929)
            ·
              refine ⟨1058495766158850241423447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1411327688211800321897929 1058495766158850241423447)
              ·
                refine ⟨1587743649238275362135171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1058495766158850241423447 1587743649238275362135171)
                ·
                  refine ⟨2381615473857413043202757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1587743649238275362135171 2381615473857413043202757)
                  ·
                    refine ⟨446552901348264945600517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2381615473857413043202757 446552901348264945600517)
                    ·
                      rfl

theorem cell22_1304488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1304488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304488 prefixEnd_1304488 := by exact prefixLift 1304488
  have htrace : WordTrace (prefixWord ++ tailWord_1304488) baseStart_1304488 baseEnd_1304488 := by
    simpa [prefixWord, tailWord_1304488, baseEnd_1304488] using wordTrace_append hprefix tailTrace_1304488
  have hstable : (prefixWord ++ tailWord_1304488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304488).length < 2 ^ (prefixWord ++ tailWord_1304488).sum := by decide
  have hdescent : baseEnd_1304488 < baseStart_1304488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304495 : List Nat := [1, 1, 2, 1, 2, 2, 3, 2, 5, 3]
def baseStart_1304495 : Nat := 118140960795 + 1304495 * 2 ^ 59
def prefixEnd_1304495 : Nat := 4983230072969 + 3 ^ 40 * 1304495 * 2
def baseEnd_1304495 : Nat := 446555297591319260675495

theorem tailTrace_1304495 : CollatzResearch.WordTrace tailWord_1304495 prefixEnd_1304495 446555297591319260675495 := by
  unfold tailWord_1304495
  simp only [CollatzResearch.WordTrace]
  refine ⟨47578841409044879853890939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31719227606029919902593959 47578841409044879853890939)
  ·
    refine ⟨71368262113567319780836409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47578841409044879853890939 71368262113567319780836409)
    ·
      refine ⟨53526196585175489835627307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71368262113567319780836409 53526196585175489835627307)
      ·
        refine ⟨80289294877763234753440961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53526196585175489835627307 80289294877763234753440961)
        ·
          refine ⟨60216971158322426065080721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80289294877763234753440961 60216971158322426065080721)
          ·
            refine ⟨45162728368741819548810541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60216971158322426065080721 45162728368741819548810541)
            ·
              refine ⟨16936023138278182330803953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45162728368741819548810541 16936023138278182330803953)
              ·
                refine ⟨12702017353708636748102965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16936023138278182330803953 12702017353708636748102965)
                ·
                  refine ⟨1190814126910184695134653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12702017353708636748102965 1190814126910184695134653)
                  ·
                    refine ⟨446555297591319260675495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1190814126910184695134653 446555297591319260675495)
                    ·
                      rfl

theorem cell22_1304495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 2, 5, 3].length) (baseStart_1304495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304495 prefixEnd_1304495 := by exact prefixLift 1304495
  have htrace : WordTrace (prefixWord ++ tailWord_1304495) baseStart_1304495 baseEnd_1304495 := by
    simpa [prefixWord, tailWord_1304495, baseEnd_1304495] using wordTrace_append hprefix tailTrace_1304495
  have hstable : (prefixWord ++ tailWord_1304495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304495).length < 2 ^ (prefixWord ++ tailWord_1304495).sum := by decide
  have hdescent : baseEnd_1304495 < baseStart_1304495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304512 : List Nat := [2, 1, 1, 2, 3, 2, 4, 1, 3, 3]
def baseStart_1304512 : Nat := 118140960795 + 1304512 * 2 ^ 59
def prefixEnd_1304512 : Nat := 4983230072969 + 3 ^ 40 * 1304512 * 2
def baseEnd_1304512 : Nat := 446561117038736883000443

theorem tailTrace_1304512 : CollatzResearch.WordTrace tailWord_1304512 prefixEnd_1304512 446561117038736883000443 := by
  unfold tailWord_1304512
  simp only [CollatzResearch.WordTrace]
  refine ⟨23789730724991645878629895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31719640966655527838173193 23789730724991645878629895)
  ·
    refine ⟨35684596087487468817944843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23789730724991645878629895 35684596087487468817944843)
    ·
      refine ⟨53526894131231203226917265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35684596087487468817944843 53526894131231203226917265)
      ·
        refine ⟨40145170598423402420187949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53526894131231203226917265 40145170598423402420187949)
        ·
          refine ⟨15054438974408775907570481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40145170598423402420187949 15054438974408775907570481)
          ·
            refine ⟨11290829230806581930677861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15054438974408775907570481 11290829230806581930677861)
            ·
              refine ⟨2117030480776234112002099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11290829230806581930677861 2117030480776234112002099)
              ·
                refine ⟨3175545721164351168003149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2117030480776234112002099 3175545721164351168003149)
                ·
                  refine ⟨1190829645436631688001181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3175545721164351168003149 1190829645436631688001181)
                  ·
                    refine ⟨446561117038736883000443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1190829645436631688001181 446561117038736883000443)
                    ·
                      rfl

theorem cell22_1304512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 4, 1, 3, 3].length) (baseStart_1304512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304512 prefixEnd_1304512 := by exact prefixLift 1304512
  have htrace : WordTrace (prefixWord ++ tailWord_1304512) baseStart_1304512 baseEnd_1304512 := by
    simpa [prefixWord, tailWord_1304512, baseEnd_1304512] using wordTrace_append hprefix tailTrace_1304512
  have hstable : (prefixWord ++ tailWord_1304512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304512).length < 2 ^ (prefixWord ++ tailWord_1304512).sum := by decide
  have hdescent : baseEnd_1304512 < baseStart_1304512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304602 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 1, 5]
def baseStart_1304602 : Nat := 118140960795 + 1304602 * 2 ^ 59
def prefixEnd_1304602 : Nat := 4983230072969 + 3 ^ 40 * 1304602 * 2
def baseEnd_1304602 : Nat := 446591925878006648250167

theorem tailTrace_1304602 : CollatzResearch.WordTrace tailWord_1304602 prefixEnd_1304602 446591925878006648250167 := by
  unfold tailWord_1304602
  simp only [CollatzResearch.WordTrace]
  refine ⟨11895686004914309282009015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31721829346438158085357373 11895686004914309282009015)
  ·
    refine ⟨17843529007371463923013523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11895686004914309282009015 17843529007371463923013523)
    ·
      refine ⟨26765293511057195884520285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17843529007371463923013523 26765293511057195884520285)
      ·
        refine ⟨10036985066646448456695107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26765293511057195884520285 10036985066646448456695107)
        ·
          refine ⟨15055477599969672685042661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10036985066646448456695107 15055477599969672685042661)
          ·
            refine ⟨2822902049994313628445499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15055477599969672685042661 2822902049994313628445499)
            ·
              refine ⟨4234353074991470442668249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2822902049994313628445499 4234353074991470442668249)
              ·
                refine ⟨3175764806243602832001187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4234353074991470442668249 3175764806243602832001187)
                ·
                  refine ⟨4763647209365404248001781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3175764806243602832001187 4763647209365404248001781)
                  ·
                    refine ⟨446591925878006648250167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4763647209365404248001781 446591925878006648250167)
                    ·
                      rfl

theorem cell22_1304602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 1, 5].length) (baseStart_1304602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304602 prefixEnd_1304602 := by exact prefixLift 1304602
  have htrace : WordTrace (prefixWord ++ tailWord_1304602) baseStart_1304602 baseEnd_1304602 := by
    simpa [prefixWord, tailWord_1304602, baseEnd_1304602] using wordTrace_append hprefix tailTrace_1304602
  have hstable : (prefixWord ++ tailWord_1304602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304602).length < 2 ^ (prefixWord ++ tailWord_1304602).sum := by decide
  have hdescent : baseEnd_1304602 < baseStart_1304602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304645 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 4, 6]
def baseStart_1304645 : Nat := 118140960795 + 1304645 * 2 ^ 59
def prefixEnd_1304645 : Nat := 4983230072969 + 3 ^ 40 * 1304645 * 2
def baseEnd_1304645 : Nat := 446606645656768869425035

theorem tailTrace_1304645 : CollatzResearch.WordTrace tailWord_1304645 prefixEnd_1304645 446606645656768869425035 := by
  unfold tailWord_1304645
  simp only [CollatzResearch.WordTrace]
  refine ⟨47584312358501455471851389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31722874905667636981234259 47584312358501455471851389)
  ·
    refine ⟨17844117134438045801944271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47584312358501455471851389 17844117134438045801944271)
    ·
      refine ⟨26766175701657068702916407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17844117134438045801944271 26766175701657068702916407)
      ·
        refine ⟨40149263552485603054374611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26766175701657068702916407 40149263552485603054374611)
        ·
          refine ⟨60223895328728404581561917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40149263552485603054374611 60223895328728404581561917)
          ·
            refine ⟨22583960748273151718085719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60223895328728404581561917 22583960748273151718085719)
            ·
              refine ⟨33875941122409727577128579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22583960748273151718085719 33875941122409727577128579)
              ·
                refine ⟨50813911683614591365692869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33875941122409727577128579 50813911683614591365692869)
                ·
                  refine ⟨9527608440677735881067413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 50813911683614591365692869 9527608440677735881067413)
                  ·
                    refine ⟨446606645656768869425035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9527608440677735881067413 446606645656768869425035)
                    ·
                      rfl

theorem cell22_1304645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 4, 6].length) (baseStart_1304645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304645 prefixEnd_1304645 := by exact prefixLift 1304645
  have htrace : WordTrace (prefixWord ++ tailWord_1304645) baseStart_1304645 baseEnd_1304645 := by
    simpa [prefixWord, tailWord_1304645, baseEnd_1304645] using wordTrace_append hprefix tailTrace_1304645
  have hstable : (prefixWord ++ tailWord_1304645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304645).length < 2 ^ (prefixWord ++ tailWord_1304645).sum := by decide
  have hdescent : baseEnd_1304645 < baseStart_1304645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304677 : List Nat := [1, 3, 1, 3, 2, 3, 1, 1, 7]
def baseStart_1304677 : Nat := 118140960795 + 1304677 * 2 ^ 59
def prefixEnd_1304677 : Nat := 4983230072969 + 3 ^ 40 * 1304677 * 2
def baseEnd_1304677 : Nat := 148872533303577150874979

theorem tailTrace_1304677 : CollatzResearch.WordTrace tailWord_1304677 prefixEnd_1304677 148872533303577150874979 := by
  unfold tailWord_1304677
  simp only [CollatzResearch.WordTrace]
  refine ⟨47585479494385524937016285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31723652996257016624677523 47585479494385524937016285)
  ·
    refine ⟨17844554810394571851381107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47585479494385524937016285 17844554810394571851381107)
    ·
      refine ⟨26766832215591857777071661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17844554810394571851381107 26766832215591857777071661)
      ·
        refine ⟨10037562080846946666401873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26766832215591857777071661 10037562080846946666401873)
        ·
          refine ⟨7528171560635209999801405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10037562080846946666401873 7528171560635209999801405)
          ·
            refine ⟨2823064335238203749925527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7528171560635209999801405 2823064335238203749925527)
            ·
              refine ⟨4234596502857305624888291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2823064335238203749925527 4234596502857305624888291)
              ·
                refine ⟨6351894754285958437332437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4234596502857305624888291 6351894754285958437332437)
                ·
                  refine ⟨148872533303577150874979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6351894754285958437332437 148872533303577150874979)
                  ·
                    rfl

theorem cell22_1304677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_1304677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304677 prefixEnd_1304677 := by exact prefixLift 1304677
  have htrace : WordTrace (prefixWord ++ tailWord_1304677) baseStart_1304677 baseEnd_1304677 := by
    simpa [prefixWord, tailWord_1304677, baseEnd_1304677] using wordTrace_append hprefix tailTrace_1304677
  have hstable : (prefixWord ++ tailWord_1304677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304677).length < 2 ^ (prefixWord ++ tailWord_1304677).sum := by decide
  have hdescent : baseEnd_1304677 < baseStart_1304677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304790 : List Nat := [5, 2, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1304790 : Nat := 118140960795 + 1304790 * 2 ^ 59
def prefixEnd_1304790 : Nat := 4983230072969 + 3 ^ 40 * 1304790 * 2
def baseEnd_1304790 : Nat := 148885427373345608183197

theorem tailTrace_1304790 : CollatzResearch.WordTrace tailWord_1304790 prefixEnd_1304790 148885427373345608183197 := by
  unfold tailWord_1304790
  simp only [CollatzResearch.WordTrace]
  refine ⟨2974350058936009077242489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31726400628650763490586549 2974350058936009077242489)
  ·
    refine ⟨2230762544202006807931867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2974350058936009077242489 2230762544202006807931867)
    ·
      refine ⟨3346143816303010211897801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2230762544202006807931867 3346143816303010211897801)
      ·
        refine ⟨2509607862227257658923351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3346143816303010211897801 2509607862227257658923351)
        ·
          refine ⟨3764411793340886488385027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2509607862227257658923351 3764411793340886488385027)
          ·
            refine ⟨5646617690011329732577541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3764411793340886488385027 5646617690011329732577541)
            ·
              refine ⟨1058740816877124324858289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5646617690011329732577541 1058740816877124324858289)
              ·
                refine ⟨794055612657843243643717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058740816877124324858289 794055612657843243643717)
                ·
                  refine ⟨148885427373345608183197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 794055612657843243643717 148885427373345608183197)
                  ·
                    rfl

theorem cell22_1304790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1304790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304790 prefixEnd_1304790 := by exact prefixLift 1304790
  have htrace : WordTrace (prefixWord ++ tailWord_1304790) baseStart_1304790 baseEnd_1304790 := by
    simpa [prefixWord, tailWord_1304790, baseEnd_1304790] using wordTrace_append hprefix tailTrace_1304790
  have hstable : (prefixWord ++ tailWord_1304790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304790).length < 2 ^ (prefixWord ++ tailWord_1304790).sum := by decide
  have hdescent : baseEnd_1304790 < baseStart_1304790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304799 : List Nat := [1, 1, 2, 3, 2, 1, 1, 5, 3, 3]
def baseStart_1304799 : Nat := 118140960795 + 1304799 * 2 ^ 59
def prefixEnd_1304799 : Nat := 4983230072969 + 3 ^ 40 * 1304799 * 2
def baseEnd_1304799 : Nat := 446659363003963801074563

theorem tailTrace_1304799 : CollatzResearch.WordTrace tailWord_1304799 prefixEnd_1304799 446659363003963801074563 := by
  unfold tailWord_1304799
  simp only [CollatzResearch.WordTrace]
  refine ⟨47589929199943539772957451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31726619466629026515304967 47589929199943539772957451)
  ·
    refine ⟨71384893799915309659436177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47589929199943539772957451 71384893799915309659436177)
    ·
      refine ⟨53538670349936482244577133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71384893799915309659436177 53538670349936482244577133)
      ·
        refine ⟨20077001381226180841716425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53538670349936482244577133 20077001381226180841716425)
        ·
          refine ⟨15057751035919635631287319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20077001381226180841716425 15057751035919635631287319)
          ·
            refine ⟨22586626553879453446930979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15057751035919635631287319 22586626553879453446930979)
            ·
              refine ⟨33879939830819180170396469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22586626553879453446930979 33879939830819180170396469)
              ·
                refine ⟨3176244359139298140974669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33879939830819180170396469 3176244359139298140974669)
                ·
                  refine ⟨1191091634677236802865501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3176244359139298140974669 1191091634677236802865501)
                  ·
                    refine ⟨446659363003963801074563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1191091634677236802865501 446659363003963801074563)
                    ·
                      rfl

theorem cell22_1304799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 5, 3, 3].length) (baseStart_1304799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304799 prefixEnd_1304799 := by exact prefixLift 1304799
  have htrace : WordTrace (prefixWord ++ tailWord_1304799) baseStart_1304799 baseEnd_1304799 := by
    simpa [prefixWord, tailWord_1304799, baseEnd_1304799] using wordTrace_append hprefix tailTrace_1304799
  have hstable : (prefixWord ++ tailWord_1304799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304799).length < 2 ^ (prefixWord ++ tailWord_1304799).sum := by decide
  have hdescent : baseEnd_1304799 < baseStart_1304799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304833 : List Nat := [1, 2, 4, 1, 1, 2, 4, 3, 1, 3]
def baseStart_1304833 : Nat := 118140960795 + 1304833 * 2 ^ 59
def prefixEnd_1304833 : Nat := 4983230072969 + 3 ^ 40 * 1304833 * 2
def baseEnd_1304833 : Nat := 446671001898799045724459

theorem tailTrace_1304833 : CollatzResearch.WordTrace tailWord_1304833 prefixEnd_1304833 446671001898799045724459 := by
  unfold tailWord_1304833
  simp only [CollatzResearch.WordTrace]
  refine ⟨47591169281820363579695153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31727446187880242386463435 47591169281820363579695153)
  ·
    refine ⟨35693376961365272684771365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47591169281820363579695153 35693376961365272684771365)
    ·
      refine ⟨6692508180255988628394631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35693376961365272684771365 6692508180255988628394631)
      ·
        refine ⟨10038762270383982942591947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6692508180255988628394631 10038762270383982942591947)
        ·
          refine ⟨15058143405575974413887921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10038762270383982942591947 15058143405575974413887921)
          ·
            refine ⟨11293607554181980810415941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15058143405575974413887921 11293607554181980810415941)
            ·
              refine ⟨2117551416409121401952989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11293607554181980810415941 2117551416409121401952989)
              ·
                refine ⟨794081781153420525732371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2117551416409121401952989 794081781153420525732371)
                ·
                  refine ⟨1191122671730130788598557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 794081781153420525732371 1191122671730130788598557)
                  ·
                    refine ⟨446671001898799045724459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1191122671730130788598557 446671001898799045724459)
                    ·
                      rfl

theorem cell22_1304833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_1304833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304833 prefixEnd_1304833 := by exact prefixLift 1304833
  have htrace : WordTrace (prefixWord ++ tailWord_1304833) baseStart_1304833 baseEnd_1304833 := by
    simpa [prefixWord, tailWord_1304833, baseEnd_1304833] using wordTrace_append hprefix tailTrace_1304833
  have hstable : (prefixWord ++ tailWord_1304833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304833).length < 2 ^ (prefixWord ++ tailWord_1304833).sum := by decide
  have hdescent : baseEnd_1304833 < baseStart_1304833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304904 : List Nat := [2, 1, 3, 1, 1, 2, 3, 1, 4, 4]
def baseStart_1304904 : Nat := 118140960795 + 1304904 * 2 ^ 59
def prefixEnd_1304904 : Nat := 4983230072969 + 3 ^ 40 * 1304904 * 2
def baseEnd_1304904 : Nat := 446695306649778527199241

theorem tailTrace_1304904 : CollatzResearch.WordTrace tailWord_1304904 prefixEnd_1304904 446695306649778527199241 := by
  unfold tailWord_1304904
  simp only [CollatzResearch.WordTrace]
  refine ⟨23796879432281571352764883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31729172576375428470353177 23796879432281571352764883)
  ·
    refine ⟨35695319148422357029147325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23796879432281571352764883 35695319148422357029147325)
    ·
      refine ⟨13385744680658383885930247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35695319148422357029147325 13385744680658383885930247)
      ·
        refine ⟨20078617020987575828895371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13385744680658383885930247 20078617020987575828895371)
        ·
          refine ⟨30117925531481363743343057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20078617020987575828895371 30117925531481363743343057)
          ·
            refine ⟨22588444148611022807507293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30117925531481363743343057 22588444148611022807507293)
            ·
              refine ⟨8470666555729133552815235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22588444148611022807507293 8470666555729133552815235)
              ·
                refine ⟨12705999833593700329222853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8470666555729133552815235 12705999833593700329222853)
                ·
                  refine ⟨2382374968798818811729285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12705999833593700329222853 2382374968798818811729285)
                  ·
                    refine ⟨446695306649778527199241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2382374968798818811729285 446695306649778527199241)
                    ·
                      rfl

theorem cell22_1304904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_1304904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304904 prefixEnd_1304904 := by exact prefixLift 1304904
  have htrace : WordTrace (prefixWord ++ tailWord_1304904) baseStart_1304904 baseEnd_1304904 := by
    simpa [prefixWord, tailWord_1304904, baseEnd_1304904] using wordTrace_append hprefix tailTrace_1304904
  have hstable : (prefixWord ++ tailWord_1304904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304904).length < 2 ^ (prefixWord ++ tailWord_1304904).sum := by decide
  have hdescent : baseEnd_1304904 < baseStart_1304904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304908 : List Nat := [2, 2, 1, 3, 2, 1, 5, 2, 4]
def baseStart_1304908 : Nat := 118140960795 + 1304908 * 2 ^ 59
def prefixEnd_1304908 : Nat := 4983230072969 + 3 ^ 40 * 1304908 * 2
def baseEnd_1304908 : Nat := 148898891977174616699743

theorem tailTrace_1304908 : CollatzResearch.WordTrace tailWord_1304908 prefixEnd_1304908 148898891977174616699743 := by
  unfold tailWord_1304908
  simp only [CollatzResearch.WordTrace]
  refine ⟨23796952378274325694337689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31729269837699100925783585 23796952378274325694337689)
  ·
    refine ⟨17847714283705744270753267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23796952378274325694337689 17847714283705744270753267)
    ·
      refine ⟨26771571425558616406129901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17847714283705744270753267 26771571425558616406129901)
      ·
        refine ⟨10039339284584481152298713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26771571425558616406129901 10039339284584481152298713)
        ·
          refine ⟨7529504463438360864224035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10039339284584481152298713 7529504463438360864224035)
          ·
            refine ⟨11294256695157541296336053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7529504463438360864224035 11294256695157541296336053)
            ·
              refine ⟨1058836565171019496531505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11294256695157541296336053 1058836565171019496531505)
              ·
                refine ⟨794127423878264622398629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1058836565171019496531505 794127423878264622398629)
                ·
                  refine ⟨148898891977174616699743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 794127423878264622398629 148898891977174616699743)
                  ·
                    rfl

theorem cell22_1304908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 5, 2, 4].length) (baseStart_1304908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304908 prefixEnd_1304908 := by exact prefixLift 1304908
  have htrace : WordTrace (prefixWord ++ tailWord_1304908) baseStart_1304908 baseEnd_1304908 := by
    simpa [prefixWord, tailWord_1304908, baseEnd_1304908] using wordTrace_append hprefix tailTrace_1304908
  have hstable : (prefixWord ++ tailWord_1304908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304908).length < 2 ^ (prefixWord ++ tailWord_1304908).sum := by decide
  have hdescent : baseEnd_1304908 < baseStart_1304908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1304919 : List Nat := [1, 1, 3, 2, 3, 1, 4, 7]
def baseStart_1304919 : Nat := 118140960795 + 1304919 * 2 ^ 59
def prefixEnd_1304919 : Nat := 4983230072969 + 3 ^ 40 * 1304919 * 2
def baseEnd_1304919 : Nat := 49633382384035943119355

theorem tailTrace_1304919 : CollatzResearch.WordTrace tailWord_1304919 prefixEnd_1304919 49633382384035943119355 := by
  unfold tailWord_1304919
  simp only [CollatzResearch.WordTrace]
  refine ⟨47594305959508800267325811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31729537306339200178217207 47594305959508800267325811)
  ·
    refine ⟨71391458939263200400988717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47594305959508800267325811 71391458939263200400988717)
    ·
      refine ⟨26771797102223700150370769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71391458939263200400988717 26771797102223700150370769)
      ·
        refine ⟨20078847826667775112778077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26771797102223700150370769 20078847826667775112778077)
        ·
          refine ⟨7529567935000415667291779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20078847826667775112778077 7529567935000415667291779)
          ·
            refine ⟨11294351902500623500937669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7529567935000415667291779 11294351902500623500937669)
            ·
              refine ⟨2117690981718866906425813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11294351902500623500937669 2117690981718866906425813)
              ·
                refine ⟨49633382384035943119355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2117690981718866906425813 49633382384035943119355)
                ·
                  rfl

theorem cell22_1304919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 7].length) (baseStart_1304919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1304919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1304919 prefixEnd_1304919 := by exact prefixLift 1304919
  have htrace : WordTrace (prefixWord ++ tailWord_1304919) baseStart_1304919 baseEnd_1304919 := by
    simpa [prefixWord, tailWord_1304919, baseEnd_1304919] using wordTrace_append hprefix tailTrace_1304919
  have hstable : (prefixWord ++ tailWord_1304919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1304919).length < 2 ^ (prefixWord ++ tailWord_1304919).sum := by decide
  have hdescent : baseEnd_1304919 < baseStart_1304919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1304919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
