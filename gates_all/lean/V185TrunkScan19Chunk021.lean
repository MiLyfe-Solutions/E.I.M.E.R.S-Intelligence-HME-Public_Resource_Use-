import V185TrunkScan19Chunk020

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental

namespace V185TrunkScan19Incremental

def tailWord_211040 : List Nat := [2, 1, 1, 3, 2, 5, 2, 3]
def baseStart_211040 : Nat := 118140960795 + 211040 * 2 ^ 59
def prefixEnd_211040 : Nat := 4983230072969 + 3 ^ 40 * 211040 * 2
def baseEnd_211040 : Nat := 64216271007383430358193

theorem tailTrace_211040 : CollatzResearch.WordTrace tailWord_211040 prefixEnd_211040 64216271007383430358193 := by
  unfold tailWord_211040
  simp only [CollatzResearch.WordTrace]
  refine ⟨3848630577722798803799287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5131507436963731738399049 3848630577722798803799287)
  ·
    refine ⟨5772945866584198205698931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3848630577722798803799287 5772945866584198205698931)
    ·
      refine ⟨8659418799876297308548397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5772945866584198205698931 8659418799876297308548397)
      ·
        refine ⟨3247282049953611490705649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8659418799876297308548397 3247282049953611490705649)
        ·
          refine ⟨2435461537465208618029237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3247282049953611490705649 2435461537465208618029237)
          ·
            refine ⟨228324519137363307940241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2435461537465208618029237 228324519137363307940241)
            ·
              refine ⟨171243389353022480955181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228324519137363307940241 171243389353022480955181)
              ·
                refine ⟨64216271007383430358193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171243389353022480955181 64216271007383430358193)
                ·
                  rfl

theorem cell19_211040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 3].length) (baseStart_211040 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211040 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211040 prefixEnd_211040 := by exact prefixLift 211040
  have htrace : WordTrace (prefixWord ++ tailWord_211040) baseStart_211040 baseEnd_211040 := by
    simpa [prefixWord, tailWord_211040, baseEnd_211040] using wordTrace_append hprefix tailTrace_211040
  have hstable : (prefixWord ++ tailWord_211040).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211040).length < 2 ^ (prefixWord ++ tailWord_211040).sum := by decide
  have hdescent : baseEnd_211040 < baseStart_211040 := by decide
  rcases family_descends (prefixWord ++ tailWord_211040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211063 : List Nat := [1, 1, 3, 1, 1, 5, 7]
def baseStart_211063 : Nat := 118140960795 + 211063 * 2 ^ 59
def prefixEnd_211063 : Nat := 4983230072969 + 3 ^ 40 * 211063 * 2
def baseEnd_211063 : Nat := 21407756519508730615673

theorem tailTrace_211063 : CollatzResearch.WordTrace tailWord_211063 prefixEnd_211063 21407756519508730615673 := by
  unfold tailWord_211063
  simp only [CollatzResearch.WordTrace]
  refine ⟨7698100034362272535685843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5132066689574848357123895 7698100034362272535685843)
  ·
    refine ⟨11547150051543408803528765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7698100034362272535685843 11547150051543408803528765)
    ·
      refine ⟨4330181269328778301323287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11547150051543408803528765 4330181269328778301323287)
      ·
        refine ⟨6495271903993167451984931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4330181269328778301323287 6495271903993167451984931)
        ·
          refine ⟨9742907855989751177977397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6495271903993167451984931 9742907855989751177977397)
          ·
            refine ⟨913397611499039172935381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9742907855989751177977397 913397611499039172935381)
            ·
              refine ⟨21407756519508730615673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 913397611499039172935381 21407756519508730615673)
              ·
                rfl

theorem cell19_211063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 7].length) (baseStart_211063 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211063 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211063 prefixEnd_211063 := by exact prefixLift 211063
  have htrace : WordTrace (prefixWord ++ tailWord_211063) baseStart_211063 baseEnd_211063 := by
    simpa [prefixWord, tailWord_211063, baseEnd_211063] using wordTrace_append hprefix tailTrace_211063
  have hstable : (prefixWord ++ tailWord_211063).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211063).length < 2 ^ (prefixWord ++ tailWord_211063).sum := by decide
  have hdescent : baseEnd_211063 < baseStart_211063 := by decide
  rcases family_descends (prefixWord ++ tailWord_211063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211080 : List Nat := [2, 1, 3, 4, 1, 1, 1, 6]
def baseStart_211080 : Nat := 118140960795 + 211080 * 2 ^ 59
def prefixEnd_211080 : Nat := 4983230072969 + 3 ^ 40 * 211080 * 2
def baseEnd_211080 : Nat := 64228442400675189469195

theorem tailTrace_211080 : CollatzResearch.WordTrace tailWord_211080 prefixEnd_211080 64228442400675189469195 := by
  unfold tailWord_211080
  simp only [CollatzResearch.WordTrace]
  refine ⟨3849360037650342219527347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5132480050200456292703129 3849360037650342219527347)
  ·
    refine ⟨5774040056475513329291021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3849360037650342219527347 5774040056475513329291021)
    ·
      refine ⟨2165265021178317498484133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5774040056475513329291021 2165265021178317498484133)
      ·
        refine ⟨405987191470934530965775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2165265021178317498484133 405987191470934530965775)
        ·
          refine ⟨608980787206401796448663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 405987191470934530965775 608980787206401796448663)
          ·
            refine ⟨913471180809602694672995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 608980787206401796448663 913471180809602694672995)
            ·
              refine ⟨1370206771214404042009493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 913471180809602694672995 1370206771214404042009493)
              ·
                refine ⟨64228442400675189469195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1370206771214404042009493 64228442400675189469195)
                ·
                  rfl

theorem cell19_211080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_211080 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211080 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211080 prefixEnd_211080 := by exact prefixLift 211080
  have htrace : WordTrace (prefixWord ++ tailWord_211080) baseStart_211080 baseEnd_211080 := by
    simpa [prefixWord, tailWord_211080, baseEnd_211080] using wordTrace_append hprefix tailTrace_211080
  have hstable : (prefixWord ++ tailWord_211080).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211080).length < 2 ^ (prefixWord ++ tailWord_211080).sum := by decide
  have hdescent : baseEnd_211080 < baseStart_211080 := by decide
  rcases family_descends (prefixWord ++ tailWord_211080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211154 : List Nat := [3, 2, 2, 2, 1, 3, 3, 3]
def baseStart_211154 : Nat := 118140960795 + 211154 * 2 ^ 59
def prefixEnd_211154 : Nat := 4983230072969 + 3 ^ 40 * 211154 * 2
def baseEnd_211154 : Nat := 64250959478264943824549

theorem tailTrace_211154 : CollatzResearch.WordTrace tailWord_211154 prefixEnd_211154 64250959478264943824549 := by
  unfold tailWord_211154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1925354769258148769312129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5134279384688396718165677 1925354769258148769312129)
  ·
    refine ⟨1444016076943611576984097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1925354769258148769312129 1444016076943611576984097)
    ·
      refine ⟨1083012057707708682738073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1444016076943611576984097 1083012057707708682738073)
      ·
        refine ⟨812259043280781512053555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1083012057707708682738073 812259043280781512053555)
        ·
          refine ⟨1218388564921172268080333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 812259043280781512053555 1218388564921172268080333)
          ·
            refine ⟨456895711845439600530125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1218388564921172268080333 456895711845439600530125)
            ·
              refine ⟨171335891942039850198797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 456895711845439600530125 171335891942039850198797)
              ·
                refine ⟨64250959478264943824549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171335891942039850198797 64250959478264943824549)
                ·
                  rfl

theorem cell19_211154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 3].length) (baseStart_211154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211154 prefixEnd_211154 := by exact prefixLift 211154
  have htrace : WordTrace (prefixWord ++ tailWord_211154) baseStart_211154 baseEnd_211154 := by
    simpa [prefixWord, tailWord_211154, baseEnd_211154] using wordTrace_append hprefix tailTrace_211154
  have hstable : (prefixWord ++ tailWord_211154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211154).length < 2 ^ (prefixWord ++ tailWord_211154).sum := by decide
  have hdescent : baseEnd_211154 < baseStart_211154 := by decide
  rcases family_descends (prefixWord ++ tailWord_211154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211175 : List Nat := [1, 1, 5, 3, 1, 2, 6]
def baseStart_211175 : Nat := 118140960795 + 211175 * 2 ^ 59
def prefixEnd_211175 : Nat := 4983230072969 + 3 ^ 40 * 211175 * 2
def baseEnd_211175 : Nat := 21419116486581039119275

theorem tailTrace_211175 : CollatzResearch.WordTrace tailWord_211175 prefixEnd_211175 21419116486581039119275 := by
  unfold tailWord_211175
  simp only [CollatzResearch.WordTrace]
  refine ⟨7702185009956515663762979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5134790006637677109175319 7702185009956515663762979)
  ·
    refine ⟨11553277514934773495644469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7702185009956515663762979 11553277514934773495644469)
    ·
      refine ⟨1083119767025135015216669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11553277514934773495644469 1083119767025135015216669)
      ·
        refine ⟨406169912634425630706251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1083119767025135015216669 406169912634425630706251)
        ·
          refine ⟨609254868951638446059377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406169912634425630706251 609254868951638446059377)
          ·
            refine ⟨456941151713728834544533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 609254868951638446059377 456941151713728834544533)
            ·
              refine ⟨21419116486581039119275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 456941151713728834544533 21419116486581039119275)
              ·
                rfl

theorem cell19_211175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 6].length) (baseStart_211175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211175 prefixEnd_211175 := by exact prefixLift 211175
  have htrace : WordTrace (prefixWord ++ tailWord_211175) baseStart_211175 baseEnd_211175 := by
    simpa [prefixWord, tailWord_211175, baseEnd_211175] using wordTrace_append hprefix tailTrace_211175
  have hstable : (prefixWord ++ tailWord_211175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211175).length < 2 ^ (prefixWord ++ tailWord_211175).sum := by decide
  have hdescent : baseEnd_211175 < baseStart_211175 := by decide
  rcases family_descends (prefixWord ++ tailWord_211175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211207 : List Nat := [1, 1, 4, 5, 2, 1, 2, 3]
def baseStart_211207 : Nat := 118140960795 + 211207 * 2 ^ 59
def prefixEnd_211207 : Nat := 4983230072969 + 3 ^ 40 * 211207 * 2
def baseEnd_211207 : Nat := 64267086574376524646627

theorem tailTrace_211207 : CollatzResearch.WordTrace tailWord_211207 prefixEnd_211207 64267086574376524646627 := by
  unfold tailWord_211207
  simp only [CollatzResearch.WordTrace]
  refine ⟨7703352145840585128927875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5135568097227056752618583 7703352145840585128927875)
  ·
    refine ⟨11555028218760877693391813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7703352145840585128927875 11555028218760877693391813)
    ·
      refine ⟨2166567791017664567510965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11555028218760877693391813 2166567791017664567510965)
      ·
        refine ⟨203115730407906053204153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2166567791017664567510965 203115730407906053204153)
        ·
          refine ⟨152336797805929539903115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203115730407906053204153 152336797805929539903115)
          ·
            refine ⟨228505196708894309854673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152336797805929539903115 228505196708894309854673)
            ·
              refine ⟨171378897531670732391005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 228505196708894309854673 171378897531670732391005)
              ·
                refine ⟨64267086574376524646627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171378897531670732391005 64267086574376524646627)
                ·
                  rfl

theorem cell19_211207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 3].length) (baseStart_211207 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211207 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211207 prefixEnd_211207 := by exact prefixLift 211207
  have htrace : WordTrace (prefixWord ++ tailWord_211207) baseStart_211207 baseEnd_211207 := by
    simpa [prefixWord, tailWord_211207, baseEnd_211207] using wordTrace_append hprefix tailTrace_211207
  have hstable : (prefixWord ++ tailWord_211207).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211207).length < 2 ^ (prefixWord ++ tailWord_211207).sum := by decide
  have hdescent : baseEnd_211207 < baseStart_211207 := by decide
  rcases family_descends (prefixWord ++ tailWord_211207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211230 : List Nat := [4, 3, 2, 1, 1, 1, 7]
def baseStart_211230 : Nat := 118140960795 + 211230 * 2 ^ 59
def prefixEnd_211230 : Nat := 4983230072969 + 3 ^ 40 * 211230 * 2
def baseEnd_211230 : Nat := 21424695041839762045151

theorem tailTrace_211230 : CollatzResearch.WordTrace tailWord_211230 prefixEnd_211230 21424695041839762045151 := by
  unfold tailWord_211230
  simp only [CollatzResearch.WordTrace]
  refine ⟨963023878094657507126893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5136127349838173371343429 963023878094657507126893)
  ·
    refine ⟨361133954285496565172585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 963023878094657507126893 361133954285496565172585)
    ·
      refine ⟨270850465714122423879439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361133954285496565172585 270850465714122423879439)
      ·
        refine ⟨406275698571183635819159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 270850465714122423879439 406275698571183635819159)
        ·
          refine ⟨609413547856775453728739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406275698571183635819159 609413547856775453728739)
          ·
            refine ⟨914120321785163180593109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 609413547856775453728739 914120321785163180593109)
            ·
              refine ⟨21424695041839762045151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 914120321785163180593109 21424695041839762045151)
              ·
                rfl

theorem cell19_211230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_211230 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211230 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211230 prefixEnd_211230 := by exact prefixLift 211230
  have htrace : WordTrace (prefixWord ++ tailWord_211230) baseStart_211230 baseEnd_211230 := by
    simpa [prefixWord, tailWord_211230, baseEnd_211230] using wordTrace_append hprefix tailTrace_211230
  have hstable : (prefixWord ++ tailWord_211230).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211230).length < 2 ^ (prefixWord ++ tailWord_211230).sum := by decide
  have hdescent : baseEnd_211230 < baseStart_211230 := by decide
  rcases family_descends (prefixWord ++ tailWord_211230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211232 : List Nat := [2, 1, 1, 5, 2, 3, 5]
def baseStart_211232 : Nat := 118140960795 + 211232 * 2 ^ 59
def prefixEnd_211232 : Nat := 4983230072969 + 3 ^ 40 * 211232 * 2
def baseEnd_211232 : Nat := 21424897898394624697001

theorem tailTrace_211232 : CollatzResearch.WordTrace tailWord_211232 prefixEnd_211232 21424897898394624697001 := by
  unfold tailWord_211232
  simp only [CollatzResearch.WordTrace]
  refine ⟨3852131985375007199293975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5136175980500009599058633 3852131985375007199293975)
  ·
    refine ⟨5778197978062510798940963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3852131985375007199293975 5778197978062510798940963)
    ·
      refine ⟨8667296967093766198411445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5778197978062510798940963 8667296967093766198411445)
      ·
        refine ⟨812559090665040581101073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8667296967093766198411445 812559090665040581101073)
        ·
          refine ⟨609419317998780435825805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 812559090665040581101073 609419317998780435825805)
          ·
            refine ⟨228532244249542663434677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 609419317998780435825805 228532244249542663434677)
            ·
              refine ⟨21424897898394624697001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 228532244249542663434677 21424897898394624697001)
              ·
                rfl

theorem cell19_211232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 3, 5].length) (baseStart_211232 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211232 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211232 prefixEnd_211232 := by exact prefixLift 211232
  have htrace : WordTrace (prefixWord ++ tailWord_211232) baseStart_211232 baseEnd_211232 := by
    simpa [prefixWord, tailWord_211232, baseEnd_211232] using wordTrace_append hprefix tailTrace_211232
  have hstable : (prefixWord ++ tailWord_211232).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211232).length < 2 ^ (prefixWord ++ tailWord_211232).sum := by decide
  have hdescent : baseEnd_211232 < baseStart_211232 := by decide
  rcases family_descends (prefixWord ++ tailWord_211232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211272 : List Nat := [2, 1, 3, 1, 1, 2, 4, 5]
def baseStart_211272 : Nat := 118140960795 + 211272 * 2 ^ 59
def prefixEnd_211272 : Nat := 4983230072969 + 3 ^ 40 * 211272 * 2
def baseEnd_211272 : Nat := 64286865088475633202005

theorem tailTrace_211272 : CollatzResearch.WordTrace tailWord_211272 prefixEnd_211272 64286865088475633202005 := by
  unfold tailWord_211272
  simp only [CollatzResearch.WordTrace]
  refine ⟨3852861445302550615022035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5137148593736734153362713 3852861445302550615022035)
  ·
    refine ⟨5779292167953825922533053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3852861445302550615022035 5779292167953825922533053)
    ·
      refine ⟨2167234562982684720949895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5779292167953825922533053 2167234562982684720949895)
      ·
        refine ⟨3250851844474027081424843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167234562982684720949895 3250851844474027081424843)
        ·
          refine ⟨4876277766711040622137265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3250851844474027081424843 4876277766711040622137265)
          ·
            refine ⟨3657208325033280466602949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4876277766711040622137265 3657208325033280466602949)
            ·
              refine ⟨685726560943740087488053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3657208325033280466602949 685726560943740087488053)
              ·
                refine ⟨64286865088475633202005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 685726560943740087488053 64286865088475633202005)
                ·
                  rfl

theorem cell19_211272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_211272 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211272 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211272 prefixEnd_211272 := by exact prefixLift 211272
  have htrace : WordTrace (prefixWord ++ tailWord_211272) baseStart_211272 baseEnd_211272 := by
    simpa [prefixWord, tailWord_211272, baseEnd_211272] using wordTrace_append hprefix tailTrace_211272
  have hstable : (prefixWord ++ tailWord_211272).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211272).length < 2 ^ (prefixWord ++ tailWord_211272).sum := by decide
  have hdescent : baseEnd_211272 < baseStart_211272 := by decide
  rcases family_descends (prefixWord ++ tailWord_211272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211306 : List Nat := [3, 1, 3, 3, 1, 3, 1, 4]
def baseStart_211306 : Nat := 118140960795 + 211306 * 2 ^ 59
def prefixEnd_211306 : Nat := 4983230072969 + 3 ^ 40 * 211306 * 2
def baseEnd_211306 : Nat := 64297210772773628446357

theorem tailTrace_211306 : CollatzResearch.WordTrace tailWord_211306 prefixEnd_211306 64297210772773628446357 := by
  unfold tailWord_211306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1926740743120481259195443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5137975314987950024521181 1926740743120481259195443)
  ·
    refine ⟨2890111114680721888793165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1926740743120481259195443 2890111114680721888793165)
    ·
      refine ⟨1083791668005270708297437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2890111114680721888793165 1083791668005270708297437)
      ·
        refine ⟨406421875501976515611539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1083791668005270708297437 406421875501976515611539)
        ·
          refine ⟨609632813252964773417309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406421875501976515611539 609632813252964773417309)
          ·
            refine ⟨228612304969861790031491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 609632813252964773417309 228612304969861790031491)
            ·
              refine ⟨342918457454792685047237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 228612304969861790031491 342918457454792685047237)
              ·
                refine ⟨64297210772773628446357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 342918457454792685047237 64297210772773628446357)
                ·
                  rfl

theorem cell19_211306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_211306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211306 prefixEnd_211306 := by exact prefixLift 211306
  have htrace : WordTrace (prefixWord ++ tailWord_211306) baseStart_211306 baseEnd_211306 := by
    simpa [prefixWord, tailWord_211306, baseEnd_211306] using wordTrace_append hprefix tailTrace_211306
  have hstable : (prefixWord ++ tailWord_211306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211306).length < 2 ^ (prefixWord ++ tailWord_211306).sum := by decide
  have hdescent : baseEnd_211306 < baseStart_211306 := by decide
  rcases family_descends (prefixWord ++ tailWord_211306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211380 : List Nat := [2, 5, 2, 2, 1, 1, 1, 5]
def baseStart_211380 : Nat := 118140960795 + 211380 * 2 ^ 59
def prefixEnd_211380 : Nat := 4983230072969 + 3 ^ 40 * 211380 * 2
def baseEnd_211380 : Nat := 64319727850363382801711

theorem tailTrace_211380 : CollatzResearch.WordTrace tailWord_211380 prefixEnd_211380 64319727850363382801711 := by
  unfold tailWord_211380
  simp only [CollatzResearch.WordTrace]
  refine ⟨3854830987106917837487797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5139774649475890449983729 3854830987106917837487797)
  ·
    refine ⟨361390405041273547264481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3854830987106917837487797 361390405041273547264481)
    ·
      refine ⟨271042803780955160448361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 361390405041273547264481 271042803780955160448361)
      ·
        refine ⟨203282102835716370336271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 271042803780955160448361 203282102835716370336271)
        ·
          refine ⟨304923154253574555504407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203282102835716370336271 304923154253574555504407)
          ·
            refine ⟨457384731380361833256611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 304923154253574555504407 457384731380361833256611)
            ·
              refine ⟨686077097070542749884917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 457384731380361833256611 686077097070542749884917)
              ·
                refine ⟨64319727850363382801711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 686077097070542749884917 64319727850363382801711)
                ·
                  rfl

theorem cell19_211380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_211380 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211380 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211380 prefixEnd_211380 := by exact prefixLift 211380
  have htrace : WordTrace (prefixWord ++ tailWord_211380) baseStart_211380 baseEnd_211380 := by
    simpa [prefixWord, tailWord_211380, baseEnd_211380] using wordTrace_append hprefix tailTrace_211380
  have hstable : (prefixWord ++ tailWord_211380).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211380).length < 2 ^ (prefixWord ++ tailWord_211380).sum := by decide
  have hdescent : baseEnd_211380 < baseStart_211380 := by decide
  rcases family_descends (prefixWord ++ tailWord_211380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211424 : List Nat := [2, 1, 1, 3, 1, 1, 6, 4]
def baseStart_211424 : Nat := 118140960795 + 211424 * 2 ^ 59
def prefixEnd_211424 : Nat := 4983230072969 + 3 ^ 40 * 211424 * 2
def baseEnd_211424 : Nat := 64333116382984317823813

theorem tailTrace_211424 : CollatzResearch.WordTrace tailWord_211424 prefixEnd_211424 64333116382984317823813 := by
  unfold tailWord_211424
  simp only [CollatzResearch.WordTrace]
  refine ⟨3855633393027215594788663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5140844524036287459718217 3855633393027215594788663)
  ·
    refine ⟨5783450089540823392182995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3855633393027215594788663 5783450089540823392182995)
    ·
      refine ⟨8675175134311235088274493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5783450089540823392182995 8675175134311235088274493)
      ·
        refine ⟨3253190675366713158102935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8675175134311235088274493 3253190675366713158102935)
        ·
          refine ⟨4879786013050069737154403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253190675366713158102935 4879786013050069737154403)
          ·
            refine ⟨7319679019575104605731605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879786013050069737154403 7319679019575104605731605)
            ·
              refine ⟨343109954042583028393669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7319679019575104605731605 343109954042583028393669)
              ·
                refine ⟨64333116382984317823813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 343109954042583028393669 64333116382984317823813)
                ·
                  rfl

theorem cell19_211424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 4].length) (baseStart_211424 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211424 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211424 prefixEnd_211424 := by exact prefixLift 211424
  have htrace : WordTrace (prefixWord ++ tailWord_211424) baseStart_211424 baseEnd_211424 := by
    simpa [prefixWord, tailWord_211424, baseEnd_211424] using wordTrace_append hprefix tailTrace_211424
  have hstable : (prefixWord ++ tailWord_211424).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211424).length < 2 ^ (prefixWord ++ tailWord_211424).sum := by decide
  have hdescent : baseEnd_211424 < baseStart_211424 := by decide
  rcases family_descends (prefixWord ++ tailWord_211424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211458 : List Nat := [3, 4, 1, 2, 3, 6]
def baseStart_211458 : Nat := 118140960795 + 211458 * 2 ^ 59
def prefixEnd_211458 : Nat := 4983230072969 + 3 ^ 40 * 211458 * 2
def baseEnd_211458 : Nat := 7149273563031368118685

theorem tailTrace_211458 : CollatzResearch.WordTrace tailWord_211458 prefixEnd_211458 7149273563031368118685 := by
  unfold tailWord_211458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928126716982813749078757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5141671245287503330876685 1928126716982813749078757)
  ·
    refine ⟨361523759434277577952267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1928126716982813749078757 361523759434277577952267)
    ·
      refine ⟨542285639151416366928401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 361523759434277577952267 542285639151416366928401)
      ·
        refine ⟨406714229363562275196301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542285639151416366928401 406714229363562275196301)
        ·
          refine ⟨152517836011335853198613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 406714229363562275196301 152517836011335853198613)
          ·
            refine ⟨7149273563031368118685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 152517836011335853198613 7149273563031368118685)
            ·
              rfl

theorem cell19_211458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 6].length) (baseStart_211458 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211458 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211458 prefixEnd_211458 := by exact prefixLift 211458
  have htrace : WordTrace (prefixWord ++ tailWord_211458) baseStart_211458 baseEnd_211458 := by
    simpa [prefixWord, tailWord_211458, baseEnd_211458] using wordTrace_append hprefix tailTrace_211458
  have hstable : (prefixWord ++ tailWord_211458).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211458).length < 2 ^ (prefixWord ++ tailWord_211458).sum := by decide
  have hdescent : baseEnd_211458 < baseStart_211458 := by decide
  rcases family_descends (prefixWord ++ tailWord_211458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211496 : List Nat := [2, 1, 5, 2, 1, 2, 3, 3]
def baseStart_211496 : Nat := 118140960795 + 211496 * 2 ^ 59
def prefixEnd_211496 : Nat := 4983230072969 + 3 ^ 40 * 211496 * 2
def baseEnd_211496 : Nat := 64355024890909484223617

theorem tailTrace_211496 : CollatzResearch.WordTrace tailWord_211496 prefixEnd_211496 64355024890909484223617 := by
  unfold tailWord_211496
  simp only [CollatzResearch.WordTrace]
  refine ⟨3856946420896793743099171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5142595227862391657465561 3856946420896793743099171)
  ·
    refine ⟨5785419631345190614648757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3856946420896793743099171 5785419631345190614648757)
    ·
      refine ⟨542383090438611620123321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5785419631345190614648757 542383090438611620123321)
      ·
        refine ⟨406787317828958715092491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 542383090438611620123321 406787317828958715092491)
        ·
          refine ⟨610180976743438072638737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 406787317828958715092491 610180976743438072638737)
          ·
            refine ⟨457635732557578554479053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 610180976743438072638737 457635732557578554479053)
            ·
              refine ⟨171613399709091957929645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 457635732557578554479053 171613399709091957929645)
              ·
                refine ⟨64355024890909484223617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171613399709091957929645 64355024890909484223617)
                ·
                  rfl

theorem cell19_211496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 3].length) (baseStart_211496 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211496 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211496 prefixEnd_211496 := by exact prefixLift 211496
  have htrace : WordTrace (prefixWord ++ tailWord_211496) baseStart_211496 baseEnd_211496 := by
    simpa [prefixWord, tailWord_211496, baseEnd_211496] using wordTrace_append hprefix tailTrace_211496
  have hstable : (prefixWord ++ tailWord_211496).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211496).length < 2 ^ (prefixWord ++ tailWord_211496).sum := by decide
  have hdescent : baseEnd_211496 < baseStart_211496 := by decide
  rcases family_descends (prefixWord ++ tailWord_211496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211538 : List Nat := [3, 2, 2, 1, 2, 1, 2, 6]
def baseStart_211538 : Nat := 118140960795 + 211538 * 2 ^ 59
def prefixEnd_211538 : Nat := 4983230072969 + 3 ^ 40 * 211538 * 2
def baseEnd_211538 : Nat := 64367804853865831290169

theorem tailTrace_211538 : CollatzResearch.WordTrace tailWord_211538 prefixEnd_211538 64367804853865831290169 := by
  unfold tailWord_211538
  simp only [CollatzResearch.WordTrace]
  refine ⟨1928856176910357164806817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5143616471760952439484845 1928856176910357164806817)
  ·
    refine ⟨1446642132682767873605113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1928856176910357164806817 1446642132682767873605113)
    ·
      refine ⟨1084981599512075905203835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1446642132682767873605113 1084981599512075905203835)
      ·
        refine ⟨1627472399268113857805753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1084981599512075905203835 1627472399268113857805753)
        ·
          refine ⟨1220604299451085393354315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1627472399268113857805753 1220604299451085393354315)
          ·
            refine ⟨1830906449176628090031473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1220604299451085393354315 1830906449176628090031473)
            ·
              refine ⟨1373179836882471067523605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1830906449176628090031473 1373179836882471067523605)
              ·
                refine ⟨64367804853865831290169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1373179836882471067523605 64367804853865831290169)
                ·
                  rfl

theorem cell19_211538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 6].length) (baseStart_211538 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211538 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211538 prefixEnd_211538 := by exact prefixLift 211538
  have htrace : WordTrace (prefixWord ++ tailWord_211538) baseStart_211538 baseEnd_211538 := by
    simpa [prefixWord, tailWord_211538, baseEnd_211538] using wordTrace_append hprefix tailTrace_211538
  have hstable : (prefixWord ++ tailWord_211538).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211538).length < 2 ^ (prefixWord ++ tailWord_211538).sum := by decide
  have hdescent : baseEnd_211538 < baseStart_211538 := by decide
  rcases family_descends (prefixWord ++ tailWord_211538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211633 : List Nat := [1, 2, 2, 6, 8]
def baseStart_211633 : Nat := 118140960795 + 211633 * 2 ^ 59
def prefixEnd_211633 : Nat := 4983230072969 + 3 ^ 40 * 211633 * 2
def baseEnd_211633 : Nat := 2385063404182731821437

theorem tailTrace_211633 : CollatzResearch.WordTrace tailWord_211633 prefixEnd_211633 2385063404182731821437 := by
  unfold tailWord_211633
  simp only [CollatzResearch.WordTrace]
  refine ⟨7718889642297259883935553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5145926428198173255957035 7718889642297259883935553)
  ·
    refine ⟨5789167231722944912951665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7718889642297259883935553 5789167231722944912951665)
    ·
      refine ⟨4341875423792208684713749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5789167231722944912951665 4341875423792208684713749)
      ·
        refine ⟨203525410490259782095957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4341875423792208684713749 203525410490259782095957)
        ·
          refine ⟨2385063404182731821437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 203525410490259782095957 2385063404182731821437)
          ·
            rfl

theorem cell19_211633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 8].length) (baseStart_211633 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211633 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211633 prefixEnd_211633 := by exact prefixLift 211633
  have htrace : WordTrace (prefixWord ++ tailWord_211633) baseStart_211633 baseEnd_211633 := by
    simpa [prefixWord, tailWord_211633, baseEnd_211633] using wordTrace_append hprefix tailTrace_211633
  have hstable : (prefixWord ++ tailWord_211633).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211633).length < 2 ^ (prefixWord ++ tailWord_211633).sum := by decide
  have hdescent : baseEnd_211633 < baseStart_211633 := by decide
  rcases family_descends (prefixWord ++ tailWord_211633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211635 : List Nat := [1, 1, 1, 2, 3, 11]
def baseStart_211635 : Nat := 118140960795 + 211635 * 2 ^ 59
def prefixEnd_211635 : Nat := 4983230072969 + 3 ^ 40 * 211635 * 2
def baseEnd_211635 : Nat := 7155257831399816348261

theorem tailTrace_211635 : CollatzResearch.WordTrace tailWord_211635 prefixEnd_211635 7155257831399816348261 := by
  unfold tailWord_211635
  simp only [CollatzResearch.WordTrace]
  refine ⟨7718962588290014225508359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5145975058860009483672239 7718962588290014225508359)
  ·
    refine ⟨11578443882435021338262539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7718962588290014225508359 11578443882435021338262539)
    ·
      refine ⟨17367665823652532007393809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11578443882435021338262539 17367665823652532007393809)
      ·
        refine ⟨13025749367739399005545357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17367665823652532007393809 13025749367739399005545357)
        ·
          refine ⟨4884656012902274627079509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13025749367739399005545357 4884656012902274627079509)
          ·
            refine ⟨7155257831399816348261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4884656012902274627079509 7155257831399816348261)
            ·
              rfl

theorem cell19_211635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 11].length) (baseStart_211635 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211635 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211635 prefixEnd_211635 := by exact prefixLift 211635
  have htrace : WordTrace (prefixWord ++ tailWord_211635) baseStart_211635 baseEnd_211635 := by
    simpa [prefixWord, tailWord_211635, baseEnd_211635] using wordTrace_append hprefix tailTrace_211635
  have hstable : (prefixWord ++ tailWord_211635).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211635).length < 2 ^ (prefixWord ++ tailWord_211635).sum := by decide
  have hdescent : baseEnd_211635 < baseStart_211635 := by decide
  rcases family_descends (prefixWord ++ tailWord_211635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211711 : List Nat := [1, 1, 2, 2, 1, 3, 1, 8]
def baseStart_211711 : Nat := 118140960795 + 211711 * 2 ^ 59
def prefixEnd_211711 : Nat := 4983230072969 + 3 ^ 40 * 211711 * 2
def baseEnd_211711 : Nat := 64420446129852689445253

theorem tailTrace_211711 : CollatzResearch.WordTrace tailWord_211711 prefixEnd_211711 64420446129852689445253 := by
  unfold tailWord_211711
  simp only [CollatzResearch.WordTrace]
  refine ⟨7721734536014679205274987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5147823024009786136849991 7721734536014679205274987)
  ·
    refine ⟨11582601804022018807912481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7721734536014679205274987 11582601804022018807912481)
    ·
      refine ⟨8686951353016514105934361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11582601804022018807912481 8686951353016514105934361)
      ·
        refine ⟨6515213514762385579450771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8686951353016514105934361 6515213514762385579450771)
        ·
          refine ⟨9772820272143578369176157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6515213514762385579450771 9772820272143578369176157)
          ·
            refine ⟨3664807602053841888441059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9772820272143578369176157 3664807602053841888441059)
            ·
              refine ⟨5497211403080762832661589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3664807602053841888441059 5497211403080762832661589)
              ·
                refine ⟨64420446129852689445253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5497211403080762832661589 64420446129852689445253)
                ·
                  rfl

theorem cell19_211711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 8].length) (baseStart_211711 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211711 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211711 prefixEnd_211711 := by exact prefixLift 211711
  have htrace : WordTrace (prefixWord ++ tailWord_211711) baseStart_211711 baseEnd_211711 := by
    simpa [prefixWord, tailWord_211711, baseEnd_211711] using wordTrace_append hprefix tailTrace_211711
  have hstable : (prefixWord ++ tailWord_211711).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211711).length < 2 ^ (prefixWord ++ tailWord_211711).sum := by decide
  have hdescent : baseEnd_211711 < baseStart_211711 := by decide
  rcases family_descends (prefixWord ++ tailWord_211711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211804 : List Nat := [2, 2, 4, 2, 1, 8]
def baseStart_211804 : Nat := 118140960795 + 211804 * 2 ^ 59
def prefixEnd_211804 : Nat := 4983230072969 + 3 ^ 40 * 211804 * 2
def baseEnd_211804 : Nat := 7160971624361781042037

theorem tailTrace_211804 : CollatzResearch.WordTrace tailWord_211804 prefixEnd_211804 7160971624361781042037 := by
  unfold tailWord_211804
  simp only [CollatzResearch.WordTrace]
  refine ⟨3862563262338878044205233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5150084349785170725606977 3862563262338878044205233)
  ·
    refine ⟨2896922446754158533153925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3862563262338878044205233 2896922446754158533153925)
    ·
      refine ⟨543172958766404724966361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2896922446754158533153925 543172958766404724966361)
      ·
        refine ⟨407379719074803543724771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543172958766404724966361 407379719074803543724771)
        ·
          refine ⟨611069578612205315587157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407379719074803543724771 611069578612205315587157)
          ·
            refine ⟨7160971624361781042037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 611069578612205315587157 7160971624361781042037)
            ·
              rfl

theorem cell19_211804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 8].length) (baseStart_211804 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211804 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211804 prefixEnd_211804 := by exact prefixLift 211804
  have htrace : WordTrace (prefixWord ++ tailWord_211804) baseStart_211804 baseEnd_211804 := by
    simpa [prefixWord, tailWord_211804, baseEnd_211804] using wordTrace_append hprefix tailTrace_211804
  have hstable : (prefixWord ++ tailWord_211804).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211804).length < 2 ^ (prefixWord ++ tailWord_211804).sum := by decide
  have hdescent : baseEnd_211804 < baseStart_211804 := by decide
  rcases family_descends (prefixWord ++ tailWord_211804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211863 : List Nat := [1, 1, 3, 3, 1, 2, 8]
def baseStart_211863 : Nat := 118140960795 + 211863 * 2 ^ 59
def prefixEnd_211863 : Nat := 4983230072969 + 3 ^ 40 * 211863 * 2
def baseEnd_211863 : Nat := 21488899141453791355687

theorem tailTrace_211863 : CollatzResearch.WordTrace tailWord_211863 prefixEnd_211863 21488899141453791355687 := by
  unfold tailWord_211863
  simp only [CollatzResearch.WordTrace]
  refine ⟨7727278431464009164808243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5151518954309339443205495 7727278431464009164808243)
  ·
    refine ⟨11590917647196013747212365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7727278431464009164808243 11590917647196013747212365)
    ·
      refine ⟨4346594117698505155204637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11590917647196013747212365 4346594117698505155204637)
      ·
        refine ⟨1629972794136939433201739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4346594117698505155204637 1629972794136939433201739)
        ·
          refine ⟨2444959191205409149802609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1629972794136939433201739 2444959191205409149802609)
          ·
            refine ⟨1833719393404056862351957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2444959191205409149802609 1833719393404056862351957)
            ·
              refine ⟨21488899141453791355687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1833719393404056862351957 21488899141453791355687)
              ·
                rfl

theorem cell19_211863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_211863 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211863 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211863 prefixEnd_211863 := by exact prefixLift 211863
  have htrace : WordTrace (prefixWord ++ tailWord_211863) baseStart_211863 baseEnd_211863 := by
    simpa [prefixWord, tailWord_211863, baseEnd_211863] using wordTrace_append hprefix tailTrace_211863
  have hstable : (prefixWord ++ tailWord_211863).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211863).length < 2 ^ (prefixWord ++ tailWord_211863).sum := by decide
  have hdescent : baseEnd_211863 < baseStart_211863 := by decide
  rcases family_descends (prefixWord ++ tailWord_211863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211897 : List Nat := [1, 2, 1, 4, 2, 4, 2, 3]
def baseStart_211897 : Nat := 118140960795 + 211897 * 2 ^ 59
def prefixEnd_211897 : Nat := 4983230072969 + 3 ^ 40 * 211897 * 2
def baseEnd_211897 : Nat := 64477043108659369311413

theorem tailTrace_211897 : CollatzResearch.WordTrace tailWord_211897 prefixEnd_211897 64477043108659369311413 := by
  unfold tailWord_211897
  simp only [CollatzResearch.WordTrace]
  refine ⟨7728518513340832971545945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5152345675560555314363963 7728518513340832971545945)
  ·
    refine ⟨5796388885005624728659459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7728518513340832971545945 5796388885005624728659459)
    ·
      refine ⟨8694583327508437092989189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5796388885005624728659459 8694583327508437092989189)
      ·
        refine ⟨1630234373907831954935473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8694583327508437092989189 1630234373907831954935473)
        ·
          refine ⟨1222675780430873966201605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1630234373907831954935473 1222675780430873966201605)
          ·
            refine ⟨229251708830788868662801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1222675780430873966201605 229251708830788868662801)
            ·
              refine ⟨171938781623091651497101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229251708830788868662801 171938781623091651497101)
              ·
                refine ⟨64477043108659369311413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 171938781623091651497101 64477043108659369311413)
                ·
                  rfl

theorem cell19_211897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 3].length) (baseStart_211897 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211897 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211897 prefixEnd_211897 := by exact prefixLift 211897
  have htrace : WordTrace (prefixWord ++ tailWord_211897) baseStart_211897 baseEnd_211897 := by
    simpa [prefixWord, tailWord_211897, baseEnd_211897] using wordTrace_append hprefix tailTrace_211897
  have hstable : (prefixWord ++ tailWord_211897).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211897).length < 2 ^ (prefixWord ++ tailWord_211897).sum := by decide
  have hdescent : baseEnd_211897 < baseStart_211897 := by decide
  rcases family_descends (prefixWord ++ tailWord_211897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211910 : List Nat := [6, 1, 3, 1, 1, 2, 5]
def baseStart_211910 : Nat := 118140960795 + 211910 * 2 ^ 59
def prefixEnd_211910 : Nat := 4983230072969 + 3 ^ 40 * 211910 * 2
def baseEnd_211910 : Nat := 21493666270493063674163

theorem tailTrace_211910 : CollatzResearch.WordTrace tailWord_211910 prefixEnd_211910 21493666270493063674163 := by
  unfold tailWord_211910
  simp only [CollatzResearch.WordTrace]
  refine ⟨241531020696679255992787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5152661774862490794512789 241531020696679255992787)
  ·
    refine ⟨362296531045018883989181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 241531020696679255992787 362296531045018883989181)
    ·
      refine ⟨135861199141882081495943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 362296531045018883989181 135861199141882081495943)
      ·
        refine ⟨203791798712823122243915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135861199141882081495943 203791798712823122243915)
        ·
          refine ⟨305687698069234683365873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 203791798712823122243915 305687698069234683365873)
          ·
            refine ⟨229265773551926012524405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305687698069234683365873 229265773551926012524405)
            ·
              refine ⟨21493666270493063674163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229265773551926012524405 21493666270493063674163)
              ·
                rfl

theorem cell19_211910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 5].length) (baseStart_211910 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211910 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211910 prefixEnd_211910 := by exact prefixLift 211910
  have htrace : WordTrace (prefixWord ++ tailWord_211910) baseStart_211910 baseEnd_211910 := by
    simpa [prefixWord, tailWord_211910, baseEnd_211910] using wordTrace_append hprefix tailTrace_211910
  have hstable : (prefixWord ++ tailWord_211910).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211910).length < 2 ^ (prefixWord ++ tailWord_211910).sum := by decide
  have hdescent : baseEnd_211910 < baseStart_211910 := by decide
  rcases family_descends (prefixWord ++ tailWord_211910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211918 : List Nat := [4, 1, 1, 1, 2, 5, 5]
def baseStart_211918 : Nat := 118140960795 + 211918 * 2 ^ 59
def prefixEnd_211918 : Nat := 4983230072969 + 3 ^ 40 * 211918 * 2
def baseEnd_211918 : Nat := 21494477696712514281563

theorem tailTrace_211918 : CollatzResearch.WordTrace tailWord_211918 prefixEnd_211918 21494477696712514281563 := by
  unfold tailWord_211918
  simp only [CollatzResearch.WordTrace]
  refine ⟨966160555783094194757551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5152856297509835705373605 966160555783094194757551)
  ·
    refine ⟨1449240833674641292136327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 966160555783094194757551 1449240833674641292136327)
    ·
      refine ⟨2173861250511961938204491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1449240833674641292136327 2173861250511961938204491)
      ·
        refine ⟨3260791875767942907306737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2173861250511961938204491 3260791875767942907306737)
        ·
          refine ⟨2445593906825957180480053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3260791875767942907306737 2445593906825957180480053)
          ·
            refine ⟨229274428764933485670005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2445593906825957180480053 229274428764933485670005)
            ·
              refine ⟨21494477696712514281563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229274428764933485670005 21494477696712514281563)
              ·
                rfl

theorem cell19_211918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 5, 5].length) (baseStart_211918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211918 prefixEnd_211918 := by exact prefixLift 211918
  have htrace : WordTrace (prefixWord ++ tailWord_211918) baseStart_211918 baseEnd_211918 := by
    simpa [prefixWord, tailWord_211918, baseEnd_211918] using wordTrace_append hprefix tailTrace_211918
  have hstable : (prefixWord ++ tailWord_211918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211918).length < 2 ^ (prefixWord ++ tailWord_211918).sum := by decide
  have hdescent : baseEnd_211918 < baseStart_211918 := by decide
  rcases family_descends (prefixWord ++ tailWord_211918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_211986 : List Nat := [3, 2, 5, 1, 2, 1, 1, 4]
def baseStart_211986 : Nat := 118140960795 + 211986 * 2 ^ 59
def prefixEnd_211986 : Nat := 4983230072969 + 3 ^ 40 * 211986 * 2
def baseEnd_211986 : Nat := 64504124458733533333393

theorem tailTrace_211986 : CollatzResearch.WordTrace tailWord_211986 prefixEnd_211986 64504124458733533333393 := by
  unfold tailWord_211986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1932941152504600292883953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5154509740012267447690541 1932941152504600292883953)
  ·
    refine ⟨1449705864378450219662965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1932941152504600292883953 1449705864378450219662965)
    ·
      refine ⟨135909924785479708093403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1449705864378450219662965 135909924785479708093403)
      ·
        refine ⟨203864887178219562140105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 135909924785479708093403 203864887178219562140105)
        ·
          refine ⟨152898665383664671605079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203864887178219562140105 152898665383664671605079)
          ·
            refine ⟨229347998075497007407619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152898665383664671605079 229347998075497007407619)
            ·
              refine ⟨344021997113245511111429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 229347998075497007407619 344021997113245511111429)
              ·
                refine ⟨64504124458733533333393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 344021997113245511111429 64504124458733533333393)
                ·
                  rfl

theorem cell19_211986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_211986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_211986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_211986 prefixEnd_211986 := by exact prefixLift 211986
  have htrace : WordTrace (prefixWord ++ tailWord_211986) baseStart_211986 baseEnd_211986 := by
    simpa [prefixWord, tailWord_211986, baseEnd_211986] using wordTrace_append hprefix tailTrace_211986
  have hstable : (prefixWord ++ tailWord_211986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_211986).length < 2 ^ (prefixWord ++ tailWord_211986).sum := by decide
  have hdescent : baseEnd_211986 < baseStart_211986 := by decide
  rcases family_descends (prefixWord ++ tailWord_211986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212053 : List Nat := [1, 3, 2, 2, 1, 2, 2, 6]
def baseStart_212053 : Nat := 118140960795 + 212053 * 2 ^ 59
def prefixEnd_212053 : Nat := 4983230072969 + 3 ^ 40 * 212053 * 2
def baseEnd_212053 : Nat := 64524511542497229844321

theorem tailTrace_212053 : CollatzResearch.WordTrace tailWord_212053 prefixEnd_212053 64524511542497229844321 := by
  unfold tailWord_212053
  simp only [CollatzResearch.WordTrace]
  refine ⟨7734208300775671614224813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5156138867183781076149875 7734208300775671614224813)
  ·
    refine ⟨2900328112790876855334305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7734208300775671614224813 2900328112790876855334305)
    ·
      refine ⟨2175246084593157641500729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2900328112790876855334305 2175246084593157641500729)
      ·
        refine ⟨1631434563444868231125547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2175246084593157641500729 1631434563444868231125547)
        ·
          refine ⟨2447151845167302346688321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1631434563444868231125547 2447151845167302346688321)
          ·
            refine ⟨1835363883875476760016241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2447151845167302346688321 1835363883875476760016241)
            ·
              refine ⟨1376522912906607570012181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1835363883875476760016241 1376522912906607570012181)
              ·
                refine ⟨64524511542497229844321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1376522912906607570012181 64524511542497229844321)
                ·
                  rfl

theorem cell19_212053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 6].length) (baseStart_212053 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212053 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212053 prefixEnd_212053 := by exact prefixLift 212053
  have htrace : WordTrace (prefixWord ++ tailWord_212053) baseStart_212053 baseEnd_212053 := by
    simpa [prefixWord, tailWord_212053, baseEnd_212053] using wordTrace_append hprefix tailTrace_212053
  have hstable : (prefixWord ++ tailWord_212053).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212053).length < 2 ^ (prefixWord ++ tailWord_212053).sum := by decide
  have hdescent : baseEnd_212053 < baseStart_212053 := by decide
  rcases family_descends (prefixWord ++ tailWord_212053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212066 : List Nat := [3, 3, 2, 2, 1, 3, 2, 3]
def baseStart_212066 : Nat := 118140960795 + 212066 * 2 ^ 59
def prefixEnd_212066 : Nat := 4983230072969 + 3 ^ 40 * 212066 * 2
def baseEnd_212066 : Nat := 64528467245317051555397

theorem tailTrace_212066 : CollatzResearch.WordTrace tailWord_212066 prefixEnd_212066 64528467245317051555397 := by
  unfold tailWord_212066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1933670612432143708612013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5156454966485716556298701 1933670612432143708612013)
  ·
    refine ⟨725126479662053890729505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1933670612432143708612013 725126479662053890729505)
    ·
      refine ⟨543844859746540418047129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 725126479662053890729505 543844859746540418047129)
      ·
        refine ⟨407883644809905313535347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 543844859746540418047129 407883644809905313535347)
        ·
          refine ⟨611825467214857970303021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 407883644809905313535347 611825467214857970303021)
          ·
            refine ⟨229434550205571738863633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 611825467214857970303021 229434550205571738863633)
            ·
              refine ⟨172075912654178804147725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 229434550205571738863633 172075912654178804147725)
              ·
                refine ⟨64528467245317051555397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172075912654178804147725 64528467245317051555397)
                ·
                  rfl

theorem cell19_212066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 3].length) (baseStart_212066 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212066 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212066 prefixEnd_212066 := by exact prefixLift 212066
  have htrace : WordTrace (prefixWord ++ tailWord_212066) baseStart_212066 baseEnd_212066 := by
    simpa [prefixWord, tailWord_212066, baseEnd_212066] using wordTrace_append hprefix tailTrace_212066
  have hstable : (prefixWord ++ tailWord_212066).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212066).length < 2 ^ (prefixWord ++ tailWord_212066).sum := by decide
  have hdescent : baseEnd_212066 < baseStart_212066 := by decide
  rcases family_descends (prefixWord ++ tailWord_212066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212085 : List Nat := [1, 3, 4, 3, 2, 1, 5]
def baseStart_212085 : Nat := 118140960795 + 212085 * 2 ^ 59
def prefixEnd_212085 : Nat := 4983230072969 + 3 ^ 40 * 212085 * 2
def baseEnd_212085 : Nat := 21511416219043545711041

theorem tailTrace_212085 : CollatzResearch.WordTrace tailWord_212085 prefixEnd_212085 21511416219043545711041 := by
  unfold tailWord_212085
  simp only [CollatzResearch.WordTrace]
  refine ⟨7735375436659741079389709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5156916957773160719593139 7735375436659741079389709)
  ·
    refine ⟨2900765788747402904771141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7735375436659741079389709 2900765788747402904771141)
    ·
      refine ⟨543893585390138044644589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2900765788747402904771141 543893585390138044644589)
      ·
        refine ⟨203960094521301766741721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 543893585390138044644589 203960094521301766741721)
        ·
          refine ⟨152970070890976325056291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 203960094521301766741721 152970070890976325056291)
          ·
            refine ⟨229455106336464487584437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 152970070890976325056291 229455106336464487584437)
            ·
              refine ⟨21511416219043545711041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229455106336464487584437 21511416219043545711041)
              ·
                rfl

theorem cell19_212085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 5].length) (baseStart_212085 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212085 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212085 prefixEnd_212085 := by exact prefixLift 212085
  have htrace : WordTrace (prefixWord ++ tailWord_212085) baseStart_212085 baseEnd_212085 := by
    simpa [prefixWord, tailWord_212085, baseEnd_212085] using wordTrace_append hprefix tailTrace_212085
  have hstable : (prefixWord ++ tailWord_212085).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212085).length < 2 ^ (prefixWord ++ tailWord_212085).sum := by decide
  have hdescent : baseEnd_212085 < baseStart_212085 := by decide
  rcases family_descends (prefixWord ++ tailWord_212085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212089 : List Nat := [1, 2, 1, 3, 5, 2, 5]
def baseStart_212089 : Nat := 118140960795 + 212089 * 2 ^ 59
def prefixEnd_212089 : Nat := 4983230072969 + 3 ^ 40 * 212089 * 2
def baseEnd_212089 : Nat := 21511821932153271014741

theorem tailTrace_212089 : CollatzResearch.WordTrace tailWord_212089 prefixEnd_212089 21511821932153271014741 := by
  unfold tailWord_212089
  simp only [CollatzResearch.WordTrace]
  refine ⟨7735521328645249762535321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5157014219096833175023547 7735521328645249762535321)
  ·
    refine ⟨5801640996483937321901491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7735521328645249762535321 5801640996483937321901491)
    ·
      refine ⟨8702461494725905982852237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5801640996483937321901491 8702461494725905982852237)
      ·
        refine ⟨3263423060522214743569589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8702461494725905982852237 3263423060522214743569589)
        ·
          refine ⟨305945911923957632209649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3263423060522214743569589 305945911923957632209649)
          ·
            refine ⟨229459433942968224157237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 305945911923957632209649 229459433942968224157237)
            ·
              refine ⟨21511821932153271014741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229459433942968224157237 21511821932153271014741)
              ·
                rfl

theorem cell19_212089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 5].length) (baseStart_212089 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212089 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212089 prefixEnd_212089 := by exact prefixLift 212089
  have htrace : WordTrace (prefixWord ++ tailWord_212089) baseStart_212089 baseEnd_212089 := by
    simpa [prefixWord, tailWord_212089, baseEnd_212089] using wordTrace_append hprefix tailTrace_212089
  have hstable : (prefixWord ++ tailWord_212089).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212089).length < 2 ^ (prefixWord ++ tailWord_212089).sum := by decide
  have hdescent : baseEnd_212089 < baseStart_212089 := by decide
  rcases family_descends (prefixWord ++ tailWord_212089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212129 : List Nat := [1, 2, 3, 3, 1, 1, 1, 7]
def baseStart_212129 : Nat := 118140960795 + 212129 * 2 ^ 59
def prefixEnd_212129 : Nat := 4983230072969 + 3 ^ 40 * 212129 * 2
def baseEnd_212129 : Nat := 64547637189751572155225

theorem tailTrace_212129 : CollatzResearch.WordTrace tailWord_212129 prefixEnd_212129 64547637189751572155225 := by
  unfold tailWord_212129
  simp only [CollatzResearch.WordTrace]
  refine ⟨7736980248500336593991441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5157986832333557729327627 7736980248500336593991441)
  ·
    refine ⟨5802735186375252445493581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7736980248500336593991441 5802735186375252445493581)
    ·
      refine ⟨2176025694890719667060093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5802735186375252445493581 2176025694890719667060093)
      ·
        refine ⟨816009635584019875147535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2176025694890719667060093 816009635584019875147535)
        ·
          refine ⟨1224014453376029812721303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 816009635584019875147535 1224014453376029812721303)
          ·
            refine ⟨1836021680064044719081955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1224014453376029812721303 1836021680064044719081955)
            ·
              refine ⟨2754032520096067078622933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1836021680064044719081955 2754032520096067078622933)
              ·
                refine ⟨64547637189751572155225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2754032520096067078622933 64547637189751572155225)
                ·
                  rfl

theorem cell19_212129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 7].length) (baseStart_212129 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212129 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212129 prefixEnd_212129 := by exact prefixLift 212129
  have htrace : WordTrace (prefixWord ++ tailWord_212129) baseStart_212129 baseEnd_212129 := by
    simpa [prefixWord, tailWord_212129, baseEnd_212129] using wordTrace_append hprefix tailTrace_212129
  have hstable : (prefixWord ++ tailWord_212129).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212129).length < 2 ^ (prefixWord ++ tailWord_212129).sum := by decide
  have hdescent : baseEnd_212129 < baseStart_212129 := by decide
  rcases family_descends (prefixWord ++ tailWord_212129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212180 : List Nat := [2, 4, 1, 4, 1, 1, 3, 3]
def baseStart_212180 : Nat := 118140960795 + 212180 * 2 ^ 59
def prefixEnd_212180 : Nat := 4983230072969 + 3 ^ 40 * 212180 * 2
def baseEnd_212180 : Nat := 64563155716198565021753

theorem tailTrace_212180 : CollatzResearch.WordTrace tailWord_212180 prefixEnd_212180 64563155716198565021753 := by
  unfold tailWord_212180
  simp only [CollatzResearch.WordTrace]
  refine ⟨3869420185657786152048997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5159226914210381536065329 3869420185657786152048997)
  ·
    refine ⟨725516284810834903509187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3869420185657786152048997 725516284810834903509187)
    ·
      refine ⟨1088274427216252355263781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 725516284810834903509187 1088274427216252355263781)
      ·
        refine ⟨204051455103047316611959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1088274427216252355263781 204051455103047316611959)
        ·
          refine ⟨306077182654570974917939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 204051455103047316611959 306077182654570974917939)
          ·
            refine ⟨459115773981856462376909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306077182654570974917939 459115773981856462376909)
            ·
              refine ⟨172168415243196173391341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459115773981856462376909 172168415243196173391341)
              ·
                refine ⟨64563155716198565021753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172168415243196173391341 64563155716198565021753)
                ·
                  rfl

theorem cell19_212180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 3].length) (baseStart_212180 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212180 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212180 prefixEnd_212180 := by exact prefixLift 212180
  have htrace : WordTrace (prefixWord ++ tailWord_212180) baseStart_212180 baseEnd_212180 := by
    simpa [prefixWord, tailWord_212180, baseEnd_212180] using wordTrace_append hprefix tailTrace_212180
  have hstable : (prefixWord ++ tailWord_212180).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212180).length < 2 ^ (prefixWord ++ tailWord_212180).sum := by decide
  have hdescent : baseEnd_212180 < baseStart_212180 := by decide
  rcases family_descends (prefixWord ++ tailWord_212180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212258 : List Nat := [3, 3, 1, 1, 5, 1, 5]
def baseStart_212258 : Nat := 118140960795 + 212258 * 2 ^ 59
def prefixEnd_212258 : Nat := 4983230072969 + 3 ^ 40 * 212258 * 2
def baseEnd_212258 : Nat := 21528963311039165096069

theorem tailTrace_212258 : CollatzResearch.WordTrace tailWord_212258 prefixEnd_212258 21528963311039165096069 := by
  unfold tailWord_212258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1935421316258247906359357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5161123510021994416958285 1935421316258247906359357)
  ·
    refine ⟨725782993596842964884759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1935421316258247906359357 725782993596842964884759)
    ·
      refine ⟨1088674490395264447327139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 725782993596842964884759 1088674490395264447327139)
      ·
        refine ⟨1633011735592896670990709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1088674490395264447327139 1633011735592896670990709)
        ·
          refine ⟨153094850211834062905379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1633011735592896670990709 153094850211834062905379)
          ·
            refine ⟨229642275317751094358069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153094850211834062905379 229642275317751094358069)
            ·
              refine ⟨21528963311039165096069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 229642275317751094358069 21528963311039165096069)
              ·
                rfl

theorem cell19_212258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 5, 1, 5].length) (baseStart_212258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212258 prefixEnd_212258 := by exact prefixLift 212258
  have htrace : WordTrace (prefixWord ++ tailWord_212258) baseStart_212258 baseEnd_212258 := by
    simpa [prefixWord, tailWord_212258, baseEnd_212258] using wordTrace_append hprefix tailTrace_212258
  have hstable : (prefixWord ++ tailWord_212258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212258).length < 2 ^ (prefixWord ++ tailWord_212258).sum := by decide
  have hdescent : baseEnd_212258 < baseStart_212258 := by decide
  rcases family_descends (prefixWord ++ tailWord_212258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212300 : List Nat := [2, 2, 1, 3, 2, 2, 2, 5]
def baseStart_212300 : Nat := 118140960795 + 212300 * 2 ^ 59
def prefixEnd_212300 : Nat := 4983230072969 + 3 ^ 40 * 212300 * 2
def baseEnd_212300 : Nat := 64599669896073842354759

theorem tailTrace_212300 : CollatzResearch.WordTrace tailWord_212300 prefixEnd_212300 64599669896073842354759 := by
  unfold tailWord_212300
  simp only [CollatzResearch.WordTrace]
  refine ⟨3871608565440416399233177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5162144753920555198977569 3871608565440416399233177)
  ·
    refine ⟨2903706424080312299424883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3871608565440416399233177 2903706424080312299424883)
    ·
      refine ⟨4355559636120468449137325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2903706424080312299424883 4355559636120468449137325)
      ·
        refine ⟨1633334863545175668426497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4355559636120468449137325 1633334863545175668426497)
        ·
          refine ⟨1225001147658881751319873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1633334863545175668426497 1225001147658881751319873)
          ·
            refine ⟨918750860744161313489905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1225001147658881751319873 918750860744161313489905)
            ·
              refine ⟨689063145558120985117429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 918750860744161313489905 689063145558120985117429)
              ·
                refine ⟨64599669896073842354759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 689063145558120985117429 64599669896073842354759)
                ·
                  rfl

theorem cell19_212300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 5].length) (baseStart_212300 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212300 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212300 prefixEnd_212300 := by exact prefixLift 212300
  have htrace : WordTrace (prefixWord ++ tailWord_212300) baseStart_212300 baseEnd_212300 := by
    simpa [prefixWord, tailWord_212300, baseEnd_212300] using wordTrace_append hprefix tailTrace_212300
  have hstable : (prefixWord ++ tailWord_212300).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212300).length < 2 ^ (prefixWord ++ tailWord_212300).sum := by decide
  have hdescent : baseEnd_212300 < baseStart_212300 := by decide
  rcases family_descends (prefixWord ++ tailWord_212300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212353 : List Nat := [1, 2, 4, 3, 2, 1, 3, 3]
def baseStart_212353 : Nat := 118140960795 + 212353 * 2 ^ 59
def prefixEnd_212353 : Nat := 4983230072969 + 3 ^ 40 * 212353 * 2
def baseEnd_212353 : Nat := 64615796992185423176837

theorem tailTrace_212353 : CollatzResearch.WordTrace tailWord_212353 prefixEnd_212353 64615796992185423176837 := by
  unfold tailWord_212353
  simp only [CollatzResearch.WordTrace]
  refine ⟨7745150199688822850145713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5163433466459215233430475 7745150199688822850145713)
  ·
    refine ⟨5808862649766617137609285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7745150199688822850145713 5808862649766617137609285)
    ·
      refine ⟨1089161746831240713301741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5808862649766617137609285 1089161746831240713301741)
      ·
        refine ⟨408435655061715267488153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1089161746831240713301741 408435655061715267488153)
        ·
          refine ⟨306326741296286450616115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408435655061715267488153 306326741296286450616115)
          ·
            refine ⟨459490111944429675924173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306326741296286450616115 459490111944429675924173)
            ·
              refine ⟨172308791979161128471565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459490111944429675924173 172308791979161128471565)
              ·
                refine ⟨64615796992185423176837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172308791979161128471565 64615796992185423176837)
                ·
                  rfl

theorem cell19_212353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 3].length) (baseStart_212353 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212353 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212353 prefixEnd_212353 := by exact prefixLift 212353
  have htrace : WordTrace (prefixWord ++ tailWord_212353) baseStart_212353 baseEnd_212353 := by
    simpa [prefixWord, tailWord_212353, baseEnd_212353] using wordTrace_append hprefix tailTrace_212353
  have hstable : (prefixWord ++ tailWord_212353).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212353).length < 2 ^ (prefixWord ++ tailWord_212353).sum := by decide
  have hdescent : baseEnd_212353 < baseStart_212353 := by decide
  rcases family_descends (prefixWord ++ tailWord_212353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212355 : List Nat := [1, 1, 1, 3, 5, 2, 3, 3]
def baseStart_212355 : Nat := 118140960795 + 212355 * 2 ^ 59
def prefixEnd_212355 : Nat := 4983230072969 + 3 ^ 40 * 212355 * 2
def baseEnd_212355 : Nat := 64616405561850011132387

theorem tailTrace_212355 : CollatzResearch.WordTrace tailWord_212355 prefixEnd_212355 64616405561850011132387 := by
  unfold tailWord_212355
  simp only [CollatzResearch.WordTrace]
  refine ⟨7745223145681577191718519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5163482097121051461145679 7745223145681577191718519)
  ·
    refine ⟨11617834718522365787577779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7745223145681577191718519 11617834718522365787577779)
    ·
      refine ⟨17426752077783548681366669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11617834718522365787577779 17426752077783548681366669)
      ·
        refine ⟨6535032029168830755512501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17426752077783548681366669 6535032029168830755512501)
        ·
          refine ⟨612659252734577883329297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6535032029168830755512501 612659252734577883329297)
          ·
            refine ⟨459494439550933412496973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 612659252734577883329297 459494439550933412496973)
            ·
              refine ⟨172310414831600029686365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 459494439550933412496973 172310414831600029686365)
              ·
                refine ⟨64616405561850011132387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172310414831600029686365 64616405561850011132387)
                ·
                  rfl

theorem cell19_212355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 3].length) (baseStart_212355 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212355 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212355 prefixEnd_212355 := by exact prefixLift 212355
  have htrace : WordTrace (prefixWord ++ tailWord_212355) baseStart_212355 baseEnd_212355 := by
    simpa [prefixWord, tailWord_212355, baseEnd_212355] using wordTrace_append hprefix tailTrace_212355
  have hstable : (prefixWord ++ tailWord_212355).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212355).length < 2 ^ (prefixWord ++ tailWord_212355).sum := by decide
  have hdescent : baseEnd_212355 < baseStart_212355 := by decide
  rcases family_descends (prefixWord ++ tailWord_212355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212412 : List Nat := [2, 2, 2, 4, 2, 1, 1, 5]
def baseStart_212412 : Nat := 118140960795 + 212412 * 2 ^ 59
def prefixEnd_212412 : Nat := 4983230072969 + 3 ^ 40 * 212412 * 2
def baseEnd_212412 : Nat := 64633749797290767865565

theorem tailTrace_212412 : CollatzResearch.WordTrace tailWord_212412 prefixEnd_212412 64633749797290767865565 := by
  unfold tailWord_212412
  simp only [CollatzResearch.WordTrace]
  refine ⟨3873651053237537963271745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5164868070983383951028993 3873651053237537963271745)
  ·
    refine ⟨2905238289928153472453809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3873651053237537963271745 2905238289928153472453809)
    ·
      refine ⟨2178928717446115104340357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2905238289928153472453809 2178928717446115104340357)
      ·
        refine ⟨408549134521146582063817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2178928717446115104340357 408549134521146582063817)
        ·
          refine ⟨306411850890859936547863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 408549134521146582063817 306411850890859936547863)
          ·
            refine ⟨459617776336289904821795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 306411850890859936547863 459617776336289904821795)
            ·
              refine ⟨689426664504434857232693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 459617776336289904821795 689426664504434857232693)
              ·
                refine ⟨64633749797290767865565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 689426664504434857232693 64633749797290767865565)
                ·
                  rfl

theorem cell19_212412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_212412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212412 prefixEnd_212412 := by exact prefixLift 212412
  have htrace : WordTrace (prefixWord ++ tailWord_212412) baseStart_212412 baseEnd_212412 := by
    simpa [prefixWord, tailWord_212412, baseEnd_212412] using wordTrace_append hprefix tailTrace_212412
  have hstable : (prefixWord ++ tailWord_212412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212412).length < 2 ^ (prefixWord ++ tailWord_212412).sum := by decide
  have hdescent : baseEnd_212412 < baseStart_212412 := by decide
  rcases family_descends (prefixWord ++ tailWord_212412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212469 : List Nat := [1, 3, 5, 1, 1, 1, 2, 5]
def baseStart_212469 : Nat := 118140960795 + 212469 * 2 ^ 59
def prefixEnd_212469 : Nat := 4983230072969 + 3 ^ 40 * 212469 * 2
def baseEnd_212469 : Nat := 64651094032731524598743

theorem tailTrace_212469 : CollatzResearch.WordTrace tailWord_212469 prefixEnd_212469 64651094032731524598743 := by
  unfold tailWord_212469
  simp only [CollatzResearch.WordTrace]
  refine ⟨7749381067268574661368461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5166254044845716440912307 7749381067268574661368461)
  ·
    refine ⟨2906017900225715498013173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7749381067268574661368461 2906017900225715498013173)
    ·
      refine ⟨272439178146160827938735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2906017900225715498013173 272439178146160827938735)
      ·
        refine ⟨408658767219241241908103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272439178146160827938735 408658767219241241908103)
        ·
          refine ⟨612988150828861862862155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 408658767219241241908103 612988150828861862862155)
          ·
            refine ⟨919482226243292794293233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 612988150828861862862155 919482226243292794293233)
            ·
              refine ⟨689611669682469595719925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 919482226243292794293233 689611669682469595719925)
              ·
                refine ⟨64651094032731524598743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 689611669682469595719925 64651094032731524598743)
                ·
                  rfl

theorem cell19_212469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_212469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212469 prefixEnd_212469 := by exact prefixLift 212469
  have htrace : WordTrace (prefixWord ++ tailWord_212469) baseStart_212469 baseEnd_212469 := by
    simpa [prefixWord, tailWord_212469, baseEnd_212469] using wordTrace_append hprefix tailTrace_212469
  have hstable : (prefixWord ++ tailWord_212469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212469).length < 2 ^ (prefixWord ++ tailWord_212469).sum := by decide
  have hdescent : baseEnd_212469 < baseStart_212469 := by decide
  rcases family_descends (prefixWord ++ tailWord_212469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212486 : List Nat := [6, 2, 1, 1, 9]
def baseStart_212486 : Nat := 118140960795 + 212486 * 2 ^ 59
def prefixEnd_212486 : Nat := 4983230072969 + 3 ^ 40 * 212486 * 2
def baseEnd_212486 : Nat := 2394676550921500822997

theorem tailTrace_212486 : CollatzResearch.WordTrace tailWord_212486 prefixEnd_212486 2394676550921500822997 := by
  unfold tailWord_212486
  simp only [CollatzResearch.WordTrace]
  refine ⟨242187534631468330148041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5166667405471324376491541 242187534631468330148041)
  ·
    refine ⟨181640650973601247611031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 242187534631468330148041 181640650973601247611031)
    ·
      refine ⟨272460976460401871416547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 181640650973601247611031 272460976460401871416547)
      ·
        refine ⟨408691464690602807124821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272460976460401871416547 408691464690602807124821)
        ·
          refine ⟨2394676550921500822997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 408691464690602807124821 2394676550921500822997)
          ·
            rfl

theorem cell19_212486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 9].length) (baseStart_212486 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212486 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212486 prefixEnd_212486 := by exact prefixLift 212486
  have htrace : WordTrace (prefixWord ++ tailWord_212486) baseStart_212486 baseEnd_212486 := by
    simpa [prefixWord, tailWord_212486, baseEnd_212486] using wordTrace_append hprefix tailTrace_212486
  have hstable : (prefixWord ++ tailWord_212486).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212486).length < 2 ^ (prefixWord ++ tailWord_212486).sum := by decide
  have hdescent : baseEnd_212486 < baseStart_212486 := by decide
  rcases family_descends (prefixWord ++ tailWord_212486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212492 : List Nat := [2, 2, 1, 2, 12]
def baseStart_212492 : Nat := 118140960795 + 212492 * 2 ^ 59
def prefixEnd_212492 : Nat := 4983230072969 + 3 ^ 40 * 212492 * 2
def baseEnd_212492 : Nat := 2394744169773121706947

theorem tailTrace_212492 : CollatzResearch.WordTrace tailWord_212492 prefixEnd_212492 2394744169773121706947 := by
  unfold tailWord_212492
  simp only [CollatzResearch.WordTrace]
  refine ⟨3875109973092624794727865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5166813297456833059637153 3875109973092624794727865)
  ·
    refine ⟨2906332479819468596045899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3875109973092624794727865 2906332479819468596045899)
    ·
      refine ⟨4359498719729202894068849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2906332479819468596045899 4359498719729202894068849)
      ·
        refine ⟨3269624039796902170551637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4359498719729202894068849 3269624039796902170551637)
        ·
          refine ⟨2394744169773121706947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3269624039796902170551637 2394744169773121706947)
          ·
            rfl

theorem cell19_212492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 12].length) (baseStart_212492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212492 prefixEnd_212492 := by exact prefixLift 212492
  have htrace : WordTrace (prefixWord ++ tailWord_212492) baseStart_212492 baseEnd_212492 := by
    simpa [prefixWord, tailWord_212492, baseEnd_212492] using wordTrace_append hprefix tailTrace_212492
  have hstable : (prefixWord ++ tailWord_212492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212492).length < 2 ^ (prefixWord ++ tailWord_212492).sum := by decide
  have hdescent : baseEnd_212492 < baseStart_212492 := by decide
  rcases family_descends (prefixWord ++ tailWord_212492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212549 : List Nat := [1, 3, 1, 1, 1, 4, 8]
def baseStart_212549 : Nat := 118140960795 + 212549 * 2 ^ 59
def prefixEnd_212549 : Nat := 4983230072969 + 3 ^ 40 * 212549 * 2
def baseEnd_212549 : Nat := 21558478939771680940249

theorem tailTrace_212549 : CollatzResearch.WordTrace tailWord_212549 prefixEnd_212549 21558478939771680940249 := by
  unfold tailWord_212549
  simp only [CollatzResearch.WordTrace]
  refine ⟨7752298906978748324280701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5168199271319165549520467 7752298906978748324280701)
  ·
    refine ⟨2907112090117030621605263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7752298906978748324280701 2907112090117030621605263)
    ·
      refine ⟨4360668135175545932407895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2907112090117030621605263 4360668135175545932407895)
      ·
        refine ⟨6541002202763318898611843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4360668135175545932407895 6541002202763318898611843)
        ·
          refine ⟨9811503304144978347917765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6541002202763318898611843 9811503304144978347917765)
          ·
            refine ⟨1839656869527183440234581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9811503304144978347917765 1839656869527183440234581)
            ·
              refine ⟨21558478939771680940249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1839656869527183440234581 21558478939771680940249)
              ·
                rfl

theorem cell19_212549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 8].length) (baseStart_212549 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212549 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212549 prefixEnd_212549 := by exact prefixLift 212549
  have htrace : WordTrace (prefixWord ++ tailWord_212549) baseStart_212549 baseEnd_212549 := by
    simpa [prefixWord, tailWord_212549, baseEnd_212549] using wordTrace_append hprefix tailTrace_212549
  have hstable : (prefixWord ++ tailWord_212549).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212549).length < 2 ^ (prefixWord ++ tailWord_212549).sum := by decide
  have hdescent : baseEnd_212549 < baseStart_212549 := by decide
  rcases family_descends (prefixWord ++ tailWord_212549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212568 : List Nat := [2, 1, 2, 2, 1, 2, 1, 8]
def baseStart_212568 : Nat := 118140960795 + 212568 * 2 ^ 59
def prefixEnd_212568 : Nat := 4983230072969 + 3 ^ 40 * 212568 * 2
def baseEnd_212568 : Nat := 64681218231128628398473

theorem tailTrace_212568 : CollatzResearch.WordTrace tailWord_212568 prefixEnd_212568 64681218231128628398473 := by
  unfold tailWord_212568
  simp only [CollatzResearch.WordTrace]
  refine ⟨3876495946954957284611179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5168661262606609712814905 3876495946954957284611179)
  ·
    refine ⟨5814743920432435926916769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3876495946954957284611179 5814743920432435926916769)
    ·
      refine ⟨4361057940324326945187577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5814743920432435926916769 4361057940324326945187577)
      ·
        refine ⟨3270793455243245208890683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4361057940324326945187577 3270793455243245208890683)
        ·
          refine ⟨4906190182864867813336025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3270793455243245208890683 4906190182864867813336025)
          ·
            refine ⟨3679642637148650860002019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4906190182864867813336025 3679642637148650860002019)
            ·
              refine ⟨5519463955722976290003029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3679642637148650860002019 5519463955722976290003029)
              ·
                refine ⟨64681218231128628398473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5519463955722976290003029 64681218231128628398473)
                ·
                  rfl

theorem cell19_212568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_212568 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212568 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212568 prefixEnd_212568 := by exact prefixLift 212568
  have htrace : WordTrace (prefixWord ++ tailWord_212568) baseStart_212568 baseEnd_212568 := by
    simpa [prefixWord, tailWord_212568, baseEnd_212568] using wordTrace_append hprefix tailTrace_212568
  have hstable : (prefixWord ++ tailWord_212568).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212568).length < 2 ^ (prefixWord ++ tailWord_212568).sum := by decide
  have hdescent : baseEnd_212568 < baseStart_212568 := by decide
  rcases family_descends (prefixWord ++ tailWord_212568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212585 : List Nat := [1, 2, 1, 1, 1, 4, 6, 3]
def baseStart_212585 : Nat := 118140960795 + 212585 * 2 ^ 59
def prefixEnd_212585 : Nat := 4983230072969 + 3 ^ 40 * 212585 * 2
def baseEnd_212585 : Nat := 64686391073277626020649

theorem tailTrace_212585 : CollatzResearch.WordTrace tailWord_212585 prefixEnd_212585 64686391073277626020649 := by
  unfold tailWord_212585
  simp only [CollatzResearch.WordTrace]
  refine ⟨7753611934848326472591209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5169074623232217648394139 7753611934848326472591209)
  ·
    refine ⟨5815208951136244854443407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7753611934848326472591209 5815208951136244854443407)
    ·
      refine ⟨8722813426704367281665111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5815208951136244854443407 8722813426704367281665111)
      ·
        refine ⟨13084220140056550922497667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8722813426704367281665111 13084220140056550922497667)
        ·
          refine ⟨19626330210084826383746501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13084220140056550922497667 19626330210084826383746501)
          ·
            refine ⟨3679936914390904946952469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19626330210084826383746501 3679936914390904946952469)
            ·
              refine ⟨172497042862073669388397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3679936914390904946952469 172497042862073669388397)
              ·
                refine ⟨64686391073277626020649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172497042862073669388397 64686391073277626020649)
                ·
                  rfl

theorem cell19_212585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 3].length) (baseStart_212585 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212585 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212585 prefixEnd_212585 := by exact prefixLift 212585
  have htrace : WordTrace (prefixWord ++ tailWord_212585) baseStart_212585 baseEnd_212585 := by
    simpa [prefixWord, tailWord_212585, baseEnd_212585] using wordTrace_append hprefix tailTrace_212585
  have hstable : (prefixWord ++ tailWord_212585).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212585).length < 2 ^ (prefixWord ++ tailWord_212585).sum := by decide
  have hdescent : baseEnd_212585 < baseStart_212585 := by decide
  rcases family_descends (prefixWord ++ tailWord_212585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212661 : List Nat := [1, 3, 3, 3, 2, 7]
def baseStart_212661 : Nat := 118140960795 + 212661 * 2 ^ 59
def prefixEnd_212661 : Nat := 4983230072969 + 3 ^ 40 * 212661 * 2
def baseEnd_212661 : Nat := 7189946302281329814617

theorem tailTrace_212661 : CollatzResearch.WordTrace tailWord_212661 prefixEnd_212661 7189946302281329814617 := by
  unfold tailWord_212661
  simp only [CollatzResearch.WordTrace]
  refine ⟨7756383882572991452357837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5170922588381994301571891 7756383882572991452357837)
  ·
    refine ⟨2908643955964871794634189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7756383882572991452357837 2908643955964871794634189)
    ·
      refine ⟨1090741483486826922987821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2908643955964871794634189 1090741483486826922987821)
      ·
        refine ⟨409028056307560096120433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1090741483486826922987821 409028056307560096120433)
        ·
          refine ⟨306771042230670072090325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 409028056307560096120433 306771042230670072090325)
          ·
            refine ⟨7189946302281329814617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 306771042230670072090325 7189946302281329814617)
            ·
              rfl

theorem cell19_212661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 7].length) (baseStart_212661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212661 prefixEnd_212661 := by exact prefixLift 212661
  have htrace : WordTrace (prefixWord ++ tailWord_212661) baseStart_212661 baseEnd_212661 := by
    simpa [prefixWord, tailWord_212661, baseEnd_212661] using wordTrace_append hprefix tailTrace_212661
  have hstable : (prefixWord ++ tailWord_212661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212661).length < 2 ^ (prefixWord ++ tailWord_212661).sum := by decide
  have hdescent : baseEnd_212661 < baseStart_212661 := by decide
  rcases family_descends (prefixWord ++ tailWord_212661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212663 : List Nat := [1, 1, 3, 1, 5, 8]
def baseStart_212663 : Nat := 118140960795 + 212663 * 2 ^ 59
def prefixEnd_212663 : Nat := 4983230072969 + 3 ^ 40 * 212663 * 2
def baseEnd_212663 : Nat := 7190013921132950698567

theorem tailTrace_212663 : CollatzResearch.WordTrace tailWord_212663 prefixEnd_212663 7190013921132950698567 := by
  unfold tailWord_212663
  simp only [CollatzResearch.WordTrace]
  refine ⟨7756456828565745793930643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5170971219043830529287095 7756456828565745793930643)
  ·
    refine ⟨11634685242848618690895965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7756456828565745793930643 11634685242848618690895965)
    ·
      refine ⟨4363006966068232009085987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11634685242848618690895965 4363006966068232009085987)
      ·
        refine ⟨6544510449102348013628981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4363006966068232009085987 6544510449102348013628981)
        ·
          refine ⟨613547854603345126277717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6544510449102348013628981 613547854603345126277717)
          ·
            refine ⟨7190013921132950698567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 613547854603345126277717 7190013921132950698567)
            ·
              rfl

theorem cell19_212663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 8].length) (baseStart_212663 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212663 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212663 prefixEnd_212663 := by exact prefixLift 212663
  have htrace : WordTrace (prefixWord ++ tailWord_212663) baseStart_212663 baseEnd_212663 := by
    simpa [prefixWord, tailWord_212663, baseEnd_212663] using wordTrace_append hprefix tailTrace_212663
  have hstable : (prefixWord ++ tailWord_212663).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212663).length < 2 ^ (prefixWord ++ tailWord_212663).sum := by decide
  have hdescent : baseEnd_212663 < baseStart_212663 := by decide
  rcases family_descends (prefixWord ++ tailWord_212663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212754 : List Nat := [3, 2, 4, 1, 1, 2, 1, 5]
def baseStart_212754 : Nat := 118140960795 + 212754 * 2 ^ 59
def prefixEnd_212754 : Nat := 4983230072969 + 3 ^ 40 * 212754 * 2
def baseEnd_212754 : Nat := 64737815209935308264633

theorem tailTrace_212754 : CollatzResearch.WordTrace tailWord_212754 prefixEnd_212754 64737815209935308264633 := by
  unfold tailWord_212754
  simp only [CollatzResearch.WordTrace]
  refine ⟨1939943967809017083873329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5173183914157378890328877 1939943967809017083873329)
  ·
    refine ⟨1454957975856762812904997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1939943967809017083873329 1454957975856762812904997)
    ·
      refine ⟨272804620473143027419687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1454957975856762812904997 272804620473143027419687)
      ·
        refine ⟨409206930709714541129531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 272804620473143027419687 409206930709714541129531)
        ·
          refine ⟨613810396064571811694297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 409206930709714541129531 613810396064571811694297)
          ·
            refine ⟨460357797048428858770723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613810396064571811694297 460357797048428858770723)
            ·
              refine ⟨690536695572643288156085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 460357797048428858770723 690536695572643288156085)
              ·
                refine ⟨64737815209935308264633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 690536695572643288156085 64737815209935308264633)
                ·
                  rfl

theorem cell19_212754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_212754 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212754 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212754 prefixEnd_212754 := by exact prefixLift 212754
  have htrace : WordTrace (prefixWord ++ tailWord_212754) baseStart_212754 baseEnd_212754 := by
    simpa [prefixWord, tailWord_212754, baseEnd_212754] using wordTrace_append hprefix tailTrace_212754
  have hstable : (prefixWord ++ tailWord_212754).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212754).length < 2 ^ (prefixWord ++ tailWord_212754).sum := by decide
  have hdescent : baseEnd_212754 < baseStart_212754 := by decide
  rcases family_descends (prefixWord ++ tailWord_212754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212794 : List Nat := [3, 1, 1, 1, 5, 2, 2, 4]
def baseStart_212794 : Nat := 118140960795 + 212794 * 2 ^ 59
def prefixEnd_212794 : Nat := 4983230072969 + 3 ^ 40 * 212794 * 2
def baseEnd_212794 : Nat := 64749986603227067375635

theorem tailTrace_212794 : CollatzResearch.WordTrace tailWord_212794 prefixEnd_212794 64749986603227067375635 := by
  unfold tailWord_212794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1940308697772788791737359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5174156527394103444632957 1940308697772788791737359)
  ·
    refine ⟨2910463046659183187606039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1940308697772788791737359 2910463046659183187606039)
    ·
      refine ⟨4365694569988774781409059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2910463046659183187606039 4365694569988774781409059)
      ·
        refine ⟨6548541854983162172113589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4365694569988774781409059 6548541854983162172113589)
        ·
          refine ⟨613925798904671453635649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6548541854983162172113589 613925798904671453635649)
          ·
            refine ⟨460444349178503590226737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 613925798904671453635649 460444349178503590226737)
            ·
              refine ⟨345333261883877692670053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 460444349178503590226737 345333261883877692670053)
              ·
                refine ⟨64749986603227067375635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 345333261883877692670053 64749986603227067375635)
                ·
                  rfl

theorem cell19_212794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 2, 4].length) (baseStart_212794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212794 prefixEnd_212794 := by exact prefixLift 212794
  have htrace : WordTrace (prefixWord ++ tailWord_212794) baseStart_212794 baseEnd_212794 := by
    simpa [prefixWord, tailWord_212794, baseEnd_212794] using wordTrace_append hprefix tailTrace_212794
  have hstable : (prefixWord ++ tailWord_212794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212794).length < 2 ^ (prefixWord ++ tailWord_212794).sum := by decide
  have hdescent : baseEnd_212794 < baseStart_212794 := by decide
  rcases family_descends (prefixWord ++ tailWord_212794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212796 : List Nat := [2, 2, 2, 2, 1, 1, 3, 6]
def baseStart_212796 : Nat := 118140960795 + 212796 * 2 ^ 59
def prefixEnd_212796 : Nat := 4983230072969 + 3 ^ 40 * 212796 * 2
def baseEnd_212796 : Nat := 64750595172891655331185

theorem tailTrace_212796 : CollatzResearch.WordTrace tailWord_212796 prefixEnd_212796 64750595172891655331185 := by
  unfold tailWord_212796
  simp only [CollatzResearch.WordTrace]
  refine ⟨3880653868541954754261121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5174205158055939672348161 3880653868541954754261121)
  ·
    refine ⟨2910490401406466065695841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3880653868541954754261121 2910490401406466065695841)
    ·
      refine ⟨2182867801054849549271881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2910490401406466065695841 2182867801054849549271881)
      ·
        refine ⟨1637150850791137161953911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2182867801054849549271881 1637150850791137161953911)
        ·
          refine ⟨2455726276186705742930867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1637150850791137161953911 2455726276186705742930867)
          ·
            refine ⟨3683589414280058614396301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2455726276186705742930867 3683589414280058614396301)
            ·
              refine ⟨1381346030355021980398613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3683589414280058614396301 1381346030355021980398613)
              ·
                refine ⟨64750595172891655331185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1381346030355021980398613 64750595172891655331185)
                ·
                  rfl

theorem cell19_212796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_212796 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212796 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212796 prefixEnd_212796 := by exact prefixLift 212796
  have htrace : WordTrace (prefixWord ++ tailWord_212796) baseStart_212796 baseEnd_212796 := by
    simpa [prefixWord, tailWord_212796, baseEnd_212796] using wordTrace_append hprefix tailTrace_212796
  have hstable : (prefixWord ++ tailWord_212796).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212796).length < 2 ^ (prefixWord ++ tailWord_212796).sum := by decide
  have hdescent : baseEnd_212796 < baseStart_212796 := by decide
  rcases family_descends (prefixWord ++ tailWord_212796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_212925 : List Nat := [1, 4, 1, 2, 3, 3, 2, 3]
def baseStart_212925 : Nat := 118140960795 + 212925 * 2 ^ 59
def prefixEnd_212925 : Nat := 4983230072969 + 3 ^ 40 * 212925 * 2
def baseEnd_212925 : Nat := 64789847916257578464167

theorem tailTrace_212925 : CollatzResearch.WordTrace tailWord_212925 prefixEnd_212925 64789847916257578464167 := by
  unfold tailWord_212925
  simp only [CollatzResearch.WordTrace]
  refine ⟨7766012753616564539968229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5177341835744376359978819 7766012753616564539968229)
  ·
    refine ⟨1456127391303105851244043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7766012753616564539968229 1456127391303105851244043)
    ·
      refine ⟨2184191086954658776866065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1456127391303105851244043 2184191086954658776866065)
      ·
        refine ⟨1638143315215994082649549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2184191086954658776866065 1638143315215994082649549)
        ·
          refine ⟨614303743205997780993581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1638143315215994082649549 614303743205997780993581)
          ·
            refine ⟨230363903702249167872593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 614303743205997780993581 230363903702249167872593)
            ·
              refine ⟨172772927776686875904445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 230363903702249167872593 172772927776686875904445)
              ·
                refine ⟨64789847916257578464167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172772927776686875904445 64789847916257578464167)
                ·
                  rfl

theorem cell19_212925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 2, 3].length) (baseStart_212925 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_212925 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_212925 prefixEnd_212925 := by exact prefixLift 212925
  have htrace : WordTrace (prefixWord ++ tailWord_212925) baseStart_212925 baseEnd_212925 := by
    simpa [prefixWord, tailWord_212925, baseEnd_212925] using wordTrace_append hprefix tailTrace_212925
  have hstable : (prefixWord ++ tailWord_212925).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_212925).length < 2 ^ (prefixWord ++ tailWord_212925).sum := by decide
  have hdescent : baseEnd_212925 < baseStart_212925 := by decide
  rcases family_descends (prefixWord ++ tailWord_212925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213041 : List Nat := [1, 2, 2, 3, 1, 4, 3, 3]
def baseStart_213041 : Nat := 118140960795 + 213041 * 2 ^ 59
def prefixEnd_213041 : Nat := 4983230072969 + 3 ^ 40 * 213041 * 2
def baseEnd_213041 : Nat := 64825144956803679886073

theorem tailTrace_213041 : CollatzResearch.WordTrace tailWord_213041 prefixEnd_213041 64825144956803679886073 := by
  unfold tailWord_213041
  simp only [CollatzResearch.WordTrace]
  refine ⟨7770243621196316351190977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5180162414130877567460651 7770243621196316351190977)
  ·
    refine ⟨5827682715897237263393233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7770243621196316351190977 5827682715897237263393233)
    ·
      refine ⟨4370762036922927947544925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5827682715897237263393233 4370762036922927947544925)
      ·
        refine ⟨1639035763846097980329347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4370762036922927947544925 1639035763846097980329347)
        ·
          refine ⟨2458553645769146970494021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1639035763846097980329347 2458553645769146970494021)
          ·
            refine ⟨460978808581715056967629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2458553645769146970494021 460978808581715056967629)
            ·
              refine ⟨172867053218143146362861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 460978808581715056967629 172867053218143146362861)
              ·
                refine ⟨64825144956803679886073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 172867053218143146362861 64825144956803679886073)
                ·
                  rfl

theorem cell19_213041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 3].length) (baseStart_213041 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213041 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213041 prefixEnd_213041 := by exact prefixLift 213041
  have htrace : WordTrace (prefixWord ++ tailWord_213041) baseStart_213041 baseEnd_213041 := by
    simpa [prefixWord, tailWord_213041, baseEnd_213041] using wordTrace_append hprefix tailTrace_213041
  have hstable : (prefixWord ++ tailWord_213041).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213041).length < 2 ^ (prefixWord ++ tailWord_213041).sum := by decide
  have hdescent : baseEnd_213041 < baseStart_213041 := by decide
  rcases family_descends (prefixWord ++ tailWord_213041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213098 : List Nat := [3, 1, 3, 2, 3, 1, 1, 5]
def baseStart_213098 : Nat := 118140960795 + 213098 * 2 ^ 59
def prefixEnd_213098 : Nat := 4983230072969 + 3 ^ 40 * 213098 * 2
def baseEnd_213098 : Nat := 64842489192244436619251

theorem tailTrace_213098 : CollatzResearch.WordTrace tailWord_213098 prefixEnd_213098 64842489192244436619251 := by
  unfold tailWord_213098
  simp only [CollatzResearch.WordTrace]
  refine ⟨1943080645497453771503987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5181548387993210057343965 1943080645497453771503987)
  ·
    refine ⟨2914620968246180657255981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1943080645497453771503987 2914620968246180657255981)
    ·
      refine ⟨1092982863092317746470993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2914620968246180657255981 1092982863092317746470993)
      ·
        refine ⟨819737147319238309853245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1092982863092317746470993 819737147319238309853245)
        ·
          refine ⟨307401430244714366194967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 819737147319238309853245 307401430244714366194967)
          ·
            refine ⟨461102145367071549292451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307401430244714366194967 461102145367071549292451)
            ·
              refine ⟨691653218050607323938677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461102145367071549292451 691653218050607323938677)
              ·
                refine ⟨64842489192244436619251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 691653218050607323938677 64842489192244436619251)
                ·
                  rfl

theorem cell19_213098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_213098 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213098 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213098 prefixEnd_213098 := by exact prefixLift 213098
  have htrace : WordTrace (prefixWord ++ tailWord_213098) baseStart_213098 baseEnd_213098 := by
    simpa [prefixWord, tailWord_213098, baseEnd_213098] using wordTrace_append hprefix tailTrace_213098
  have hstable : (prefixWord ++ tailWord_213098).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213098).length < 2 ^ (prefixWord ++ tailWord_213098).sum := by decide
  have hdescent : baseEnd_213098 < baseStart_213098 := by decide
  rcases family_descends (prefixWord ++ tailWord_213098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213100 : List Nat := [2, 2, 1, 1, 3, 4, 1, 5]
def baseStart_213100 : Nat := 118140960795 + 213100 * 2 ^ 59
def prefixEnd_213100 : Nat := 4983230072969 + 3 ^ 40 * 213100 * 2
def baseEnd_213100 : Nat := 64843097761909024574801

theorem tailTrace_213100 : CollatzResearch.WordTrace tailWord_213100 prefixEnd_213100 64843097761909024574801 := by
  unfold tailWord_213100
  simp only [CollatzResearch.WordTrace]
  refine ⟨3886197763991284713794377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5181597018655046285059169 3886197763991284713794377)
  ·
    refine ⟨2914648322993463535345783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3886197763991284713794377 2914648322993463535345783)
    ·
      refine ⟨4371972484490195303018675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2914648322993463535345783 4371972484490195303018675)
      ·
        refine ⟨6557958726735292954528013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4371972484490195303018675 6557958726735292954528013)
        ·
          refine ⟨2459234522525734857948005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6557958726735292954528013 2459234522525734857948005)
          ·
            refine ⟨461106472973575285865251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2459234522525734857948005 461106472973575285865251)
            ·
              refine ⟨691659709460362928797877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461106472973575285865251 691659709460362928797877)
              ·
                refine ⟨64843097761909024574801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 691659709460362928797877 64843097761909024574801)
                ·
                  rfl

theorem cell19_213100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 5].length) (baseStart_213100 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213100 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213100 prefixEnd_213100 := by exact prefixLift 213100
  have htrace : WordTrace (prefixWord ++ tailWord_213100) baseStart_213100 baseEnd_213100 := by
    simpa [prefixWord, tailWord_213100, baseEnd_213100] using wordTrace_append hprefix tailTrace_213100
  have hstable : (prefixWord ++ tailWord_213100).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213100).length < 2 ^ (prefixWord ++ tailWord_213100).sum := by decide
  have hdescent : baseEnd_213100 < baseStart_213100 := by decide
  rcases family_descends (prefixWord ++ tailWord_213100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213172 : List Nat := [2, 5, 3, 1, 8]
def baseStart_213172 : Nat := 118140960795 + 213172 * 2 ^ 59
def prefixEnd_213172 : Nat := 4983230072969 + 3 ^ 40 * 213172 * 2
def baseEnd_213172 : Nat := 2402407639623488554615

theorem tailTrace_213172 : CollatzResearch.WordTrace tailWord_213172 prefixEnd_213172 2402407639623488554615 := by
  unfold tailWord_213172
  simp only [CollatzResearch.WordTrace]
  refine ⟨3887510791860862862104885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5183347722481150482806513 3887510791860862862104885)
  ·
    refine ⟨364454136736955893322333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3887510791860862862104885 364454136736955893322333)
    ·
      refine ⟨136670301276358459995875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 364454136736955893322333 136670301276358459995875)
      ·
        refine ⟨205005451914537689993813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 136670301276358459995875 205005451914537689993813)
        ·
          refine ⟨2402407639623488554615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 205005451914537689993813 2402407639623488554615)
          ·
            rfl

theorem cell19_213172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 8].length) (baseStart_213172 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213172 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213172 prefixEnd_213172 := by exact prefixLift 213172
  have htrace : WordTrace (prefixWord ++ tailWord_213172) baseStart_213172 baseEnd_213172 := by
    simpa [prefixWord, tailWord_213172, baseEnd_213172] using wordTrace_append hprefix tailTrace_213172
  have hstable : (prefixWord ++ tailWord_213172).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213172).length < 2 ^ (prefixWord ++ tailWord_213172).sum := by decide
  have hdescent : baseEnd_213172 < baseStart_213172 := by decide
  rcases family_descends (prefixWord ++ tailWord_213172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213235 : List Nat := [1, 1, 1, 2, 2, 4, 8]
def baseStart_213235 : Nat := 118140960795 + 213235 * 2 ^ 59
def prefixEnd_213235 : Nat := 4983230072969 + 3 ^ 40 * 213235 * 2
def baseEnd_213235 : Nat := 21628058738089570524811

theorem tailTrace_213235 : CollatzResearch.WordTrace tailWord_213235 prefixEnd_213235 21628058738089570524811 := by
  unfold tailWord_213235
  simp only [CollatzResearch.WordTrace]
  refine ⟨7777319382493487483753159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5184879588328991655835439 7777319382493487483753159)
  ·
    refine ⟨11665979073740231225629739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7777319382493487483753159 11665979073740231225629739)
    ·
      refine ⟨17498968610610346838444609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11665979073740231225629739 17498968610610346838444609)
      ·
        refine ⟨13124226457957760128833457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17498968610610346838444609 13124226457957760128833457)
        ·
          refine ⟨9843169843468320096625093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13124226457957760128833457 9843169843468320096625093)
          ·
            refine ⟨1845594345650310018117205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9843169843468320096625093 1845594345650310018117205)
            ·
              refine ⟨21628058738089570524811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1845594345650310018117205 21628058738089570524811)
              ·
                rfl

theorem cell19_213235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 8].length) (baseStart_213235 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213235 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213235 prefixEnd_213235 := by exact prefixLift 213235
  have htrace : WordTrace (prefixWord ++ tailWord_213235) baseStart_213235 baseEnd_213235 := by
    simpa [prefixWord, tailWord_213235, baseEnd_213235] using wordTrace_append hprefix tailTrace_213235
  have hstable : (prefixWord ++ tailWord_213235).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213235).length < 2 ^ (prefixWord ++ tailWord_213235).sum := by decide
  have hdescent : baseEnd_213235 < baseStart_213235 := by decide
  rcases family_descends (prefixWord ++ tailWord_213235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213271 : List Nat := [1, 1, 3, 4, 1, 3, 1, 5]
def baseStart_213271 : Nat := 118140960795 + 213271 * 2 ^ 59
def prefixEnd_213271 : Nat := 4983230072969 + 3 ^ 40 * 213271 * 2
def baseEnd_213271 : Nat := 64895130468231294774335

theorem tailTrace_213271 : CollatzResearch.WordTrace tailWord_213271 prefixEnd_213271 64895130468231294774335 := by
  unfold tailWord_213271
  simp only [CollatzResearch.WordTrace]
  refine ⟨7778632410363065632063667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5185754940242043754709111 7778632410363065632063667)
  ·
    refine ⟨11667948615544598448095501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7778632410363065632063667 11667948615544598448095501)
    ·
      refine ⟨4375480730829224418035813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11667948615544598448095501 4375480730829224418035813)
      ·
        refine ⟨820402637030479578381715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4375480730829224418035813 820402637030479578381715)
        ·
          refine ⟨1230603955545719367572573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 820402637030479578381715 1230603955545719367572573)
          ·
            refine ⟨461476483329644762839715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1230603955545719367572573 461476483329644762839715)
            ·
              refine ⟨692214724994467144259573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 461476483329644762839715 692214724994467144259573)
              ·
                refine ⟨64895130468231294774335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 692214724994467144259573 64895130468231294774335)
                ·
                  rfl

theorem cell19_213271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 5].length) (baseStart_213271 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213271 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213271 prefixEnd_213271 := by exact prefixLift 213271
  have htrace : WordTrace (prefixWord ++ tailWord_213271) baseStart_213271 baseEnd_213271 := by
    simpa [prefixWord, tailWord_213271, baseEnd_213271] using wordTrace_append hprefix tailTrace_213271
  have hstable : (prefixWord ++ tailWord_213271).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213271).length < 2 ^ (prefixWord ++ tailWord_213271).sum := by decide
  have hdescent : baseEnd_213271 < baseStart_213271 := by decide
  rcases family_descends (prefixWord ++ tailWord_213271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213288 : List Nat := [2, 1, 5, 1, 3, 2, 5]
def baseStart_213288 : Nat := 118140960795 + 213288 * 2 ^ 59
def prefixEnd_213288 : Nat := 4983230072969 + 3 ^ 40 * 213288 * 2
def baseEnd_213288 : Nat := 21633434436793430798837

theorem tailTrace_213288 : CollatzResearch.WordTrace tailWord_213288 prefixEnd_213288 21633434436793430798837 := by
  unfold tailWord_213288
  simp only [CollatzResearch.WordTrace]
  refine ⟨3889626225650738767716259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5186168300867651690288345 3889626225650738767716259)
  ·
    refine ⟨5834439338476108151574389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3889626225650738767716259 5834439338476108151574389)
    ·
      refine ⟨546978687982135139210099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5834439338476108151574389 546978687982135139210099)
      ·
        refine ⟨820468031973202708815149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 546978687982135139210099 820468031973202708815149)
        ·
          refine ⟨307675511989951015805681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 820468031973202708815149 307675511989951015805681)
          ·
            refine ⟨230756633992463261854261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 307675511989951015805681 230756633992463261854261)
            ·
              refine ⟨21633434436793430798837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 230756633992463261854261 21633434436793430798837)
              ·
                rfl

theorem cell19_213288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_213288 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213288 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213288 prefixEnd_213288 := by exact prefixLift 213288
  have htrace : WordTrace (prefixWord ++ tailWord_213288) baseStart_213288 baseEnd_213288 := by
    simpa [prefixWord, tailWord_213288, baseEnd_213288] using wordTrace_append hprefix tailTrace_213288
  have hstable : (prefixWord ++ tailWord_213288).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213288).length < 2 ^ (prefixWord ++ tailWord_213288).sum := by decide
  have hdescent : baseEnd_213288 < baseStart_213288 := by decide
  rcases family_descends (prefixWord ++ tailWord_213288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213292 : List Nat := [2, 2, 1, 1, 1, 3, 9]
def baseStart_213292 : Nat := 118140960795 + 213292 * 2 ^ 59
def prefixEnd_213292 : Nat := 4983230072969 + 3 ^ 40 * 213292 * 2
def baseEnd_213292 : Nat := 21633840149903156102537

theorem tailTrace_213292 : CollatzResearch.WordTrace tailWord_213292 prefixEnd_213292 21633840149903156102537 := by
  unfold tailWord_213292
  simp only [CollatzResearch.WordTrace]
  refine ⟨3889699171643493109289065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5186265562191324145718753 3889699171643493109289065)
  ·
    refine ⟨2917274378732619831966799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3889699171643493109289065 2917274378732619831966799)
    ·
      refine ⟨4375911568098929747950199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2917274378732619831966799 4375911568098929747950199)
      ·
        refine ⟨6563867352148394621925299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4375911568098929747950199 6563867352148394621925299)
        ·
          refine ⟨9845801028222591932887949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6563867352148394621925299 9845801028222591932887949)
          ·
            refine ⟨3692175385583471974832981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9845801028222591932887949 3692175385583471974832981)
            ·
              refine ⟨21633840149903156102537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3692175385583471974832981 21633840149903156102537)
              ·
                rfl

theorem cell19_213292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 9].length) (baseStart_213292 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213292 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213292 prefixEnd_213292 := by exact prefixLift 213292
  have htrace : WordTrace (prefixWord ++ tailWord_213292) baseStart_213292 baseEnd_213292 := by
    simpa [prefixWord, tailWord_213292, baseEnd_213292] using wordTrace_append hprefix tailTrace_213292
  have hstable : (prefixWord ++ tailWord_213292).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213292).length < 2 ^ (prefixWord ++ tailWord_213292).sum := by decide
  have hdescent : baseEnd_213292 < baseStart_213292 := by decide
  rcases family_descends (prefixWord ++ tailWord_213292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213349 : List Nat := [1, 3, 1, 3, 1, 10]
def baseStart_213349 : Nat := 118140960795 + 213349 * 2 ^ 59
def prefixEnd_213349 : Nat := 4983230072969 + 3 ^ 40 * 213349 * 2
def baseEnd_213349 : Nat := 7213207187238913893421

theorem tailTrace_213349 : CollatzResearch.WordTrace tailWord_213349 prefixEnd_213349 7213207187238913893421 := by
  unfold tailWord_213349
  simp only [CollatzResearch.WordTrace]
  refine ⟨7781477304080484953403101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5187651536053656635602067 7781477304080484953403101)
  ·
    refine ⟨2918053989030181857526163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7781477304080484953403101 2918053989030181857526163)
    ·
      refine ⟨4377080983545272786289245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2918053989030181857526163 4377080983545272786289245)
      ·
        refine ⟨1641405368829477294858467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4377080983545272786289245 1641405368829477294858467)
        ·
          refine ⟨2462108053244215942287701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1641405368829477294858467 2462108053244215942287701)
          ·
            refine ⟨7213207187238913893421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2462108053244215942287701 7213207187238913893421)
            ·
              rfl

theorem cell19_213349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 10].length) (baseStart_213349 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213349 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213349 prefixEnd_213349 := by exact prefixLift 213349
  have htrace : WordTrace (prefixWord ++ tailWord_213349) baseStart_213349 baseEnd_213349 := by
    simpa [prefixWord, tailWord_213349, baseEnd_213349] using wordTrace_append hprefix tailTrace_213349
  have hstable : (prefixWord ++ tailWord_213349).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213349).length < 2 ^ (prefixWord ++ tailWord_213349).sum := by decide
  have hdescent : baseEnd_213349 < baseStart_213349 := by decide
  rcases family_descends (prefixWord ++ tailWord_213349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213398 : List Nat := [5, 3, 1, 2, 1, 1, 6]
def baseStart_213398 : Nat := 118140960795 + 213398 * 2 ^ 59
def prefixEnd_213398 : Nat := 4983230072969 + 3 ^ 40 * 213398 * 2
def baseEnd_213398 : Nat := 21644591547310876650589

theorem tailTrace_213398 : CollatzResearch.WordTrace tailWord_213398 prefixEnd_213398 21644591547310876650589 := by
  unfold tailWord_213398
  simp only [CollatzResearch.WordTrace]
  refine ⟨486454030056435395121053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5188842987268644214624565 486454030056435395121053)
  ·
    refine ⟨182420261271163273170395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 486454030056435395121053 182420261271163273170395)
    ·
      refine ⟨273630391906744909755593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 182420261271163273170395 273630391906744909755593)
      ·
        refine ⟨205222793930058682316695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 273630391906744909755593 205222793930058682316695)
        ·
          refine ⟨307834190895088023475043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205222793930058682316695 307834190895088023475043)
          ·
            refine ⟨461751286342632035212565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 307834190895088023475043 461751286342632035212565)
            ·
              refine ⟨21644591547310876650589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 461751286342632035212565 21644591547310876650589)
              ·
                rfl

theorem cell19_213398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 6].length) (baseStart_213398 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213398 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213398 prefixEnd_213398 := by exact prefixLift 213398
  have htrace : WordTrace (prefixWord ++ tailWord_213398) baseStart_213398 baseEnd_213398 := by
    simpa [prefixWord, tailWord_213398, baseEnd_213398] using wordTrace_append hprefix tailTrace_213398
  have hstable : (prefixWord ++ tailWord_213398).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213398).length < 2 ^ (prefixWord ++ tailWord_213398).sum := by decide
  have hdescent : baseEnd_213398 < baseStart_213398 := by decide
  rcases family_descends (prefixWord ++ tailWord_213398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213461 : List Nat := [1, 3, 2, 3, 1, 4, 5]
def baseStart_213461 : Nat := 118140960795 + 213461 * 2 ^ 59
def prefixEnd_213461 : Nat := 4983230072969 + 3 ^ 40 * 213461 * 2
def baseEnd_213461 : Nat := 21650981528789050183865

theorem tailTrace_213461 : CollatzResearch.WordTrace tailWord_213461 prefixEnd_213461 21650981528789050183865 := by
  unfold tailWord_213461
  simp only [CollatzResearch.WordTrace]
  refine ⟨7785562279674728081480237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5190374853116485387653491 7785562279674728081480237)
  ·
    refine ⟨2919585854878023030555089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7785562279674728081480237 2919585854878023030555089)
    ·
      refine ⟨2189689391158517272916317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2919585854878023030555089 2189689391158517272916317)
      ·
        refine ⟨821133521684443977343619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2189689391158517272916317 821133521684443977343619)
        ·
          refine ⟨1231700282526665966015429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 821133521684443977343619 1231700282526665966015429)
          ·
            refine ⟨230943802973749868627893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1231700282526665966015429 230943802973749868627893)
            ·
              refine ⟨21650981528789050183865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 230943802973749868627893 21650981528789050183865)
              ·
                rfl

theorem cell19_213461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 5].length) (baseStart_213461 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213461 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213461 prefixEnd_213461 := by exact prefixLift 213461
  have htrace : WordTrace (prefixWord ++ tailWord_213461) baseStart_213461 baseEnd_213461 := by
    simpa [prefixWord, tailWord_213461, baseEnd_213461] using wordTrace_append hprefix tailTrace_213461
  have hstable : (prefixWord ++ tailWord_213461).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213461).length < 2 ^ (prefixWord ++ tailWord_213461).sum := by decide
  have hdescent : baseEnd_213461 < baseStart_213461 := by decide
  rcases family_descends (prefixWord ++ tailWord_213461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213480 : List Nat := [2, 1, 4, 1, 1, 4, 2, 4]
def baseStart_213480 : Nat := 118140960795 + 213480 * 2 ^ 59
def prefixEnd_213480 : Nat := 4983230072969 + 3 ^ 40 * 213480 * 2
def baseEnd_213480 : Nat := 64958725998180736129321

theorem tailTrace_213480 : CollatzResearch.WordTrace tailWord_213480 prefixEnd_213480 64958725998180736129321 := by
  unfold tailWord_213480
  simp only [CollatzResearch.WordTrace]
  refine ⟨3893127633302947163210947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5190836844403929550947929 3893127633302947163210947)
  ·
    refine ⟨5839691449954420744816421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3893127633302947163210947 5839691449954420744816421)
    ·
      refine ⟨1094942146866453889653079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5839691449954420744816421 1094942146866453889653079)
      ·
        refine ⟨1642413220299680834479619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1094942146866453889653079 1642413220299680834479619)
        ·
          refine ⟨2463619830449521251719429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1642413220299680834479619 2463619830449521251719429)
          ·
            refine ⟨461928718209285234697393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2463619830449521251719429 461928718209285234697393)
            ·
              refine ⟨346446538656963926023045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 461928718209285234697393 346446538656963926023045)
              ·
                refine ⟨64958725998180736129321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 346446538656963926023045 64958725998180736129321)
                ·
                  rfl

theorem cell19_213480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_213480 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213480 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213480 prefixEnd_213480 := by exact prefixLift 213480
  have htrace : WordTrace (prefixWord ++ tailWord_213480) baseStart_213480 baseEnd_213480 := by
    simpa [prefixWord, tailWord_213480, baseEnd_213480] using wordTrace_append hprefix tailTrace_213480
  have hstable : (prefixWord ++ tailWord_213480).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213480).length < 2 ^ (prefixWord ++ tailWord_213480).sum := by decide
  have hdescent : baseEnd_213480 < baseStart_213480 := by decide
  rcases family_descends (prefixWord ++ tailWord_213480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213501 : List Nat := [1, 4, 1, 1, 1, 3, 1, 7]
def baseStart_213501 : Nat := 118140960795 + 213501 * 2 ^ 59
def prefixEnd_213501 : Nat := 4983230072969 + 3 ^ 40 * 213501 * 2
def baseEnd_213501 : Nat := 64965115979658909662597

theorem tailTrace_213501 : CollatzResearch.WordTrace tailWord_213501 prefixEnd_213501 64965115979658909662597 := by
  unfold tailWord_213501
  simp only [CollatzResearch.WordTrace]
  refine ⟨7787021199529814912936357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5191347466353209941957571 7787021199529814912936357)
  ·
    refine ⟨1460066474911840296175567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7787021199529814912936357 1460066474911840296175567)
    ·
      refine ⟨2190099712367760444263351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1460066474911840296175567 2190099712367760444263351)
      ·
        refine ⟨3285149568551640666395027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2190099712367760444263351 3285149568551640666395027)
        ·
          refine ⟨4927724352827460999592541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3285149568551640666395027 4927724352827460999592541)
          ·
            refine ⟨1847896632310297874847203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4927724352827460999592541 1847896632310297874847203)
            ·
              refine ⟨2771844948465446812270805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1847896632310297874847203 2771844948465446812270805)
              ·
                refine ⟨64965115979658909662597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2771844948465446812270805 64965115979658909662597)
                ·
                  rfl

theorem cell19_213501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_213501 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213501 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213501 prefixEnd_213501 := by exact prefixLift 213501
  have htrace : WordTrace (prefixWord ++ tailWord_213501) baseStart_213501 baseEnd_213501 := by
    simpa [prefixWord, tailWord_213501, baseEnd_213501] using wordTrace_append hprefix tailTrace_213501
  have hstable : (prefixWord ++ tailWord_213501).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213501).length < 2 ^ (prefixWord ++ tailWord_213501).sum := by decide
  have hdescent : baseEnd_213501 < baseStart_213501 := by decide
  rcases family_descends (prefixWord ++ tailWord_213501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213613 : List Nat := [1, 5, 1, 1, 3, 2, 1, 5]
def baseStart_213613 : Nat := 118140960795 + 213613 * 2 ^ 59
def prefixEnd_213613 : Nat := 4983230072969 + 3 ^ 40 * 213613 * 2
def baseEnd_213613 : Nat := 64999195880875835173403

theorem tailTrace_213613 : CollatzResearch.WordTrace tailWord_213613 prefixEnd_213613 64999195880875835173403 := by
  unfold tailWord_213613
  simp only [CollatzResearch.WordTrace]
  refine ⟨7791106175124058041013493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5194070783416038694008995 7791106175124058041013493)
  ·
    refine ⟨730416203917880441345015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7791106175124058041013493 730416203917880441345015)
    ·
      refine ⟨1095624305876820662017523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 730416203917880441345015 1095624305876820662017523)
      ·
        refine ⟨1643436458815230993026285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1095624305876820662017523 1643436458815230993026285)
        ·
          refine ⟨616288672055711622384857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1643436458815230993026285 616288672055711622384857)
          ·
            refine ⟨462216504041783716788643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 616288672055711622384857 462216504041783716788643)
            ·
              refine ⟨693324756062675575182965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 462216504041783716788643 693324756062675575182965)
              ·
                refine ⟨64999195880875835173403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 693324756062675575182965 64999195880875835173403)
                ·
                  rfl

theorem cell19_213613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 5].length) (baseStart_213613 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213613 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213613 prefixEnd_213613 := by exact prefixLift 213613
  have htrace : WordTrace (prefixWord ++ tailWord_213613) baseStart_213613 baseEnd_213613 := by
    simpa [prefixWord, tailWord_213613, baseEnd_213613] using wordTrace_append hprefix tailTrace_213613
  have hstable : (prefixWord ++ tailWord_213613).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213613).length < 2 ^ (prefixWord ++ tailWord_213613).sum := by decide
  have hdescent : baseEnd_213613 < baseStart_213613 := by decide
  rcases family_descends (prefixWord ++ tailWord_213613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213702 : List Nat := [6, 1, 2, 1, 2, 2, 1, 4]
def baseStart_213702 : Nat := 118140960795 + 213702 * 2 ^ 59
def prefixEnd_213702 : Nat := 4983230072969 + 3 ^ 40 * 213702 * 2
def baseEnd_213702 : Nat := 65026277230949999195383

theorem tailTrace_213702 : CollatzResearch.WordTrace tailWord_213702 prefixEnd_213702 65026277230949999195383 := by
  unfold tailWord_213702
  simp only [CollatzResearch.WordTrace]
  refine ⟨243573508493800820031355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5196234847867750827335573 243573508493800820031355)
  ·
    refine ⟨365360262740701230047033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 243573508493800820031355 365360262740701230047033)
    ·
      refine ⟨274020197055525922535275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 365360262740701230047033 274020197055525922535275)
      ·
        refine ⟨411030295583288883802913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274020197055525922535275 411030295583288883802913)
        ·
          refine ⟨308272721687466662852185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 411030295583288883802913 308272721687466662852185)
          ·
            refine ⟨231204541265599997139139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308272721687466662852185 231204541265599997139139)
            ·
              refine ⟨346806811898399995708709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231204541265599997139139 346806811898399995708709)
              ·
                refine ⟨65026277230949999195383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 346806811898399995708709 65026277230949999195383)
                ·
                  rfl

theorem cell19_213702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_213702 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213702 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213702 prefixEnd_213702 := by exact prefixLift 213702
  have htrace : WordTrace (prefixWord ++ tailWord_213702) baseStart_213702 baseEnd_213702 := by
    simpa [prefixWord, tailWord_213702, baseEnd_213702] using wordTrace_append hprefix tailTrace_213702
  have hstable : (prefixWord ++ tailWord_213702).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213702).length < 2 ^ (prefixWord ++ tailWord_213702).sum := by decide
  have hdescent : baseEnd_213702 < baseStart_213702 := by decide
  rcases family_descends (prefixWord ++ tailWord_213702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213708 : List Nat := [2, 2, 1, 5, 1, 1, 3, 4]
def baseStart_213708 : Nat := 118140960795 + 213708 * 2 ^ 59
def prefixEnd_213708 : Nat := 4983230072969 + 3 ^ 40 * 213708 * 2
def baseEnd_213708 : Nat := 65028102939943763062033

theorem tailTrace_213708 : CollatzResearch.WordTrace tailWord_213708 prefixEnd_213708 65028102939943763062033 := by
  unfold tailWord_213708
  simp only [CollatzResearch.WordTrace]
  refine ⟨3897285554889944632860889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5196380739853259510481185 3897285554889944632860889)
  ·
    refine ⟨2922964166167458474645667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3897285554889944632860889 2922964166167458474645667)
    ·
      refine ⟨4384446249251187711968501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2922964166167458474645667 4384446249251187711968501)
      ·
        refine ⟨411041835867298847997047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4384446249251187711968501 411041835867298847997047)
        ·
          refine ⟨616562753800948271995571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 411041835867298847997047 616562753800948271995571)
          ·
            refine ⟨924844130701422407993357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 616562753800948271995571 924844130701422407993357)
            ·
              refine ⟨346816549013033402997509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 924844130701422407993357 346816549013033402997509)
              ·
                refine ⟨65028102939943763062033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 346816549013033402997509 65028102939943763062033)
                ·
                  rfl

theorem cell19_213708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_213708 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213708 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213708 prefixEnd_213708 := by exact prefixLift 213708
  have htrace : WordTrace (prefixWord ++ tailWord_213708) baseStart_213708 baseEnd_213708 := by
    simpa [prefixWord, tailWord_213708, baseEnd_213708] using wordTrace_append hprefix tailTrace_213708
  have hstable : (prefixWord ++ tailWord_213708).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213708).length < 2 ^ (prefixWord ++ tailWord_213708).sum := by decide
  have hdescent : baseEnd_213708 < baseStart_213708 := by decide
  rcases family_descends (prefixWord ++ tailWord_213708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213727 : List Nat := [1, 1, 2, 3, 2, 4, 3, 3]
def baseStart_213727 : Nat := 118140960795 + 213727 * 2 ^ 59
def prefixEnd_213727 : Nat := 4983230072969 + 3 ^ 40 * 213727 * 2
def baseEnd_213727 : Nat := 65033884351757348639759

theorem tailTrace_213727 : CollatzResearch.WordTrace tailWord_213727 prefixEnd_213727 65033884351757348639759 := by
  unfold tailWord_213727
  simp only [CollatzResearch.WordTrace]
  refine ⟨7795264096711055510663435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5196842731140703673775623 7795264096711055510663435)
  ·
    refine ⟨11692896145066583265995153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7795264096711055510663435 11692896145066583265995153)
    ·
      refine ⟨8769672108799937449496365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11692896145066583265995153 8769672108799937449496365)
      ·
        refine ⟨3288627040799976543561137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8769672108799937449496365 3288627040799976543561137)
        ·
          refine ⟨2466470280599982407670853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3288627040799976543561137 2466470280599982407670853)
          ·
            refine ⟨462463177612496701438285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2466470280599982407670853 462463177612496701438285)
            ·
              refine ⟨173423691604686263039357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 462463177612496701438285 173423691604686263039357)
              ·
                refine ⟨65033884351757348639759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173423691604686263039357 65033884351757348639759)
                ·
                  rfl

theorem cell19_213727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 3, 3].length) (baseStart_213727 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213727 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213727 prefixEnd_213727 := by exact prefixLift 213727
  have htrace : WordTrace (prefixWord ++ tailWord_213727) baseStart_213727 baseEnd_213727 := by
    simpa [prefixWord, tailWord_213727, baseEnd_213727] using wordTrace_append hprefix tailTrace_213727
  have hstable : (prefixWord ++ tailWord_213727).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213727).length < 2 ^ (prefixWord ++ tailWord_213727).sum := by decide
  have hdescent : baseEnd_213727 < baseStart_213727 := by decide
  rcases family_descends (prefixWord ++ tailWord_213727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213778 : List Nat := [3, 2, 4, 1, 3, 1, 2, 3]
def baseStart_213778 : Nat := 118140960795 + 213778 * 2 ^ 59
def prefixEnd_213778 : Nat := 4983230072969 + 3 ^ 40 * 213778 * 2
def baseEnd_213778 : Nat := 65049402878204341506287

theorem tailTrace_213778 : CollatzResearch.WordTrace tailWord_213778 prefixEnd_213778 65049402878204341506287 := by
  unfold tailWord_213778
  simp only [CollatzResearch.WordTrace]
  refine ⟨1949281054881572805192497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5198082813017527480513325 1949281054881572805192497)
  ·
    refine ⟨1461960791161179603894373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1949281054881572805192497 1461960791161179603894373)
    ·
      refine ⟨274117648342721175730195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1461960791161179603894373 274117648342721175730195)
      ·
        refine ⟨411176472514081763595293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274117648342721175730195 411176472514081763595293)
        ·
          refine ⟨154191177192780661348235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 411176472514081763595293 154191177192780661348235)
          ·
            refine ⟨231286765789170992022353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154191177192780661348235 231286765789170992022353)
            ·
              refine ⟨173465074341878244016765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231286765789170992022353 173465074341878244016765)
              ·
                refine ⟨65049402878204341506287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173465074341878244016765 65049402878204341506287)
                ·
                  rfl

theorem cell19_213778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 2, 3].length) (baseStart_213778 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213778 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213778 prefixEnd_213778 := by exact prefixLift 213778
  have htrace : WordTrace (prefixWord ++ tailWord_213778) baseStart_213778 baseEnd_213778 := by
    simpa [prefixWord, tailWord_213778, baseEnd_213778] using wordTrace_append hprefix tailTrace_213778
  have hstable : (prefixWord ++ tailWord_213778).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213778).length < 2 ^ (prefixWord ++ tailWord_213778).sum := by decide
  have hdescent : baseEnd_213778 < baseStart_213778 := by decide
  rcases family_descends (prefixWord ++ tailWord_213778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213786 : List Nat := [3, 1, 1, 3, 2, 1, 3, 5]
def baseStart_213786 : Nat := 118140960795 + 213786 * 2 ^ 59
def prefixEnd_213786 : Nat := 4983230072969 + 3 ^ 40 * 213786 * 2
def baseEnd_213786 : Nat := 65051837156862693328487

theorem tailTrace_213786 : CollatzResearch.WordTrace tailWord_213786 prefixEnd_213786 65051837156862693328487 := by
  unfold tailWord_213786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1949354000874327146765303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5198277335664872391374141 1949354000874327146765303)
  ·
    refine ⟨2924031001311490720147955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1949354000874327146765303 2924031001311490720147955)
    ·
      refine ⟨4386046501967236080221933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2924031001311490720147955 4386046501967236080221933)
      ·
        refine ⟨1644767438237713530083225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4386046501967236080221933 1644767438237713530083225)
        ·
          refine ⟨1233575578678285147562419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1644767438237713530083225 1233575578678285147562419)
          ·
            refine ⟨1850363368017427721343629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1233575578678285147562419 1850363368017427721343629)
            ·
              refine ⟨693886263006535395503861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1850363368017427721343629 693886263006535395503861)
              ·
                refine ⟨65051837156862693328487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 693886263006535395503861 65051837156862693328487)
                ·
                  rfl

theorem cell19_213786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_213786 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213786 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213786 prefixEnd_213786 := by exact prefixLift 213786
  have htrace : WordTrace (prefixWord ++ tailWord_213786) baseStart_213786 baseEnd_213786 := by
    simpa [prefixWord, tailWord_213786, baseEnd_213786] using wordTrace_append hprefix tailTrace_213786
  have hstable : (prefixWord ++ tailWord_213786).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213786).length < 2 ^ (prefixWord ++ tailWord_213786).sum := by decide
  have hdescent : baseEnd_213786 < baseStart_213786 := by decide
  rcases family_descends (prefixWord ++ tailWord_213786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213881 : List Nat := [1, 2, 1, 3, 2, 3, 3, 4]
def baseStart_213881 : Nat := 118140960795 + 213881 * 2 ^ 59
def prefixEnd_213881 : Nat := 4983230072969 + 3 ^ 40 * 213881 * 2
def baseEnd_213881 : Nat := 65080744215930621217117

theorem tailTrace_213881 : CollatzResearch.WordTrace tailWord_213881 prefixEnd_213881 65080744215930621217117 := by
  unfold tailWord_213881
  simp only [CollatzResearch.WordTrace]
  refine ⟨7800880938153139811769497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5200587292102093207846331 7800880938153139811769497)
  ·
    refine ⟨5850660703614854858827123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7800880938153139811769497 5850660703614854858827123)
    ·
      refine ⟨8775991055422282288240685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5850660703614854858827123 8775991055422282288240685)
      ·
        refine ⟨3290996645783355858090257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8775991055422282288240685 3290996645783355858090257)
        ·
          refine ⟨2468247484337516893567693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3290996645783355858090257 2468247484337516893567693)
          ·
            refine ⟨925592806626568835087885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2468247484337516893567693 925592806626568835087885)
            ·
              refine ⟨347097302484963313157957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 925592806626568835087885 347097302484963313157957)
              ·
                refine ⟨65080744215930621217117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347097302484963313157957 65080744215930621217117)
                ·
                  rfl

theorem cell19_213881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 4].length) (baseStart_213881 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213881 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213881 prefixEnd_213881 := by exact prefixLift 213881
  have htrace : WordTrace (prefixWord ++ tailWord_213881) baseStart_213881 baseEnd_213881 := by
    simpa [prefixWord, tailWord_213881, baseEnd_213881] using wordTrace_append hprefix tailTrace_213881
  have hstable : (prefixWord ++ tailWord_213881).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213881).length < 2 ^ (prefixWord ++ tailWord_213881).sum := by decide
  have hdescent : baseEnd_213881 < baseStart_213881 := by decide
  rcases family_descends (prefixWord ++ tailWord_213881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213919 : List Nat := [1, 1, 2, 5, 2, 2, 6]
def baseStart_213919 : Nat := 118140960795 + 213919 * 2 ^ 59
def prefixEnd_213919 : Nat := 4983230072969 + 3 ^ 40 * 213919 * 2
def baseEnd_213919 : Nat := 21697435679852597457523

theorem tailTrace_213919 : CollatzResearch.WordTrace tailWord_213919 prefixEnd_213919 21697435679852597457523 := by
  unfold tailWord_213919
  simp only [CollatzResearch.WordTrace]
  refine ⟨7802266912015472301652811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5201511274676981534435207 7802266912015472301652811)
  ·
    refine ⟨11703400368023208452479217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7802266912015472301652811 11703400368023208452479217)
    ·
      refine ⟨8777550276017406339359413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11703400368023208452479217 8777550276017406339359413)
      ·
        refine ⟨822895338376631844314945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8777550276017406339359413 822895338376631844314945)
        ·
          refine ⟨617171503782473883236209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 822895338376631844314945 617171503782473883236209)
          ·
            refine ⟨462878627836855412427157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 617171503782473883236209 462878627836855412427157)
            ·
              refine ⟨21697435679852597457523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 462878627836855412427157 21697435679852597457523)
              ·
                rfl

theorem cell19_213919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 6].length) (baseStart_213919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213919 prefixEnd_213919 := by exact prefixLift 213919
  have htrace : WordTrace (prefixWord ++ tailWord_213919) baseStart_213919 baseEnd_213919 := by
    simpa [prefixWord, tailWord_213919, baseEnd_213919] using wordTrace_append hprefix tailTrace_213919
  have hstable : (prefixWord ++ tailWord_213919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213919).length < 2 ^ (prefixWord ++ tailWord_213919).sum := by decide
  have hdescent : baseEnd_213919 < baseStart_213919 := by decide
  rcases family_descends (prefixWord ++ tailWord_213919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213974 : List Nat := [5, 2, 1, 1, 2, 1, 7]
def baseStart_213974 : Nat := 118140960795 + 213974 * 2 ^ 59
def prefixEnd_213974 : Nat := 4983230072969 + 3 ^ 40 * 213974 * 2
def baseEnd_213974 : Nat := 21703014235111320383399

theorem tailTrace_213974 : CollatzResearch.WordTrace tailWord_213974 prefixEnd_213974 21703014235111320383399 := by
  unfold tailWord_213974
  simp only [CollatzResearch.WordTrace]
  refine ⟨487767057926013543431561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5202848617877477796603317 487767057926013543431561)
  ·
    refine ⟨365825293444510157573671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 487767057926013543431561 365825293444510157573671)
    ·
      refine ⟨548737940166765236360507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 365825293444510157573671 548737940166765236360507)
      ·
        refine ⟨823106910250147854540761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 548737940166765236360507 823106910250147854540761)
        ·
          refine ⟨617330182687610890905571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 823106910250147854540761 617330182687610890905571)
          ·
            refine ⟨925995274031416336358357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 617330182687610890905571 925995274031416336358357)
            ·
              refine ⟨21703014235111320383399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 925995274031416336358357 21703014235111320383399)
              ·
                rfl

theorem cell19_213974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 7].length) (baseStart_213974 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213974 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213974 prefixEnd_213974 := by exact prefixLift 213974
  have htrace : WordTrace (prefixWord ++ tailWord_213974) baseStart_213974 baseEnd_213974 := by
    simpa [prefixWord, tailWord_213974, baseEnd_213974] using wordTrace_append hprefix tailTrace_213974
  have hstable : (prefixWord ++ tailWord_213974).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213974).length < 2 ^ (prefixWord ++ tailWord_213974).sum := by decide
  have hdescent : baseEnd_213974 < baseStart_213974 := by decide
  rcases family_descends (prefixWord ++ tailWord_213974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_213976 : List Nat := [2, 1, 2, 2, 2, 5, 5]
def baseStart_213976 : Nat := 118140960795 + 213976 * 2 ^ 59
def prefixEnd_213976 : Nat := 4983230072969 + 3 ^ 40 * 213976 * 2
def baseEnd_213976 : Nat := 21703217091666183035249

theorem tailTrace_213976 : CollatzResearch.WordTrace tailWord_213976 prefixEnd_213976 21703217091666183035249 := by
  unfold tailWord_213976
  simp only [CollatzResearch.WordTrace]
  refine ⟨3902172936404485518238891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5202897248539314024318521 3902172936404485518238891)
  ·
    refine ⟨5853259404606728277358337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3902172936404485518238891 5853259404606728277358337)
    ·
      refine ⟨4389944553455046208018753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5853259404606728277358337 4389944553455046208018753)
      ·
        refine ⟨3292458415091284656014065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4389944553455046208018753 3292458415091284656014065)
        ·
          refine ⟨2469343811318463492010549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3292458415091284656014065 2469343811318463492010549)
          ·
            refine ⟨231500982311105952375989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2469343811318463492010549 231500982311105952375989)
            ·
              refine ⟨21703217091666183035249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231500982311105952375989 21703217091666183035249)
              ·
                rfl

theorem cell19_213976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 5, 5].length) (baseStart_213976 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_213976 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_213976 prefixEnd_213976 := by exact prefixLift 213976
  have htrace : WordTrace (prefixWord ++ tailWord_213976) baseStart_213976 baseEnd_213976 := by
    simpa [prefixWord, tailWord_213976, baseEnd_213976] using wordTrace_append hprefix tailTrace_213976
  have hstable : (prefixWord ++ tailWord_213976).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_213976).length < 2 ^ (prefixWord ++ tailWord_213976).sum := by decide
  have hdescent : baseEnd_213976 < baseStart_213976 := by decide
  rcases family_descends (prefixWord ++ tailWord_213976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214048 : List Nat := [2, 1, 1, 7, 1, 2, 1, 4]
def baseStart_214048 : Nat := 118140960795 + 214048 * 2 ^ 59
def prefixEnd_214048 : Nat := 4983230072969 + 3 ^ 40 * 214048 * 2
def baseEnd_214048 : Nat := 65131559782923715505551

theorem tailTrace_214048 : CollatzResearch.WordTrace tailWord_214048 prefixEnd_214048 65131559782923715505551 := by
  unfold tailWord_214048
  simp only [CollatzResearch.WordTrace]
  refine ⟨3903485964274063666549399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5204647952365418222065865 3903485964274063666549399)
  ·
    refine ⟨5855228946411095499824099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3903485964274063666549399 5855228946411095499824099)
    ·
      refine ⟨8782843419616643249736149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5855228946411095499824099 8782843419616643249736149)
      ·
        refine ⟨205847892647265076165691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8782843419616643249736149 205847892647265076165691)
        ·
          refine ⟨308771838970897614248537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205847892647265076165691 308771838970897614248537)
          ·
            refine ⟨231578879228173210686403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308771838970897614248537 231578879228173210686403)
            ·
              refine ⟨347368318842259816029605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231578879228173210686403 347368318842259816029605)
              ·
                refine ⟨65131559782923715505551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347368318842259816029605 65131559782923715505551)
                ·
                  rfl

theorem cell19_214048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 1, 4].length) (baseStart_214048 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214048 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214048 prefixEnd_214048 := by exact prefixLift 214048
  have htrace : WordTrace (prefixWord ++ tailWord_214048) baseStart_214048 baseEnd_214048 := by
    simpa [prefixWord, tailWord_214048, baseEnd_214048] using wordTrace_append hprefix tailTrace_214048
  have hstable : (prefixWord ++ tailWord_214048).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214048).length < 2 ^ (prefixWord ++ tailWord_214048).sum := by decide
  have hdescent : baseEnd_214048 < baseStart_214048 := by decide
  rcases family_descends (prefixWord ++ tailWord_214048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214050 : List Nat := [3, 3, 1, 1, 1, 5, 1, 4]
def baseStart_214050 : Nat := 118140960795 + 214050 * 2 ^ 59
def prefixEnd_214050 : Nat := 4983230072969 + 3 ^ 40 * 214050 * 2
def baseEnd_214050 : Nat := 65132168352588303461101

theorem tailTrace_214050 : CollatzResearch.WordTrace tailWord_214050 prefixEnd_214050 65132168352588303461101 := by
  unfold tailWord_214050
  simp only [CollatzResearch.WordTrace]
  refine ⟨1951761218635220418667901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5204696583027254449781069 1951761218635220418667901)
  ·
    refine ⟨731910456988207657000463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1951761218635220418667901 731910456988207657000463)
    ·
      refine ⟨1097865685482311485500695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 731910456988207657000463 1097865685482311485500695)
      ·
        refine ⟨1646798528223467228251043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1097865685482311485500695 1646798528223467228251043)
        ·
          refine ⟨2470197792335200842376565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1646798528223467228251043 2470197792335200842376565)
          ·
            refine ⟨231581043031425078972803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2470197792335200842376565 231581043031425078972803)
            ·
              refine ⟨347371564547137618459205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231581043031425078972803 347371564547137618459205)
              ·
                refine ⟨65132168352588303461101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 347371564547137618459205 65132168352588303461101)
                ·
                  rfl

theorem cell19_214050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_214050 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214050 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214050 prefixEnd_214050 := by exact prefixLift 214050
  have htrace : WordTrace (prefixWord ++ tailWord_214050) baseStart_214050 baseEnd_214050 := by
    simpa [prefixWord, tailWord_214050, baseEnd_214050] using wordTrace_append hprefix tailTrace_214050
  have hstable : (prefixWord ++ tailWord_214050).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214050).length < 2 ^ (prefixWord ++ tailWord_214050).sum := by decide
  have hdescent : baseEnd_214050 < baseStart_214050 := by decide
  rcases family_descends (prefixWord ++ tailWord_214050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214111 : List Nat := [1, 1, 2, 3, 1, 1, 4, 6]
def baseStart_214111 : Nat := 118140960795 + 214111 * 2 ^ 59
def prefixEnd_214111 : Nat := 4983230072969 + 3 ^ 40 * 214111 * 2
def baseEnd_214111 : Nat := 65150729727358236105379

theorem tailTrace_214111 : CollatzResearch.WordTrace tailWord_214111 prefixEnd_214111 65150729727358236105379 := by
  unfold tailWord_214111
  simp only [CollatzResearch.WordTrace]
  refine ⟨7809269727319889092642187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5206179818213259395094791 7809269727319889092642187)
  ·
    refine ⟨11713904590979833638963281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7809269727319889092642187 11713904590979833638963281)
    ·
      refine ⟨8785428443234875229222461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11713904590979833638963281 8785428443234875229222461)
      ·
        refine ⟨3294535666213078210958423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8785428443234875229222461 3294535666213078210958423)
        ·
          refine ⟨4941803499319617316437635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3294535666213078210958423 4941803499319617316437635)
          ·
            refine ⟨7412705248979425974656453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4941803499319617316437635 7412705248979425974656453)
            ·
              refine ⟨1389882234183642370248085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7412705248979425974656453 1389882234183642370248085)
              ·
                refine ⟨65150729727358236105379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1389882234183642370248085 65150729727358236105379)
                ·
                  rfl

theorem cell19_214111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_214111 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214111 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214111 prefixEnd_214111 := by exact prefixLift 214111
  have htrace : WordTrace (prefixWord ++ tailWord_214111) baseStart_214111 baseEnd_214111 := by
    simpa [prefixWord, tailWord_214111, baseEnd_214111] using wordTrace_append hprefix tailTrace_214111
  have hstable : (prefixWord ++ tailWord_214111).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214111).length < 2 ^ (prefixWord ++ tailWord_214111).sum := by decide
  have hdescent : baseEnd_214111 < baseStart_214111 := by decide
  rcases family_descends (prefixWord ++ tailWord_214111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214126 : List Nat := [4, 1, 2, 2, 1, 2, 4, 3]
def baseStart_214126 : Nat := 118140960795 + 214126 * 2 ^ 59
def prefixEnd_214126 : Nat := 4983230072969 + 3 ^ 40 * 214126 * 2
def baseEnd_214126 : Nat := 65155293999842645772005

theorem tailTrace_214126 : CollatzResearch.WordTrace tailWord_214126 prefixEnd_214126 65155293999842645772005 := by
  unfold tailWord_214126
  simp only [CollatzResearch.WordTrace]
  refine ⟨976227102783193331804779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5206544548177031102958821 976227102783193331804779)
  ·
    refine ⟨1464340654174789997707169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 976227102783193331804779 1464340654174789997707169)
    ·
      refine ⟨1098255490631092498280377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1464340654174789997707169 1098255490631092498280377)
      ·
        refine ⟨823691617973319373710283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1098255490631092498280377 823691617973319373710283)
        ·
          refine ⟨1235537426959979060565425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 823691617973319373710283 1235537426959979060565425)
          ·
            refine ⟨926653070219984295424069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1235537426959979060565425 926653070219984295424069)
            ·
              refine ⟨173747450666247055392013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 926653070219984295424069 173747450666247055392013)
              ·
                refine ⟨65155293999842645772005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173747450666247055392013 65155293999842645772005)
                ·
                  rfl

theorem cell19_214126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_214126 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214126 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214126 prefixEnd_214126 := by exact prefixLift 214126
  have htrace : WordTrace (prefixWord ++ tailWord_214126) baseStart_214126 baseEnd_214126 := by
    simpa [prefixWord, tailWord_214126, baseEnd_214126] using wordTrace_append hprefix tailTrace_214126
  have hstable : (prefixWord ++ tailWord_214126).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214126).length < 2 ^ (prefixWord ++ tailWord_214126).sum := by decide
  have hdescent : baseEnd_214126 < baseStart_214126 := by decide
  rcases family_descends (prefixWord ++ tailWord_214126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214244 : List Nat := [2, 3, 1, 1, 1, 2, 2, 7]
def baseStart_214244 : Nat := 118140960795 + 214244 * 2 ^ 59
def prefixEnd_214244 : Nat := 4983230072969 + 3 ^ 40 * 214244 * 2
def baseEnd_214244 : Nat := 65191199610053335149461

theorem tailTrace_214244 : CollatzResearch.WordTrace tailWord_214244 prefixEnd_214244 65191199610053335149461 := by
  unfold tailWord_214244
  simp only [CollatzResearch.WordTrace]
  refine ⟨3907060317919026403616893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5209413757225368538155857 3907060317919026403616893)
  ·
    refine ⟨1465147619219634901356335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3907060317919026403616893 1465147619219634901356335)
    ·
      refine ⟨2197721428829452352034503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1465147619219634901356335 2197721428829452352034503)
      ·
        refine ⟨3296582143244178528051755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2197721428829452352034503 3296582143244178528051755)
        ·
          refine ⟨4944873214866267792077633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3296582143244178528051755 4944873214866267792077633)
          ·
            refine ⟨3708654911149700844058225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4944873214866267792077633 3708654911149700844058225)
            ·
              refine ⟨2781491183362275633043669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3708654911149700844058225 2781491183362275633043669)
              ·
                refine ⟨65191199610053335149461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2781491183362275633043669 65191199610053335149461)
                ·
                  rfl

theorem cell19_214244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_214244 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214244 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214244 prefixEnd_214244 := by exact prefixLift 214244
  have htrace : WordTrace (prefixWord ++ tailWord_214244) baseStart_214244 baseEnd_214244 := by
    simpa [prefixWord, tailWord_214244, baseEnd_214244] using wordTrace_append hprefix tailTrace_214244
  have hstable : (prefixWord ++ tailWord_214244).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214244).length < 2 ^ (prefixWord ++ tailWord_214244).sum := by decide
  have hdescent : baseEnd_214244 < baseStart_214244 := by decide
  rcases family_descends (prefixWord ++ tailWord_214244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214282 : List Nat := [3, 1, 2, 2, 1, 1, 1, 8]
def baseStart_214282 : Nat := 118140960795 + 214282 * 2 ^ 59
def prefixEnd_214282 : Nat := 4983230072969 + 3 ^ 40 * 214282 * 2
def baseEnd_214282 : Nat := 65202762433680506304913

theorem tailTrace_214282 : CollatzResearch.WordTrace tailWord_214282 prefixEnd_214282 65202762433680506304913 := by
  unfold tailWord_214282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1953876652425096324279275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5210337739800256864744733 1953876652425096324279275)
  ·
    refine ⟨2930814978637644486418913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1953876652425096324279275 2930814978637644486418913)
    ·
      refine ⟨2198111233978233364814185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2930814978637644486418913 2198111233978233364814185)
      ·
        refine ⟨1648583425483675023610639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2198111233978233364814185 1648583425483675023610639)
        ·
          refine ⟨2472875138225512535415959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648583425483675023610639 2472875138225512535415959)
          ·
            refine ⟨3709312707338268803123939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472875138225512535415959 3709312707338268803123939)
            ·
              refine ⟨5563969061007403204685909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3709312707338268803123939 5563969061007403204685909)
              ·
                refine ⟨65202762433680506304913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5563969061007403204685909 65202762433680506304913)
                ·
                  rfl

theorem cell19_214282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_214282 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214282 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214282 prefixEnd_214282 := by exact prefixLift 214282
  have htrace : WordTrace (prefixWord ++ tailWord_214282) baseStart_214282 baseEnd_214282 := by
    simpa [prefixWord, tailWord_214282, baseEnd_214282] using wordTrace_append hprefix tailTrace_214282
  have hstable : (prefixWord ++ tailWord_214282).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214282).length < 2 ^ (prefixWord ++ tailWord_214282).sum := by decide
  have hdescent : baseEnd_214282 < baseStart_214282 := by decide
  rcases family_descends (prefixWord ++ tailWord_214282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214337 : List Nat := [1, 2, 5, 2, 1, 1, 1, 6]
def baseStart_214337 : Nat := 118140960795 + 214337 * 2 ^ 59
def prefixEnd_214337 : Nat := 4983230072969 + 3 ^ 40 * 214337 * 2
def baseEnd_214337 : Nat := 65219498099456675082541

theorem tailTrace_214337 : CollatzResearch.WordTrace tailWord_214337 prefixEnd_214337 65219498099456675082541 := by
  unfold tailWord_214337
  simp only [CollatzResearch.WordTrace]
  refine ⟨7817512624501129690369265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5211675083000753126912843 7817512624501129690369265)
  ·
    refine ⟨5863134468375847267776949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7817512624501129690369265 5863134468375847267776949)
    ·
      refine ⟨549668856410235681354089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5863134468375847267776949 549668856410235681354089)
      ·
        refine ⟨412251642307676761015567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549668856410235681354089 412251642307676761015567)
        ·
          refine ⟨618377463461515141523351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412251642307676761015567 618377463461515141523351)
          ·
            refine ⟨927566195192272712285027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618377463461515141523351 927566195192272712285027)
            ·
              refine ⟨1391349292788409068427541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 927566195192272712285027 1391349292788409068427541)
              ·
                refine ⟨65219498099456675082541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1391349292788409068427541 65219498099456675082541)
                ·
                  rfl

theorem cell19_214337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 6].length) (baseStart_214337 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214337 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214337 prefixEnd_214337 := by exact prefixLift 214337
  have htrace : WordTrace (prefixWord ++ tailWord_214337) baseStart_214337 baseEnd_214337 := by
    simpa [prefixWord, tailWord_214337, baseEnd_214337] using wordTrace_append hprefix tailTrace_214337
  have hstable : (prefixWord ++ tailWord_214337).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214337).length < 2 ^ (prefixWord ++ tailWord_214337).sum := by decide
  have hdescent : baseEnd_214337 < baseStart_214337 := by decide
  rcases family_descends (prefixWord ++ tailWord_214337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214375 : List Nat := [1, 1, 5, 1, 5, 6]
def baseStart_214375 : Nat := 118140960795 + 214375 * 2 ^ 59
def prefixEnd_214375 : Nat := 4983230072969 + 3 ^ 40 * 214375 * 2
def baseEnd_214375 : Nat := 7247895658120427359777

theorem tailTrace_214375 : CollatzResearch.WordTrace tailWord_214375 prefixEnd_214375 7247895658120427359777 := by
  unfold tailWord_214375
  simp only [CollatzResearch.WordTrace]
  refine ⟨7818898598363462180252579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5212599065575641453501719 7818898598363462180252579)
  ·
    refine ⟨11728347897545193270378869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7818898598363462180252579 11728347897545193270378869)
    ·
      refine ⟨1099532615394861869098019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11728347897545193270378869 1099532615394861869098019)
      ·
        refine ⟨1649298923092292803647029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1099532615394861869098019 1649298923092292803647029)
        ·
          refine ⟨154621774039902450341909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1649298923092292803647029 154621774039902450341909)
          ·
            refine ⟨7247895658120427359777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154621774039902450341909 7247895658120427359777)
            ·
              rfl

theorem cell19_214375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 6].length) (baseStart_214375 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214375 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214375 prefixEnd_214375 := by exact prefixLift 214375
  have htrace : WordTrace (prefixWord ++ tailWord_214375) baseStart_214375 baseEnd_214375 := by
    simpa [prefixWord, tailWord_214375, baseEnd_214375] using wordTrace_append hprefix tailTrace_214375
  have hstable : (prefixWord ++ tailWord_214375).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214375).length < 2 ^ (prefixWord ++ tailWord_214375).sum := by decide
  have hdescent : baseEnd_214375 < baseStart_214375 := by decide
  rcases family_descends (prefixWord ++ tailWord_214375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214430 : List Nat := [4, 3, 1, 2, 2, 1, 6]
def baseStart_214430 : Nat := 118140960795 + 214430 * 2 ^ 59
def prefixEnd_214430 : Nat := 4983230072969 + 3 ^ 40 * 214430 * 2
def baseEnd_214430 : Nat := 21749265529620005005207

theorem tailTrace_214430 : CollatzResearch.WordTrace tailWord_214430 prefixEnd_214430 21749265529620005005207 := by
  unfold tailWord_214430
  simp only [CollatzResearch.WordTrace]
  refine ⟨977613076645525821688093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5213936408776137715669829 977613076645525821688093)
  ·
    refine ⟨366604903742072183133035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 977613076645525821688093 366604903742072183133035)
    ·
      refine ⟨549907355613108274699553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 366604903742072183133035 549907355613108274699553)
      ·
        refine ⟨412430516709831206024665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 549907355613108274699553 412430516709831206024665)
        ·
          refine ⟨309322887532373404518499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412430516709831206024665 309322887532373404518499)
          ·
            refine ⟨463984331298560106777749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309322887532373404518499 463984331298560106777749)
            ·
              refine ⟨21749265529620005005207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 463984331298560106777749 21749265529620005005207)
              ·
                rfl

theorem cell19_214430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 6].length) (baseStart_214430 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214430 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214430 prefixEnd_214430 := by exact prefixLift 214430
  have htrace : WordTrace (prefixWord ++ tailWord_214430) baseStart_214430 baseEnd_214430 := by
    simpa [prefixWord, tailWord_214430, baseEnd_214430] using wordTrace_append hprefix tailTrace_214430
  have hstable : (prefixWord ++ tailWord_214430).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214430).length < 2 ^ (prefixWord ++ tailWord_214430).sum := by decide
  have hdescent : baseEnd_214430 < baseStart_214430 := by decide
  rcases family_descends (prefixWord ++ tailWord_214430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214468 : List Nat := [2, 3, 3, 2, 1, 1, 4, 3]
def baseStart_214468 : Nat := 118140960795 + 214468 * 2 ^ 59
def prefixEnd_214468 : Nat := 4983230072969 + 3 ^ 40 * 214468 * 2
def baseEnd_214468 : Nat := 65259359412487186171073

theorem tailTrace_214468 : CollatzResearch.WordTrace tailWord_214468 prefixEnd_214468 65259359412487186171073 := by
  unfold tailWord_214468
  simp only [CollatzResearch.WordTrace]
  refine ⟨3911145293513269531694029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5214860391351026042258705 3911145293513269531694029)
  ·
    refine ⟨1466679485067476074385261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3911145293513269531694029 1466679485067476074385261)
    ·
      refine ⟨550004806900303527894473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1466679485067476074385261 550004806900303527894473)
      ·
        refine ⟨412503605175227645920855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 550004806900303527894473 412503605175227645920855)
        ·
          refine ⟨618755407762841468881283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412503605175227645920855 618755407762841468881283)
          ·
            refine ⟨928133111644262203321925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618755407762841468881283 928133111644262203321925)
            ·
              refine ⟨174024958433299163122861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 928133111644262203321925 174024958433299163122861)
              ·
                refine ⟨65259359412487186171073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174024958433299163122861 65259359412487186171073)
                ·
                  rfl

theorem cell19_214468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 3].length) (baseStart_214468 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214468 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214468 prefixEnd_214468 := by exact prefixLift 214468
  have htrace : WordTrace (prefixWord ++ tailWord_214468) baseStart_214468 baseEnd_214468 := by
    simpa [prefixWord, tailWord_214468, baseEnd_214468] using wordTrace_append hprefix tailTrace_214468
  have hstable : (prefixWord ++ tailWord_214468).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214468).length < 2 ^ (prefixWord ++ tailWord_214468).sum := by decide
  have hdescent : baseEnd_214468 < baseStart_214468 := by decide
  rcases family_descends (prefixWord ++ tailWord_214468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214472 : List Nat := [2, 1, 3, 1, 3, 1, 3, 5]
def baseStart_214472 : Nat := 118140960795 + 214472 * 2 ^ 59
def prefixEnd_214472 : Nat := 4983230072969 + 3 ^ 40 * 214472 * 2
def baseEnd_214472 : Nat := 65260576551816362082173

theorem tailTrace_214472 : CollatzResearch.WordTrace tailWord_214472 prefixEnd_214472 65260576551816362082173 := by
  unfold tailWord_214472
  simp only [CollatzResearch.WordTrace]
  refine ⟨3911218239506023873266835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5214957652674698497689113 3911218239506023873266835)
  ·
    refine ⟨5866827359259035809900253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3911218239506023873266835 5866827359259035809900253)
    ·
      refine ⟨2200060259722138428712595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5866827359259035809900253 2200060259722138428712595)
      ·
        refine ⟨3300090389583207643068893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200060259722138428712595 3300090389583207643068893)
        ·
          refine ⟨1237533896093702866150835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3300090389583207643068893 1237533896093702866150835)
          ·
            refine ⟨1856300844140554299226253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237533896093702866150835 1856300844140554299226253)
            ·
              refine ⟨696112816552707862209845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1856300844140554299226253 696112816552707862209845)
              ·
                refine ⟨65260576551816362082173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 696112816552707862209845 65260576551816362082173)
                ·
                  rfl

theorem cell19_214472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 5].length) (baseStart_214472 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214472 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214472 prefixEnd_214472 := by exact prefixLift 214472
  have htrace : WordTrace (prefixWord ++ tailWord_214472) baseStart_214472 baseEnd_214472 := by
    simpa [prefixWord, tailWord_214472, baseEnd_214472] using wordTrace_append hprefix tailTrace_214472
  have hstable : (prefixWord ++ tailWord_214472).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214472).length < 2 ^ (prefixWord ++ tailWord_214472).sum := by decide
  have hdescent : baseEnd_214472 < baseStart_214472 := by decide
  rcases family_descends (prefixWord ++ tailWord_214472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214563 : List Nat := [1, 1, 1, 4, 6, 1, 1, 4]
def baseStart_214563 : Nat := 118140960795 + 214563 * 2 ^ 59
def prefixEnd_214563 : Nat := 4983230072969 + 3 ^ 40 * 214563 * 2
def baseEnd_214563 : Nat := 65288266471555114059703

theorem tailTrace_214563 : CollatzResearch.WordTrace tailWord_214563 prefixEnd_214563 65288266471555114059703 := by
  unfold tailWord_214563
  simp only [CollatzResearch.WordTrace]
  refine ⟨7825755521682370288096343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5217170347788246858730895 7825755521682370288096343)
  ·
    refine ⟨11738633282523555432144515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7825755521682370288096343 11738633282523555432144515)
    ·
      refine ⟨17607949923785333148216773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11738633282523555432144515 17607949923785333148216773)
      ·
        refine ⟨3301490610709749965290645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17607949923785333148216773 3301490610709749965290645)
        ·
          refine ⟨154757372377019529622999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3301490610709749965290645 154757372377019529622999)
          ·
            refine ⟨232136058565529294434499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154757372377019529622999 232136058565529294434499)
            ·
              refine ⟨348204087848293941651749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232136058565529294434499 348204087848293941651749)
              ·
                refine ⟨65288266471555114059703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 348204087848293941651749 65288266471555114059703)
                ·
                  rfl

theorem cell19_214563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 4].length) (baseStart_214563 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214563 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214563 prefixEnd_214563 := by exact prefixLift 214563
  have htrace : WordTrace (prefixWord ++ tailWord_214563) baseStart_214563 baseEnd_214563 := by
    simpa [prefixWord, tailWord_214563, baseEnd_214563] using wordTrace_append hprefix tailTrace_214563
  have hstable : (prefixWord ++ tailWord_214563).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214563).length < 2 ^ (prefixWord ++ tailWord_214563).sum := by decide
  have hdescent : baseEnd_214563 < baseStart_214563 := by decide
  rcases family_descends (prefixWord ++ tailWord_214563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214584 : List Nat := [2, 1, 2, 1, 4, 3, 3, 3]
def baseStart_214584 : Nat := 118140960795 + 214584 * 2 ^ 59
def prefixEnd_214584 : Nat := 4983230072969 + 3 ^ 40 * 214584 * 2
def baseEnd_214584 : Nat := 65294656453033287592979

theorem tailTrace_214584 : CollatzResearch.WordTrace tailWord_214584 prefixEnd_214584 65294656453033287592979 := by
  unfold tailWord_214584
  simp only [CollatzResearch.WordTrace]
  refine ⟨3913260727303145437305403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5217680969737527249740537 3913260727303145437305403)
  ·
    refine ⟨5869891090954718155958105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3913260727303145437305403 5869891090954718155958105)
    ·
      refine ⟨4402418318216038616968579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5869891090954718155958105 4402418318216038616968579)
      ·
        refine ⟨6603627477324057925452869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4402418318216038616968579 6603627477324057925452869)
        ·
          refine ⟨1238180151998260861022413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6603627477324057925452869 1238180151998260861022413)
          ·
            refine ⟨464317556999347822883405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1238180151998260861022413 464317556999347822883405)
            ·
              refine ⟨174119083874755433581277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 464317556999347822883405 174119083874755433581277)
              ·
                refine ⟨65294656453033287592979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174119083874755433581277 65294656453033287592979)
                ·
                  rfl

theorem cell19_214584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_214584 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214584 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214584 prefixEnd_214584 := by exact prefixLift 214584
  have htrace : WordTrace (prefixWord ++ tailWord_214584) baseStart_214584 baseEnd_214584 := by
    simpa [prefixWord, tailWord_214584, baseEnd_214584] using wordTrace_append hprefix tailTrace_214584
  have hstable : (prefixWord ++ tailWord_214584).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214584).length < 2 ^ (prefixWord ++ tailWord_214584).sum := by decide
  have hdescent : baseEnd_214584 < baseStart_214584 := by decide
  rcases family_descends (prefixWord ++ tailWord_214584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214637 : List Nat := [1, 5, 1, 1, 5, 1, 2, 3]
def baseStart_214637 : Nat := 118140960795 + 214637 * 2 ^ 59
def prefixEnd_214637 : Nat := 4983230072969 + 3 ^ 40 * 214637 * 2
def baseEnd_214637 : Nat := 65310783549144868415057

theorem tailTrace_214637 : CollatzResearch.WordTrace tailWord_214637 prefixEnd_214637 65310783549144868415057 := by
  unfold tailWord_214637
  simp only [CollatzResearch.WordTrace]
  refine ⟨7828454523414280926290165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5218969682276187284193443 7828454523414280926290165)
  ·
    refine ⟨733917611570088836839703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7828454523414280926290165 733917611570088836839703)
    ·
      refine ⟨1100876417355133255259555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 733917611570088836839703 1100876417355133255259555)
      ·
        refine ⟨1651314626032699882889333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1100876417355133255259555 1651314626032699882889333)
        ·
          refine ⟨154810746190565614020875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1651314626032699882889333 154810746190565614020875)
          ·
            refine ⟨232216119285848421031313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154810746190565614020875 232216119285848421031313)
            ·
              refine ⟨174162089464386315773485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232216119285848421031313 174162089464386315773485)
              ·
                refine ⟨65310783549144868415057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174162089464386315773485 65310783549144868415057)
                ·
                  rfl

theorem cell19_214637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 3].length) (baseStart_214637 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214637 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214637 prefixEnd_214637 := by exact prefixLift 214637
  have htrace : WordTrace (prefixWord ++ tailWord_214637) baseStart_214637 baseEnd_214637 := by
    simpa [prefixWord, tailWord_214637, baseEnd_214637] using wordTrace_append hprefix tailTrace_214637
  have hstable : (prefixWord ++ tailWord_214637).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214637).length < 2 ^ (prefixWord ++ tailWord_214637).sum := by decide
  have hdescent : baseEnd_214637 < baseStart_214637 := by decide
  rcases family_descends (prefixWord ++ tailWord_214637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214660 : List Nat := [2, 3, 2, 1, 4, 2, 5]
def baseStart_214660 : Nat := 118140960795 + 214660 * 2 ^ 59
def prefixEnd_214660 : Nat := 4983230072969 + 3 ^ 40 * 214660 * 2
def baseEnd_214660 : Nat := 21772594033429209967961

theorem tailTrace_214660 : CollatzResearch.WordTrace tailWord_214660 prefixEnd_214660 21772594033429209967961 := by
  unfold tailWord_214660
  simp only [CollatzResearch.WordTrace]
  refine ⟨3914646701165477927188717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5219528934887303902918289 3914646701165477927188717)
  ·
    refine ⟨1467992512937054222695769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3914646701165477927188717 1467992512937054222695769)
    ·
      refine ⟨1100994384702790667021827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1467992512937054222695769 1100994384702790667021827)
      ·
        refine ⟨1651491577054186000532741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1100994384702790667021827 1651491577054186000532741)
        ·
          refine ⟨309654670697659875099889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1651491577054186000532741 309654670697659875099889)
          ·
            refine ⟨232241003023244906324917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309654670697659875099889 232241003023244906324917)
            ·
              refine ⟨21772594033429209967961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232241003023244906324917 21772594033429209967961)
              ·
                rfl

theorem cell19_214660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_214660 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214660 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214660 prefixEnd_214660 := by exact prefixLift 214660
  have htrace : WordTrace (prefixWord ++ tailWord_214660) baseStart_214660 baseEnd_214660 := by
    simpa [prefixWord, tailWord_214660, baseEnd_214660] using wordTrace_append hprefix tailTrace_214660
  have hstable : (prefixWord ++ tailWord_214660).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214660).length < 2 ^ (prefixWord ++ tailWord_214660).sum := by decide
  have hdescent : baseEnd_214660 < baseStart_214660 := by decide
  rcases family_descends (prefixWord ++ tailWord_214660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214772 : List Nat := [2, 6, 1, 1, 1, 2, 6]
def baseStart_214772 : Nat := 118140960795 + 214772 * 2 ^ 59
def prefixEnd_214772 : Nat := 4983230072969 + 3 ^ 40 * 214772 * 2
def baseEnd_214772 : Nat := 21783954000501518471563

theorem tailTrace_214772 : CollatzResearch.WordTrace tailWord_214772 prefixEnd_214772 21783954000501518471563 := by
  unfold tailWord_214772
  simp only [CollatzResearch.WordTrace]
  refine ⟨3916689188962599491227285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5222252251950132654969713 3916689188962599491227285)
  ·
    refine ⟨183594805732621851151279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 3916689188962599491227285 183594805732621851151279)
    ·
      refine ⟨275392208598932776726919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183594805732621851151279 275392208598932776726919)
      ·
        refine ⟨413088312898399165090379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275392208598932776726919 413088312898399165090379)
        ·
          refine ⟨619632469347598747635569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 413088312898399165090379 619632469347598747635569)
          ·
            refine ⟨464724352010699060726677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 619632469347598747635569 464724352010699060726677)
            ·
              refine ⟨21783954000501518471563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 464724352010699060726677 21783954000501518471563)
              ·
                rfl

theorem cell19_214772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 6].length) (baseStart_214772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214772 prefixEnd_214772 := by exact prefixLift 214772
  have htrace : WordTrace (prefixWord ++ tailWord_214772) baseStart_214772 baseEnd_214772 := by
    simpa [prefixWord, tailWord_214772, baseEnd_214772] using wordTrace_append hprefix tailTrace_214772
  have hstable : (prefixWord ++ tailWord_214772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214772).length < 2 ^ (prefixWord ++ tailWord_214772).sum := by decide
  have hdescent : baseEnd_214772 < baseStart_214772 := by decide
  rcases family_descends (prefixWord ++ tailWord_214772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214804 : List Nat := [2, 4, 4, 1, 2, 1, 2, 3]
def baseStart_214804 : Nat := 118140960795 + 214804 * 2 ^ 59
def prefixEnd_214804 : Nat := 4983230072969 + 3 ^ 40 * 214804 * 2
def baseEnd_214804 : Nat := 65361599116137962703491

theorem tailTrace_214804 : CollatzResearch.WordTrace tailWord_214804 prefixEnd_214804 65361599116137962703491 := by
  unfold tailWord_214804
  simp only [CollatzResearch.WordTrace]
  refine ⟨3917272756904634223809733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5223030342539512298412977 3917272756904634223809733)
  ·
    refine ⟨734488641919618916964325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3917272756904634223809733 734488641919618916964325)
    ·
      refine ⟨137716620359928546930811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 734488641919618916964325 137716620359928546930811)
      ·
        refine ⟨206574930539892820396217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137716620359928546930811 206574930539892820396217)
        ·
          refine ⟨154931197904919615297163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206574930539892820396217 154931197904919615297163)
          ·
            refine ⟨232396796857379422945745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154931197904919615297163 232396796857379422945745)
            ·
              refine ⟨174297597643034567209309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232396796857379422945745 174297597643034567209309)
              ·
                refine ⟨65361599116137962703491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174297597643034567209309 65361599116137962703491)
                ·
                  rfl

theorem cell19_214804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 3].length) (baseStart_214804 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214804 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214804 prefixEnd_214804 := by exact prefixLift 214804
  have htrace : WordTrace (prefixWord ++ tailWord_214804) baseStart_214804 baseEnd_214804 := by
    simpa [prefixWord, tailWord_214804, baseEnd_214804] using wordTrace_append hprefix tailTrace_214804
  have hstable : (prefixWord ++ tailWord_214804).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214804).length < 2 ^ (prefixWord ++ tailWord_214804).sum := by decide
  have hdescent : baseEnd_214804 < baseStart_214804 := by decide
  rcases family_descends (prefixWord ++ tailWord_214804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214833 : List Nat := [1, 2, 2, 3, 2, 4, 5]
def baseStart_214833 : Nat := 118140960795 + 214833 * 2 ^ 59
def prefixEnd_214833 : Nat := 4983230072969 + 3 ^ 40 * 214833 * 2
def baseEnd_214833 : Nat := 21790141125424829352989

theorem tailTrace_214833 : CollatzResearch.WordTrace tailWord_214833 prefixEnd_214833 21790141125424829352989 := by
  unfold tailWord_214833
  simp only [CollatzResearch.WordTrace]
  refine ⟨7835603230704206400425153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5223735487136137600283435 7835603230704206400425153)
  ·
    refine ⟨5876702423028154800318865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7835603230704206400425153 5876702423028154800318865)
    ·
      refine ⟨4407526817271116100239149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5876702423028154800318865 4407526817271116100239149)
      ·
        refine ⟨1652822556476668537589681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4407526817271116100239149 1652822556476668537589681)
        ·
          refine ⟨1239616917357501403192261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1652822556476668537589681 1239616917357501403192261)
          ·
            refine ⟨232428172004531513098549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1239616917357501403192261 232428172004531513098549)
            ·
              refine ⟨21790141125424829352989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232428172004531513098549 21790141125424829352989)
              ·
                rfl

theorem cell19_214833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_214833 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214833 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214833 prefixEnd_214833 := by exact prefixLift 214833
  have htrace : WordTrace (prefixWord ++ tailWord_214833) baseStart_214833 baseEnd_214833 := by
    simpa [prefixWord, tailWord_214833, baseEnd_214833] using wordTrace_append hprefix tailTrace_214833
  have hstable : (prefixWord ++ tailWord_214833).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214833).length < 2 ^ (prefixWord ++ tailWord_214833).sum := by decide
  have hdescent : baseEnd_214833 < baseStart_214833 := by decide
  rcases family_descends (prefixWord ++ tailWord_214833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214873 : List Nat := [1, 2, 1, 2, 2, 3, 1, 7]
def baseStart_214873 : Nat := 118140960795 + 214873 * 2 ^ 59
def prefixEnd_214873 : Nat := 4983230072969 + 3 ^ 40 * 214873 * 2
def baseEnd_214873 : Nat := 65382594769566247169969

theorem tailTrace_214873 : CollatzResearch.WordTrace tailWord_214873 prefixEnd_214873 65382594769566247169969 := by
  unfold tailWord_214873
  simp only [CollatzResearch.WordTrace]
  refine ⟨7837062150559293231881273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5224708100372862154587515 7837062150559293231881273)
  ·
    refine ⟨5877796612919469923910955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7837062150559293231881273 5877796612919469923910955)
    ·
      refine ⟨8816694919379204885866433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5877796612919469923910955 8816694919379204885866433)
      ·
        refine ⟨6612521189534403664399825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8816694919379204885866433 6612521189534403664399825)
        ·
          refine ⟨4959390892150802748299869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6612521189534403664399825 4959390892150802748299869)
          ·
            refine ⟨1859771584556551030612451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4959390892150802748299869 1859771584556551030612451)
            ·
              refine ⟨2789657376834826545918677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859771584556551030612451 2789657376834826545918677)
              ·
                refine ⟨65382594769566247169969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2789657376834826545918677 65382594769566247169969)
                ·
                  rfl

theorem cell19_214873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_214873 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214873 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214873 prefixEnd_214873 := by exact prefixLift 214873
  have htrace : WordTrace (prefixWord ++ tailWord_214873) baseStart_214873 baseEnd_214873 := by
    simpa [prefixWord, tailWord_214873, baseEnd_214873] using wordTrace_append hprefix tailTrace_214873
  have hstable : (prefixWord ++ tailWord_214873).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214873).length < 2 ^ (prefixWord ++ tailWord_214873).sum := by decide
  have hdescent : baseEnd_214873 < baseStart_214873 := by decide
  rcases family_descends (prefixWord ++ tailWord_214873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214890 : List Nat := [3, 1, 3, 4, 8]
def baseStart_214890 : Nat := 118140960795 + 214890 * 2 ^ 59
def prefixEnd_214890 : Nat := 4983230072969 + 3 ^ 40 * 214890 * 2
def baseEnd_214890 : Nat := 2421769170804268325635

theorem tailTrace_214890 : CollatzResearch.WordTrace tailWord_214890 prefixEnd_214890 2421769170804268325635 := by
  unfold tailWord_214890
  simp only [CollatzResearch.WordTrace]
  refine ⟨1959420547874426283812531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5225121460998470090166749 1959420547874426283812531)
  ·
    refine ⟨2939130821811639425718797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1959420547874426283812531 2939130821811639425718797)
    ·
      refine ⟨1102174058179364784644549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2939130821811639425718797 1102174058179364784644549)
      ·
        refine ⟨206657635908630897120853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1102174058179364784644549 206657635908630897120853)
        ·
          refine ⟨2421769170804268325635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 206657635908630897120853 2421769170804268325635)
          ·
            rfl

theorem cell19_214890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 8].length) (baseStart_214890 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214890 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214890 prefixEnd_214890 := by exact prefixLift 214890
  have htrace : WordTrace (prefixWord ++ tailWord_214890) baseStart_214890 baseEnd_214890 := by
    simpa [prefixWord, tailWord_214890, baseEnd_214890] using wordTrace_append hprefix tailTrace_214890
  have hstable : (prefixWord ++ tailWord_214890).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214890).length < 2 ^ (prefixWord ++ tailWord_214890).sum := by decide
  have hdescent : baseEnd_214890 < baseStart_214890 := by decide
  rcases family_descends (prefixWord ++ tailWord_214890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214892 : List Nat := [2, 2, 1, 1, 4, 9]
def baseStart_214892 : Nat := 118140960795 + 214892 * 2 ^ 59
def prefixEnd_214892 : Nat := 4983230072969 + 3 ^ 40 * 214892 * 2
def baseEnd_214892 : Nat := 7265375131264425860855

theorem tailTrace_214892 : CollatzResearch.WordTrace tailWord_214892 prefixEnd_214892 7265375131264425860855 := by
  unfold tailWord_214892
  simp only [CollatzResearch.WordTrace]
  refine ⟨3918877568745229738411465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5225170091660306317881953 3918877568745229738411465)
  ·
    refine ⟨2939158176558922303808599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3918877568745229738411465 2939158176558922303808599)
    ·
      refine ⟨4408737264838383455712899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2939158176558922303808599 4408737264838383455712899)
      ·
        refine ⟨6613105897257575183569349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4408737264838383455712899 6613105897257575183569349)
        ·
          refine ⟨1239957355735795346919253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6613105897257575183569349 1239957355735795346919253)
          ·
            refine ⟨7265375131264425860855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1239957355735795346919253 7265375131264425860855)
            ·
              rfl

theorem cell19_214892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 9].length) (baseStart_214892 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214892 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214892 prefixEnd_214892 := by exact prefixLift 214892
  have htrace : WordTrace (prefixWord ++ tailWord_214892) baseStart_214892 baseEnd_214892 := by
    simpa [prefixWord, tailWord_214892, baseEnd_214892] using wordTrace_append hprefix tailTrace_214892
  have hstable : (prefixWord ++ tailWord_214892).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214892).length < 2 ^ (prefixWord ++ tailWord_214892).sum := by decide
  have hdescent : baseEnd_214892 < baseStart_214892 := by decide
  rcases family_descends (prefixWord ++ tailWord_214892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214968 : List Nat := [2, 1, 2, 1, 2, 3, 2, 6]
def baseStart_214968 : Nat := 118140960795 + 214968 * 2 ^ 59
def prefixEnd_214968 : Nat := 4983230072969 + 3 ^ 40 * 214968 * 2
def baseEnd_214968 : Nat := 65411501828634175058599

theorem tailTrace_214968 : CollatzResearch.WordTrace tailWord_214968 prefixEnd_214968 65411501828634175058599 := by
  unfold tailWord_214968
  simp only [CollatzResearch.WordTrace]
  refine ⟨3920263542607562228294779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5227018056810082971059705 3920263542607562228294779)
  ·
    refine ⟨5880395313911343342442169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3920263542607562228294779 5880395313911343342442169)
    ·
      refine ⟨4410296485433507506831627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5880395313911343342442169 4410296485433507506831627)
      ·
        refine ⟨6615444728150261260247441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4410296485433507506831627 6615444728150261260247441)
        ·
          refine ⟨4961583546112695945185581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6615444728150261260247441 4961583546112695945185581)
          ·
            refine ⟨1860593829792260979444593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4961583546112695945185581 1860593829792260979444593)
            ·
              refine ⟨1395445372344195734583445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1860593829792260979444593 1395445372344195734583445)
              ·
                refine ⟨65411501828634175058599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1395445372344195734583445 65411501828634175058599)
                ·
                  rfl

theorem cell19_214968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_214968 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214968 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214968 prefixEnd_214968 := by exact prefixLift 214968
  have htrace : WordTrace (prefixWord ++ tailWord_214968) baseStart_214968 baseEnd_214968 := by
    simpa [prefixWord, tailWord_214968, baseEnd_214968] using wordTrace_append hprefix tailTrace_214968
  have hstable : (prefixWord ++ tailWord_214968).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214968).length < 2 ^ (prefixWord ++ tailWord_214968).sum := by decide
  have hdescent : baseEnd_214968 < baseStart_214968 := by decide
  rcases family_descends (prefixWord ++ tailWord_214968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_214987 : List Nat := [1, 1, 1, 1, 3, 4, 3, 5]
def baseStart_214987 : Nat := 118140960795 + 214987 * 2 ^ 59
def prefixEnd_214987 : Nat := 4983230072969 + 3 ^ 40 * 214987 * 2
def baseEnd_214987 : Nat := 65417283240447760636325

theorem tailTrace_214987 : CollatzResearch.WordTrace tailWord_214987 prefixEnd_214987 65417283240447760636325 := by
  unfold tailWord_214987
  simp only [CollatzResearch.WordTrace]
  refine ⟨7841220072146290701531215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5227480048097527134354143 7841220072146290701531215)
  ·
    refine ⟨11761830108219436052296823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7841220072146290701531215 11761830108219436052296823)
    ·
      refine ⟨17642745162329154078445235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11761830108219436052296823 17642745162329154078445235)
      ·
        refine ⟨26464117743493731117667853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17642745162329154078445235 26464117743493731117667853)
        ·
          refine ⟨9924044153810149169125445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26464117743493731117667853 9924044153810149169125445)
          ·
            refine ⟨1860758278839402969211021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9924044153810149169125445 1860758278839402969211021)
            ·
              refine ⟨697784354564776113454133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1860758278839402969211021 697784354564776113454133)
              ·
                refine ⟨65417283240447760636325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 697784354564776113454133 65417283240447760636325)
                ·
                  rfl

theorem cell19_214987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_214987 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_214987 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_214987 prefixEnd_214987 := by exact prefixLift 214987
  have htrace : WordTrace (prefixWord ++ tailWord_214987) baseStart_214987 baseEnd_214987 := by
    simpa [prefixWord, tailWord_214987, baseEnd_214987] using wordTrace_append hprefix tailTrace_214987
  have hstable : (prefixWord ++ tailWord_214987).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_214987).length < 2 ^ (prefixWord ++ tailWord_214987).sum := by decide
  have hdescent : baseEnd_214987 < baseStart_214987 := by decide
  rcases family_descends (prefixWord ++ tailWord_214987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215002 : List Nat := [3, 1, 1, 2, 6, 1, 5]
def baseStart_215002 : Nat := 118140960795 + 215002 * 2 ^ 59
def prefixEnd_215002 : Nat := 4983230072969 + 3 ^ 40 * 215002 * 2
def baseEnd_215002 : Nat := 21807282504310723434317

theorem tailTrace_215002 : CollatzResearch.WordTrace tailWord_215002 prefixEnd_215002 21807282504310723434317 := by
  unfold tailWord_215002
  simp only [CollatzResearch.WordTrace]
  refine ⟨1960441791772987065831815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5227844778061298842218173 1960441791772987065831815)
  ·
    refine ⟨2940662687659480598747723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1960441791772987065831815 2940662687659480598747723)
    ·
      refine ⟨4410994031489220898121585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2940662687659480598747723 4410994031489220898121585)
      ·
        refine ⟨3308245523616915673591189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4410994031489220898121585 3308245523616915673591189)
        ·
          refine ⟨155074008919542922199587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3308245523616915673591189 155074008919542922199587)
          ·
            refine ⟨232611013379314383299381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155074008919542922199587 232611013379314383299381)
            ·
              refine ⟨21807282504310723434317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232611013379314383299381 21807282504310723434317)
              ·
                rfl

theorem cell19_215002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 6, 1, 5].length) (baseStart_215002 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215002 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215002 prefixEnd_215002 := by exact prefixLift 215002
  have htrace : WordTrace (prefixWord ++ tailWord_215002) baseStart_215002 baseEnd_215002 := by
    simpa [prefixWord, tailWord_215002, baseEnd_215002] using wordTrace_append hprefix tailTrace_215002
  have hstable : (prefixWord ++ tailWord_215002).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215002).length < 2 ^ (prefixWord ++ tailWord_215002).sum := by decide
  have hdescent : baseEnd_215002 < baseStart_215002 := by decide
  rcases family_descends (prefixWord ++ tailWord_215002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215061 : List Nat := [1, 3, 2, 1, 6, 6]
def baseStart_215061 : Nat := 118140960795 + 215061 * 2 ^ 59
def prefixEnd_215061 : Nat := 4983230072969 + 3 ^ 40 * 215061 * 2
def baseEnd_215061 : Nat := 7271088924226390554631

theorem tailTrace_215061 : CollatzResearch.WordTrace tailWord_215061 prefixEnd_215061 7271088924226390554631 := by
  unfold tailWord_215061
  simp only [CollatzResearch.WordTrace]
  refine ⟨7843919073878201339725037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5229279382585467559816691 7843919073878201339725037)
  ·
    refine ⟨2941469652704325502396889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7843919073878201339725037 2941469652704325502396889)
    ·
      refine ⟨2206102239528244126797667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2941469652704325502396889 2206102239528244126797667)
      ·
        refine ⟨3309153359292366190196501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2206102239528244126797667 3309153359292366190196501)
        ·
          refine ⟨155116563716829665165461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3309153359292366190196501 155116563716829665165461)
          ·
            refine ⟨7271088924226390554631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155116563716829665165461 7271088924226390554631)
            ·
              rfl

theorem cell19_215061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 6].length) (baseStart_215061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215061 prefixEnd_215061 := by exact prefixLift 215061
  have htrace : WordTrace (prefixWord ++ tailWord_215061) baseStart_215061 baseEnd_215061 := by
    simpa [prefixWord, tailWord_215061, baseEnd_215061] using wordTrace_append hprefix tailTrace_215061
  have hstable : (prefixWord ++ tailWord_215061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215061).length < 2 ^ (prefixWord ++ tailWord_215061).sum := by decide
  have hdescent : baseEnd_215061 < baseStart_215061 := by decide
  rcases family_descends (prefixWord ++ tailWord_215061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215063 : List Nat := [1, 1, 3, 5, 9]
def baseStart_215063 : Nat := 118140960795 + 215063 * 2 ^ 59
def prefixEnd_215063 : Nat := 4983230072969 + 3 ^ 40 * 215063 * 2
def baseEnd_215063 : Nat := 2423718847692670479527

theorem tailTrace_215063 : CollatzResearch.WordTrace tailWord_215063 prefixEnd_215063 2423718847692670479527 := by
  unfold tailWord_215063
  simp only [CollatzResearch.WordTrace]
  refine ⟨7843992019870955681297843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5229328013247303787531895 7843992019870955681297843)
  ·
    refine ⟨11765988029806433521946765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7843992019870955681297843 11765988029806433521946765)
    ·
      refine ⟨4412245511177412570730037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11765988029806433521946765 4412245511177412570730037)
      ·
        refine ⟨413648016672882428505941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4412245511177412570730037 413648016672882428505941)
        ·
          refine ⟨2423718847692670479527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 413648016672882428505941 2423718847692670479527)
          ·
            rfl

theorem cell19_215063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 9].length) (baseStart_215063 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215063 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215063 prefixEnd_215063 := by exact prefixLift 215063
  have htrace : WordTrace (prefixWord ++ tailWord_215063) baseStart_215063 baseEnd_215063 := by
    simpa [prefixWord, tailWord_215063, baseEnd_215063] using wordTrace_append hprefix tailTrace_215063
  have hstable : (prefixWord ++ tailWord_215063).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215063).length < 2 ^ (prefixWord ++ tailWord_215063).sum := by decide
  have hdescent : baseEnd_215063 < baseStart_215063 := by decide
  rcases family_descends (prefixWord ++ tailWord_215063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215076 : List Nat := [2, 3, 1, 4, 3, 1, 1, 4]
def baseStart_215076 : Nat := 118140960795 + 215076 * 2 ^ 59
def prefixEnd_215076 : Nat := 4983230072969 + 3 ^ 40 * 215076 * 2
def baseEnd_215076 : Nat := 65444364590521924658305

theorem tailTrace_215076 : CollatzResearch.WordTrace tailWord_215076 prefixEnd_215076 65444364590521924658305 := by
  unfold tailWord_215076
  simp only [CollatzResearch.WordTrace]
  refine ⟨3922233084411929450760541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5229644112549239267680721 3922233084411929450760541)
  ·
    refine ⟨1470837406654473544035203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3922233084411929450760541 1470837406654473544035203)
    ·
      refine ⟨2206256109981710316052805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1470837406654473544035203 2206256109981710316052805)
      ·
        refine ⟨413673020621570684259901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2206256109981710316052805 413673020621570684259901)
        ·
          refine ⟨155127382733089006597463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 413673020621570684259901 155127382733089006597463)
          ·
            refine ⟨232691074099633509896195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155127382733089006597463 232691074099633509896195)
            ·
              refine ⟨349036611149450264844293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232691074099633509896195 349036611149450264844293)
              ·
                refine ⟨65444364590521924658305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 349036611149450264844293 65444364590521924658305)
                ·
                  rfl

theorem cell19_215076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_215076 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215076 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215076 prefixEnd_215076 := by exact prefixLift 215076
  have htrace : WordTrace (prefixWord ++ tailWord_215076) baseStart_215076 baseEnd_215076 := by
    simpa [prefixWord, tailWord_215076, baseEnd_215076] using wordTrace_append hprefix tailTrace_215076
  have hstable : (prefixWord ++ tailWord_215076).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215076).length < 2 ^ (prefixWord ++ tailWord_215076).sum := by decide
  have hdescent : baseEnd_215076 < baseStart_215076 := by decide
  rcases family_descends (prefixWord ++ tailWord_215076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215097 : List Nat := [1, 2, 1, 5, 3, 1, 3, 3]
def baseStart_215097 : Nat := 118140960795 + 215097 * 2 ^ 59
def prefixEnd_215097 : Nat := 4983230072969 + 3 ^ 40 * 215097 * 2
def baseEnd_215097 : Nat := 65450754572000098191581

theorem tailTrace_215097 : CollatzResearch.WordTrace tailWord_215097 prefixEnd_215097 65450754572000098191581 := by
  unfold tailWord_215097
  simp only [CollatzResearch.WordTrace]
  refine ⟨7845232101747779488035545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5230154734498519658690363 7845232101747779488035545)
  ·
    refine ⟨5883924076310834616026659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7845232101747779488035545 5883924076310834616026659)
    ·
      refine ⟨8825886114466251924039989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5883924076310834616026659 8825886114466251924039989)
      ·
        refine ⟨827426823231211117878749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8825886114466251924039989 827426823231211117878749)
        ·
          refine ⟨310285058711704169204531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 827426823231211117878749 310285058711704169204531)
          ·
            refine ⟨465427588067556253806797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 310285058711704169204531 465427588067556253806797)
            ·
              refine ⟨174535345525333595177549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 465427588067556253806797 174535345525333595177549)
              ·
                refine ⟨65450754572000098191581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174535345525333595177549 65450754572000098191581)
                ·
                  rfl

theorem cell19_215097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 3].length) (baseStart_215097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215097 prefixEnd_215097 := by exact prefixLift 215097
  have htrace : WordTrace (prefixWord ++ tailWord_215097) baseStart_215097 baseEnd_215097 := by
    simpa [prefixWord, tailWord_215097, baseEnd_215097] using wordTrace_append hprefix tailTrace_215097
  have hstable : (prefixWord ++ tailWord_215097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215097).length < 2 ^ (prefixWord ++ tailWord_215097).sum := by decide
  have hdescent : baseEnd_215097 < baseStart_215097 := by decide
  rcases family_descends (prefixWord ++ tailWord_215097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215154 : List Nat := [3, 2, 1, 2, 2, 4, 2, 3]
def baseStart_215154 : Nat := 118140960795 + 215154 * 2 ^ 59
def prefixEnd_215154 : Nat := 4983230072969 + 3 ^ 40 * 215154 * 2
def baseEnd_215154 : Nat := 65468098807440854924759

theorem tailTrace_215154 : CollatzResearch.WordTrace tailWord_215154 prefixEnd_215154 65468098807440854924759 := by
  unfold tailWord_215154
  simp only [CollatzResearch.WordTrace]
  refine ⟨1961827765635319555715129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5231540708360852148573677 1961827765635319555715129)
  ·
    refine ⟨1471370824226489666786347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1961827765635319555715129 1471370824226489666786347)
    ·
      refine ⟨2207056236339734500179521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1471370824226489666786347 2207056236339734500179521)
      ·
        refine ⟨1655292177254800875134641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2207056236339734500179521 1655292177254800875134641)
        ·
          refine ⟨1241469132941100656350981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1655292177254800875134641 1241469132941100656350981)
          ·
            refine ⟨232775462426456373065809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1241469132941100656350981 232775462426456373065809)
            ·
              refine ⟨174581596819842279799357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 232775462426456373065809 174581596819842279799357)
              ·
                refine ⟨65468098807440854924759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174581596819842279799357 65468098807440854924759)
                ·
                  rfl

theorem cell19_215154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_215154 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215154 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215154 prefixEnd_215154 := by exact prefixLift 215154
  have htrace : WordTrace (prefixWord ++ tailWord_215154) baseStart_215154 baseEnd_215154 := by
    simpa [prefixWord, tailWord_215154, baseEnd_215154] using wordTrace_append hprefix tailTrace_215154
  have hstable : (prefixWord ++ tailWord_215154).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215154).length < 2 ^ (prefixWord ++ tailWord_215154).sum := by decide
  have hdescent : baseEnd_215154 < baseStart_215154 := by decide
  rcases family_descends (prefixWord ++ tailWord_215154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215213 : List Nat := [1, 5, 2, 1, 2, 1, 2, 5]
def baseStart_215213 : Nat := 118140960795 + 215213 * 2 ^ 59
def prefixEnd_215213 : Nat := 4983230072969 + 3 ^ 40 * 215213 * 2
def baseEnd_215213 : Nat := 65486051612546199613487

theorem tailTrace_215213 : CollatzResearch.WordTrace tailWord_215213 prefixEnd_215213 65486051612546199613487 := by
  unfold tailWord_215213
  simp only [CollatzResearch.WordTrace]
  refine ⟨7849462969327531299258293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5232975312885020866172195 7849462969327531299258293)
  ·
    refine ⟨735887153374456059305465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7849462969327531299258293 735887153374456059305465)
    ·
      refine ⟨551915365030842044479099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 735887153374456059305465 551915365030842044479099)
      ·
        refine ⟨827873047546263066718649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 551915365030842044479099 827873047546263066718649)
        ·
          refine ⟨620904785659697300038987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 827873047546263066718649 620904785659697300038987)
          ·
            refine ⟨931357178489545950058481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 620904785659697300038987 931357178489545950058481)
            ·
              refine ⟨698517883867159462543861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 931357178489545950058481 698517883867159462543861)
              ·
                refine ⟨65486051612546199613487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 698517883867159462543861 65486051612546199613487)
                ·
                  rfl

theorem cell19_215213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 5].length) (baseStart_215213 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215213 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215213 prefixEnd_215213 := by exact prefixLift 215213
  have htrace : WordTrace (prefixWord ++ tailWord_215213) baseStart_215213 baseEnd_215213 := by
    simpa [prefixWord, tailWord_215213, baseEnd_215213] using wordTrace_append hprefix tailTrace_215213
  have hstable : (prefixWord ++ tailWord_215213).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215213).length < 2 ^ (prefixWord ++ tailWord_215213).sum := by decide
  have hdescent : baseEnd_215213 < baseStart_215213 := by decide
  rcases family_descends (prefixWord ++ tailWord_215213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215310 : List Nat := [4, 1, 1, 2, 1, 2, 2, 6]
def baseStart_215310 : Nat := 118140960795 + 215310 * 2 ^ 59
def prefixEnd_215310 : Nat := 4983230072969 + 3 ^ 40 * 215310 * 2
def baseEnd_215310 : Nat := 65515567241278715457667

theorem tailTrace_215310 : CollatzResearch.WordTrace tailWord_215310 prefixEnd_215310 65515567241278715457667 := by
  unfold tailWord_215310
  simp only [CollatzResearch.WordTrace]
  refine ⟨981625106247014608192423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5235333899984077910359589 981625106247014608192423)
  ·
    refine ⟨1472437659370521912288635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 981625106247014608192423 1472437659370521912288635)
    ·
      refine ⟨2208656489055782868432953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1472437659370521912288635 2208656489055782868432953)
      ·
        refine ⟨1656492366791837151324715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2208656489055782868432953 1656492366791837151324715)
        ·
          refine ⟨2484738550187755726987073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1656492366791837151324715 2484738550187755726987073)
          ·
            refine ⟨1863553912640816795240305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2484738550187755726987073 1863553912640816795240305)
            ·
              refine ⟨1397665434480612596430229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1863553912640816795240305 1397665434480612596430229)
              ·
                refine ⟨65515567241278715457667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1397665434480612596430229 65515567241278715457667)
                ·
                  rfl

theorem cell19_215310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_215310 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215310 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215310 prefixEnd_215310 := by exact prefixLift 215310
  have htrace : WordTrace (prefixWord ++ tailWord_215310) baseStart_215310 baseEnd_215310 := by
    simpa [prefixWord, tailWord_215310, baseEnd_215310] using wordTrace_append hprefix tailTrace_215310
  have hstable : (prefixWord ++ tailWord_215310).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215310).length < 2 ^ (prefixWord ++ tailWord_215310).sum := by decide
  have hdescent : baseEnd_215310 < baseStart_215310 := by decide
  rcases family_descends (prefixWord ++ tailWord_215310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215327 : List Nat := [1, 1, 2, 4, 3, 1, 4, 3]
def baseStart_215327 : Nat := 118140960795 + 215327 * 2 ^ 59
def prefixEnd_215327 : Nat := 4983230072969 + 3 ^ 40 * 215327 * 2
def baseEnd_215327 : Nat := 65520740083427713079843

theorem tailTrace_215327 : CollatzResearch.WordTrace tailWord_215327 prefixEnd_215327 65520740083427713079843 := by
  unfold tailWord_215327
  simp only [CollatzResearch.WordTrace]
  refine ⟨7853620890914528768908235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5235747260609685845938823 7853620890914528768908235)
  ·
    refine ⟨11780431336371793153362353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7853620890914528768908235 11780431336371793153362353)
    ·
      refine ⟨8835323502278844865021765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11780431336371793153362353 8835323502278844865021765)
      ·
        refine ⟨1656623156677283412191581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8835323502278844865021765 1656623156677283412191581)
        ·
          refine ⟨621233683753981279571843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1656623156677283412191581 621233683753981279571843)
          ·
            refine ⟨931850525630971919357765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 621233683753981279571843 931850525630971919357765)
            ·
              refine ⟨174721973555807234879581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 931850525630971919357765 174721973555807234879581)
              ·
                refine ⟨65520740083427713079843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174721973555807234879581 65520740083427713079843)
                ·
                  rfl

theorem cell19_215327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 3].length) (baseStart_215327 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215327 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215327 prefixEnd_215327 := by exact prefixLift 215327
  have htrace : WordTrace (prefixWord ++ tailWord_215327) baseStart_215327 baseEnd_215327 := by
    simpa [prefixWord, tailWord_215327, baseEnd_215327] using wordTrace_append hprefix tailTrace_215327
  have hstable : (prefixWord ++ tailWord_215327).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215327).length < 2 ^ (prefixWord ++ tailWord_215327).sum := by decide
  have hdescent : baseEnd_215327 < baseStart_215327 := by decide
  rcases family_descends (prefixWord ++ tailWord_215327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215342 : List Nat := [4, 1, 3, 3, 2, 1, 5]
def baseStart_215342 : Nat := 118140960795 + 215342 * 2 ^ 59
def prefixEnd_215342 : Nat := 4983230072969 + 3 ^ 40 * 215342 * 2
def baseEnd_215342 : Nat := 21841768118637374248823

theorem tailTrace_215342 : CollatzResearch.WordTrace tailWord_215342 prefixEnd_215342 21841768118637374248823 := by
  unfold tailWord_215342
  simp only [CollatzResearch.WordTrace]
  refine ⟨981770998232523291338035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5236111990573457553802853 981770998232523291338035)
  ·
    refine ⟨1472656497348784937007053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 981770998232523291338035 1472656497348784937007053)
    ·
      refine ⟨552246186505794351377645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1472656497348784937007053 552246186505794351377645)
      ·
        refine ⟨207092319939672881766617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 552246186505794351377645 207092319939672881766617)
        ·
          refine ⟨155319239954754661324963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207092319939672881766617 155319239954754661324963)
          ·
            refine ⟨232978859932131991987445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155319239954754661324963 232978859932131991987445)
            ·
              refine ⟨21841768118637374248823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232978859932131991987445 21841768118637374248823)
              ·
                rfl

theorem cell19_215342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 5].length) (baseStart_215342 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215342 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215342 prefixEnd_215342 := by exact prefixLift 215342
  have htrace : WordTrace (prefixWord ++ tailWord_215342) baseStart_215342 baseEnd_215342 := by
    simpa [prefixWord, tailWord_215342, baseEnd_215342] using wordTrace_append hprefix tailTrace_215342
  have hstable : (prefixWord ++ tailWord_215342).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215342).length < 2 ^ (prefixWord ++ tailWord_215342).sum := by decide
  have hdescent : baseEnd_215342 < baseStart_215342 := by decide
  rcases family_descends (prefixWord ++ tailWord_215342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215346 : List Nat := [3, 2, 1, 1, 5, 2, 5]
def baseStart_215346 : Nat := 118140960795 + 215346 * 2 ^ 59
def prefixEnd_215346 : Nat := 4983230072969 + 3 ^ 40 * 215346 * 2
def baseEnd_215346 : Nat := 21842173831747099552523

theorem tailTrace_215346 : CollatzResearch.WordTrace tailWord_215346 prefixEnd_215346 21842173831747099552523 := by
  unfold tailWord_215346
  simp only [CollatzResearch.WordTrace]
  refine ⟨1963578469461423753462473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5236209251897130009233261 1963578469461423753462473)
  ·
    refine ⟨1472683852096067815096855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1963578469461423753462473 1472683852096067815096855)
    ·
      refine ⟨2209025778144101722645283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1472683852096067815096855 2209025778144101722645283)
      ·
        refine ⟨3313538667216152583967925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209025778144101722645283 3313538667216152583967925)
        ·
          refine ⟨310644250051514304746993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3313538667216152583967925 310644250051514304746993)
          ·
            refine ⟨232983187538635728560245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 310644250051514304746993 232983187538635728560245)
            ·
              refine ⟨21842173831747099552523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 232983187538635728560245 21842173831747099552523)
              ·
                rfl

theorem cell19_215346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_215346 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215346 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215346 prefixEnd_215346 := by exact prefixLift 215346
  have htrace : WordTrace (prefixWord ++ tailWord_215346) baseStart_215346 baseEnd_215346 := by
    simpa [prefixWord, tailWord_215346, baseEnd_215346] using wordTrace_append hprefix tailTrace_215346
  have hstable : (prefixWord ++ tailWord_215346).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215346).length < 2 ^ (prefixWord ++ tailWord_215346).sum := by decide
  have hdescent : baseEnd_215346 < baseStart_215346 := by decide
  rcases family_descends (prefixWord ++ tailWord_215346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215367 : List Nat := [1, 1, 4, 1, 2, 2, 4, 4]
def baseStart_215367 : Nat := 118140960795 + 215367 * 2 ^ 59
def prefixEnd_215367 : Nat := 4983230072969 + 3 ^ 40 * 215367 * 2
def baseEnd_215367 : Nat := 65532911476719472190845

theorem tailTrace_215367 : CollatzResearch.WordTrace tailWord_215367 prefixEnd_215367 65532911476719472190845 := by
  unfold tailWord_215367
  simp only [CollatzResearch.WordTrace]
  refine ⟨7855079810769615600364355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5236719873846410400242903 7855079810769615600364355)
  ·
    refine ⟨11782619716154423400546533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7855079810769615600364355 11782619716154423400546533)
    ·
      refine ⟨2209241196778954387602475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11782619716154423400546533 2209241196778954387602475)
      ·
        refine ⟨3313861795168431581403713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2209241196778954387602475 3313861795168431581403713)
        ·
          refine ⟨2485396346376323686052785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3313861795168431581403713 2485396346376323686052785)
          ·
            refine ⟨1864047259782242764539589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2485396346376323686052785 1864047259782242764539589)
            ·
              refine ⟨349508861209170518351173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1864047259782242764539589 349508861209170518351173)
              ·
                refine ⟨65532911476719472190845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 349508861209170518351173 65532911476719472190845)
                ·
                  rfl

theorem cell19_215367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_215367 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215367 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215367 prefixEnd_215367 := by exact prefixLift 215367
  have htrace : WordTrace (prefixWord ++ tailWord_215367) baseStart_215367 baseEnd_215367 := by
    simpa [prefixWord, tailWord_215367, baseEnd_215367] using wordTrace_append hprefix tailTrace_215367
  have hstable : (prefixWord ++ tailWord_215367).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215367).length < 2 ^ (prefixWord ++ tailWord_215367).sum := by decide
  have hdescent : baseEnd_215367 < baseStart_215367 := by decide
  rcases family_descends (prefixWord ++ tailWord_215367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215519 : List Nat := [1, 1, 2, 3, 3, 4, 5]
def baseStart_215519 : Nat := 118140960795 + 215519 * 2 ^ 59
def prefixEnd_215519 : Nat := 4983230072969 + 3 ^ 40 * 215519 * 2
def baseEnd_215519 : Nat := 21859720923742718937551

theorem tailTrace_215519 : CollatzResearch.WordTrace tailWord_215519 prefixEnd_215519 21859720923742718937551 := by
  unfold tailWord_215519
  simp only [CollatzResearch.WordTrace]
  refine ⟨7860623706218945559897611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5240415804145963706598407 7860623706218945559897611)
  ·
    refine ⟨11790935559328418339846417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7860623706218945559897611 11790935559328418339846417)
    ·
      refine ⟨8843201669496313754884813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11790935559328418339846417 8843201669496313754884813)
      ·
        refine ⟨3316200626061117658081805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8843201669496313754884813 3316200626061117658081805)
        ·
          refine ⟨1243575234772919121780677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3316200626061117658081805 1243575234772919121780677)
          ·
            refine ⟨233170356519922335333877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1243575234772919121780677 233170356519922335333877)
            ·
              refine ⟨21859720923742718937551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 233170356519922335333877 21859720923742718937551)
              ·
                rfl

theorem cell19_215519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 5].length) (baseStart_215519 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215519 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215519 prefixEnd_215519 := by exact prefixLift 215519
  have htrace : WordTrace (prefixWord ++ tailWord_215519) baseStart_215519 baseEnd_215519 := by
    simpa [prefixWord, tailWord_215519, baseEnd_215519] using wordTrace_append hprefix tailTrace_215519
  have hstable : (prefixWord ++ tailWord_215519).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215519).length < 2 ^ (prefixWord ++ tailWord_215519).sum := by decide
  have hdescent : baseEnd_215519 < baseStart_215519 := by decide
  rcases family_descends (prefixWord ++ tailWord_215519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215612 : List Nat := [2, 2, 2, 2, 3, 2, 3, 3]
def baseStart_215612 : Nat := 118140960795 + 215612 * 2 ^ 59
def prefixEnd_215612 : Nat := 4983230072969 + 3 ^ 40 * 215612 * 2
def baseEnd_215612 : Nat := 65607461260631496745733

theorem tailTrace_215612 : CollatzResearch.WordTrace tailWord_215612 prefixEnd_215612 65607461260631496745733 := by
  unfold tailWord_215612
  simp only [CollatzResearch.WordTrace]
  refine ⟨3932007847441011221516545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5242677129921348295355393 3932007847441011221516545)
  ·
    refine ⟨2949005885580758416137409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3932007847441011221516545 2949005885580758416137409)
    ·
      refine ⟨2211754414185568812103057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2949005885580758416137409 2211754414185568812103057)
      ·
        refine ⟨1658815810639176609077293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2211754414185568812103057 1658815810639176609077293)
        ·
          refine ⟨622055928989691228403985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1658815810639176609077293 622055928989691228403985)
          ·
            refine ⟨466541946742268421302989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 622055928989691228403985 466541946742268421302989)
            ·
              refine ⟨174953230028350657988621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 466541946742268421302989 174953230028350657988621)
              ·
                refine ⟨65607461260631496745733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174953230028350657988621 65607461260631496745733)
                ·
                  rfl

theorem cell19_215612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_215612 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215612 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215612 prefixEnd_215612 := by exact prefixLift 215612
  have htrace : WordTrace (prefixWord ++ tailWord_215612) baseStart_215612 baseEnd_215612 := by
    simpa [prefixWord, tailWord_215612, baseEnd_215612] using wordTrace_append hprefix tailTrace_215612
  have hstable : (prefixWord ++ tailWord_215612).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215612).length < 2 ^ (prefixWord ++ tailWord_215612).sum := by decide
  have hdescent : baseEnd_215612 < baseStart_215612 := by decide
  rcases family_descends (prefixWord ++ tailWord_215612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215616 : List Nat := [2, 1, 1, 2, 2, 2, 2, 7]
def baseStart_215616 : Nat := 118140960795 + 215616 * 2 ^ 59
def prefixEnd_215616 : Nat := 4983230072969 + 3 ^ 40 * 215616 * 2
def baseEnd_215616 : Nat := 65608678399960672656833

theorem tailTrace_215616 : CollatzResearch.WordTrace tailWord_215616 prefixEnd_215616 65608678399960672656833 := by
  unfold tailWord_215616
  simp only [CollatzResearch.WordTrace]
  refine ⟨3932080793433765563089351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5242774391245020750785801 3932080793433765563089351)
  ·
    refine ⟨5898121190150648344634027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3932080793433765563089351 5898121190150648344634027)
    ·
      refine ⟨8847181785225972516951041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5898121190150648344634027 8847181785225972516951041)
      ·
        refine ⟨6635386338919479387713281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8847181785225972516951041 6635386338919479387713281)
        ·
          refine ⟨4976539754189609540784961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6635386338919479387713281 4976539754189609540784961)
          ·
            refine ⟨3732404815642207155588721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4976539754189609540784961 3732404815642207155588721)
            ·
              refine ⟨2799303611731655366691541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3732404815642207155588721 2799303611731655366691541)
              ·
                refine ⟨65608678399960672656833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2799303611731655366691541 65608678399960672656833)
                ·
                  rfl

theorem cell19_215616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_215616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215616 prefixEnd_215616 := by exact prefixLift 215616
  have htrace : WordTrace (prefixWord ++ tailWord_215616) baseStart_215616 baseEnd_215616 := by
    simpa [prefixWord, tailWord_215616, baseEnd_215616] using wordTrace_append hprefix tailTrace_215616
  have hstable : (prefixWord ++ tailWord_215616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215616).length < 2 ^ (prefixWord ++ tailWord_215616).sum := by decide
  have hdescent : baseEnd_215616 < baseStart_215616 := by decide
  rcases family_descends (prefixWord ++ tailWord_215616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215669 : List Nat := [1, 3, 4, 2, 2, 1, 1, 5]
def baseStart_215669 : Nat := 118140960795 + 215669 * 2 ^ 59
def prefixEnd_215669 : Nat := 4983230072969 + 3 ^ 40 * 215669 * 2
def baseEnd_215669 : Nat := 65624805496072253478911

theorem tailTrace_215669 : CollatzResearch.WordTrace tailWord_215669 prefixEnd_215669 65624805496072253478911 := by
  unfold tailWord_215669
  simp only [CollatzResearch.WordTrace]
  refine ⟨7866094655675521177858061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5244063103783680785238707 7866094655675521177858061)
  ·
    refine ⟨2949785495878320441696773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7866094655675521177858061 2949785495878320441696773)
    ·
      refine ⟨553084780477185082818145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2949785495878320441696773 553084780477185082818145)
      ·
        refine ⟨414813585357888812113609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 553084780477185082818145 414813585357888812113609)
        ·
          refine ⟨311110189018416609085207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 414813585357888812113609 311110189018416609085207)
          ·
            refine ⟨466665283527624913627811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311110189018416609085207 466665283527624913627811)
            ·
              refine ⟨699997925291437370441717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 466665283527624913627811 699997925291437370441717)
              ·
                refine ⟨65624805496072253478911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 699997925291437370441717 65624805496072253478911)
                ·
                  rfl

theorem cell19_215669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_215669 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215669 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215669 prefixEnd_215669 := by exact prefixLift 215669
  have htrace : WordTrace (prefixWord ++ tailWord_215669) baseStart_215669 baseEnd_215669 := by
    simpa [prefixWord, tailWord_215669, baseEnd_215669] using wordTrace_append hprefix tailTrace_215669
  have hstable : (prefixWord ++ tailWord_215669).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215669).length < 2 ^ (prefixWord ++ tailWord_215669).sum := by decide
  have hdescent : baseEnd_215669 < baseStart_215669 := by decide
  rcases family_descends (prefixWord ++ tailWord_215669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215671 : List Nat := [1, 1, 3, 1, 1, 3, 6, 3]
def baseStart_215671 : Nat := 118140960795 + 215671 * 2 ^ 59
def prefixEnd_215671 : Nat := 4983230072969 + 3 ^ 40 * 215671 * 2
def baseEnd_215671 : Nat := 65625414065736841434461

theorem tailTrace_215671 : CollatzResearch.WordTrace tailWord_215671 prefixEnd_215671 65625414065736841434461 := by
  unfold tailWord_215671
  simp only [CollatzResearch.WordTrace]
  refine ⟨7866167601668275519430867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5244111734445517012953911 7866167601668275519430867)
  ·
    refine ⟨11799251402502413279146301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7866167601668275519430867 11799251402502413279146301)
    ·
      refine ⟨4424719275938404979679863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11799251402502413279146301 4424719275938404979679863)
      ·
        refine ⟨6637078913907607469519795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4424719275938404979679863 6637078913907607469519795)
        ·
          refine ⟨9955618370861411204279693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6637078913907607469519795 9955618370861411204279693)
          ·
            refine ⟨3733356889073029201604885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9955618370861411204279693 3733356889073029201604885)
            ·
              refine ⟨175001104175298243825229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 3733356889073029201604885 175001104175298243825229)
              ·
                refine ⟨65625414065736841434461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175001104175298243825229 65625414065736841434461)
                ·
                  rfl

theorem cell19_215671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 3].length) (baseStart_215671 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215671 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215671 prefixEnd_215671 := by exact prefixLift 215671
  have htrace : WordTrace (prefixWord ++ tailWord_215671) baseStart_215671 baseEnd_215671 := by
    simpa [prefixWord, tailWord_215671, baseEnd_215671] using wordTrace_append hprefix tailTrace_215671
  have hstable : (prefixWord ++ tailWord_215671).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215671).length < 2 ^ (prefixWord ++ tailWord_215671).sum := by decide
  have hdescent : baseEnd_215671 < baseStart_215671 := by decide
  rcases family_descends (prefixWord ++ tailWord_215671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215682 : List Nat := [3, 4, 3, 1, 2, 1, 5]
def baseStart_215682 : Nat := 118140960795 + 215682 * 2 ^ 59
def prefixEnd_215682 : Nat := 4983230072969 + 3 ^ 40 * 215682 * 2
def baseEnd_215682 : Nat := 21876253732964025063329

theorem tailTrace_215682 : CollatzResearch.WordTrace tailWord_215682 prefixEnd_215682 21876253732964025063329 := by
  unfold tailWord_215682
  simp only [CollatzResearch.WordTrace]
  refine ⟨1966642201157106099520325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5244379203085616265387533 1966642201157106099520325)
  ·
    refine ⟨368745412716957393660061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1966642201157106099520325 368745412716957393660061)
    ·
      refine ⟨138279529768859022622523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 368745412716957393660061 138279529768859022622523)
      ·
        refine ⟨207419294653288533933785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138279529768859022622523 207419294653288533933785)
        ·
          refine ⟨155564470989966400450339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207419294653288533933785 155564470989966400450339)
          ·
            refine ⟨233346706484949600675509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155564470989966400450339 233346706484949600675509)
            ·
              refine ⟨21876253732964025063329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 233346706484949600675509 21876253732964025063329)
              ·
                rfl

theorem cell19_215682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 2, 1, 5].length) (baseStart_215682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215682 prefixEnd_215682 := by exact prefixLift 215682
  have htrace : WordTrace (prefixWord ++ tailWord_215682) baseStart_215682 baseEnd_215682 := by
    simpa [prefixWord, tailWord_215682, baseEnd_215682] using wordTrace_append hprefix tailTrace_215682
  have hstable : (prefixWord ++ tailWord_215682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215682).length < 2 ^ (prefixWord ++ tailWord_215682).sum := by decide
  have hdescent : baseEnd_215682 < baseStart_215682 := by decide
  rcases family_descends (prefixWord ++ tailWord_215682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215726 : List Nat := [4, 1, 4, 1, 1, 1, 2, 5]
def baseStart_215726 : Nat := 118140960795 + 215726 * 2 ^ 59
def prefixEnd_215726 : Nat := 4983230072969 + 3 ^ 40 * 215726 * 2
def baseEnd_215726 : Nat := 65642149731513010212089

theorem tailTrace_215726 : CollatzResearch.WordTrace tailWord_215726 prefixEnd_215726 65642149731513010212089 := by
  unfold tailWord_215726
  simp only [CollatzResearch.WordTrace]
  refine ⟨983521702058627489085379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5245449077646013275122021 983521702058627489085379)
  ·
    refine ⟨1475282553087941233628069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 983521702058627489085379 1475282553087941233628069)
    ·
      refine ⟨276615478703988981305263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1475282553087941233628069 276615478703988981305263)
      ·
        refine ⟨414923218055983471957895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 276615478703988981305263 414923218055983471957895)
        ·
          refine ⟨622384827083975207936843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 414923218055983471957895 622384827083975207936843)
          ·
            refine ⟨933577240625962811905265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 622384827083975207936843 933577240625962811905265)
            ·
              refine ⟨700182930469472108928949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 933577240625962811905265 700182930469472108928949)
              ·
                refine ⟨65642149731513010212089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 700182930469472108928949 65642149731513010212089)
                ·
                  rfl

theorem cell19_215726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 2, 5].length) (baseStart_215726 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215726 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215726 prefixEnd_215726 := by exact prefixLift 215726
  have htrace : WordTrace (prefixWord ++ tailWord_215726) baseStart_215726 baseEnd_215726 := by
    simpa [prefixWord, tailWord_215726, baseEnd_215726] using wordTrace_append hprefix tailTrace_215726
  have hstable : (prefixWord ++ tailWord_215726).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215726).length < 2 ^ (prefixWord ++ tailWord_215726).sum := by decide
  have hdescent : baseEnd_215726 < baseStart_215726 := by decide
  rcases family_descends (prefixWord ++ tailWord_215726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215745 : List Nat := [1, 2, 6, 2, 1, 7]
def baseStart_215745 : Nat := 118140960795 + 215745 * 2 ^ 59
def prefixEnd_215745 : Nat := 4983230072969 + 3 ^ 40 * 215745 * 2
def baseEnd_215745 : Nat := 7294214571480732865535

theorem tailTrace_215745 : CollatzResearch.WordTrace tailWord_215745 prefixEnd_215745 7294214571480732865535 := by
  unfold tailWord_215745
  simp only [CollatzResearch.WordTrace]
  refine ⟨7868866603400186157624689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5245911068933457438416459 7868866603400186157624689)
  ·
    refine ⟨5901649952550139618218517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7868866603400186157624689 5901649952550139618218517)
    ·
      refine ⟨276639841525787794603993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5901649952550139618218517 276639841525787794603993)
      ·
        refine ⟨207479881144340845952995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276639841525787794603993 207479881144340845952995)
        ·
          refine ⟨311219821716511268929493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207479881144340845952995 311219821716511268929493)
          ·
            refine ⟨7294214571480732865535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 311219821716511268929493 7294214571480732865535)
            ·
              rfl

theorem cell19_215745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 7].length) (baseStart_215745 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215745 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215745 prefixEnd_215745 := by exact prefixLift 215745
  have htrace : WordTrace (prefixWord ++ tailWord_215745) baseStart_215745 baseEnd_215745 := by
    simpa [prefixWord, tailWord_215745, baseEnd_215745] using wordTrace_append hprefix tailTrace_215745
  have hstable : (prefixWord ++ tailWord_215745).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215745).length < 2 ^ (prefixWord ++ tailWord_215745).sum := by decide
  have hdescent : baseEnd_215745 < baseStart_215745 := by decide
  rcases family_descends (prefixWord ++ tailWord_215745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215762 : List Nat := [3, 2, 2, 2, 4, 1, 1, 4]
def baseStart_215762 : Nat := 118140960795 + 215762 * 2 ^ 59
def prefixEnd_215762 : Nat := 4983230072969 + 3 ^ 40 * 215762 * 2
def baseEnd_215762 : Nat := 65653103985475593411991

theorem tailTrace_215762 : CollatzResearch.WordTrace tailWord_215762 prefixEnd_215762 65653103985475593411991 := by
  unfold tailWord_215762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1967371661084649515248385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5246324429559065373995693 1967371661084649515248385)
  ·
    refine ⟨1475528745813487136436289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1967371661084649515248385 1475528745813487136436289)
    ·
      refine ⟨1106646559360115352327217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1475528745813487136436289 1106646559360115352327217)
      ·
        refine ⟨829984919520086514245413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1106646559360115352327217 829984919520086514245413)
        ·
          refine ⟨155622172410016221421015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 829984919520086514245413 155622172410016221421015)
          ·
            refine ⟨233433258615024332131523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155622172410016221421015 233433258615024332131523)
            ·
              refine ⟨350149887922536498197285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233433258615024332131523 350149887922536498197285)
              ·
                refine ⟨65653103985475593411991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350149887922536498197285 65653103985475593411991)
                ·
                  rfl

theorem cell19_215762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_215762 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215762 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215762 prefixEnd_215762 := by exact prefixLift 215762
  have htrace : WordTrace (prefixWord ++ tailWord_215762) baseStart_215762 baseEnd_215762 := by
    simpa [prefixWord, tailWord_215762, baseEnd_215762] using wordTrace_append hprefix tailTrace_215762
  have hstable : (prefixWord ++ tailWord_215762).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215762).length < 2 ^ (prefixWord ++ tailWord_215762).sum := by decide
  have hdescent : baseEnd_215762 < baseStart_215762 := by decide
  rcases family_descends (prefixWord ++ tailWord_215762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215840 : List Nat := [2, 1, 1, 5, 1, 4, 2, 3]
def baseStart_215840 : Nat := 118140960795 + 215840 * 2 ^ 59
def prefixEnd_215840 : Nat := 4983230072969 + 3 ^ 40 * 215840 * 2
def baseEnd_215840 : Nat := 65676838202394523678445

theorem tailTrace_215840 : CollatzResearch.WordTrace tailWord_215840 prefixEnd_215840 65676838202394523678445 := by
  unfold tailWord_215840
  simp only [CollatzResearch.WordTrace]
  refine ⟨3936165769028008691166487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5248221025370678254888649 3936165769028008691166487)
  ·
    refine ⟨5904248653542013036749731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3936165769028008691166487 5904248653542013036749731)
    ·
      refine ⟨8856372980313019555124597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5904248653542013036749731 8856372980313019555124597)
      ·
        refine ⟨830284966904345583292931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8856372980313019555124597 830284966904345583292931)
        ·
          refine ⟨1245427450356518374939397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 830284966904345583292931 1245427450356518374939397)
          ·
            refine ⟨233517646941847195301137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1245427450356518374939397 233517646941847195301137)
            ·
              refine ⟨175138235206385396475853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233517646941847195301137 175138235206385396475853)
              ·
                refine ⟨65676838202394523678445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175138235206385396475853 65676838202394523678445)
                ·
                  rfl

theorem cell19_215840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_215840 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215840 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215840 prefixEnd_215840 := by exact prefixLift 215840
  have htrace : WordTrace (prefixWord ++ tailWord_215840) baseStart_215840 baseEnd_215840 := by
    simpa [prefixWord, tailWord_215840, baseEnd_215840] using wordTrace_append hprefix tailTrace_215840
  have hstable : (prefixWord ++ tailWord_215840).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215840).length < 2 ^ (prefixWord ++ tailWord_215840).sum := by decide
  have hdescent : baseEnd_215840 < baseStart_215840 := by decide
  rcases family_descends (prefixWord ++ tailWord_215840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215842 : List Nat := [3, 3, 1, 1, 2, 3, 1, 5]
def baseStart_215842 : Nat := 118140960795 + 215842 * 2 ^ 59
def prefixEnd_215842 : Nat := 4983230072969 + 3 ^ 40 * 215842 * 2
def baseEnd_215842 : Nat := 65677446772059111633995

theorem tailTrace_215842 : CollatzResearch.WordTrace tailWord_215842 prefixEnd_215842 65677446772059111633995 := by
  unfold tailWord_215842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1968101121012192930976445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5248269656032514482603853 1968101121012192930976445)
  ·
    refine ⟨738037920379572349116167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1968101121012192930976445 738037920379572349116167)
    ·
      refine ⟨1107056880569358523674251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 738037920379572349116167 1107056880569358523674251)
      ·
        refine ⟨1660585320854037785511377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107056880569358523674251 1660585320854037785511377)
        ·
          refine ⟨1245438990640528339133533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1660585320854037785511377 1245438990640528339133533)
          ·
            refine ⟨467039621490198127175075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1245438990640528339133533 467039621490198127175075)
            ·
              refine ⟨700559432235297190762613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467039621490198127175075 700559432235297190762613)
              ·
                refine ⟨65677446772059111633995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 700559432235297190762613 65677446772059111633995)
                ·
                  rfl

theorem cell19_215842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_215842 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215842 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215842 prefixEnd_215842 := by exact prefixLift 215842
  have htrace : WordTrace (prefixWord ++ tailWord_215842) baseStart_215842 baseEnd_215842 := by
    simpa [prefixWord, tailWord_215842, baseEnd_215842] using wordTrace_append hprefix tailTrace_215842
  have hstable : (prefixWord ++ tailWord_215842).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215842).length < 2 ^ (prefixWord ++ tailWord_215842).sum := by decide
  have hdescent : baseEnd_215842 < baseStart_215842 := by decide
  rcases family_descends (prefixWord ++ tailWord_215842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215861 : List Nat := [1, 3, 3, 1, 3, 3, 5]
def baseStart_215861 : Nat := 118140960795 + 215861 * 2 ^ 59
def prefixEnd_215861 : Nat := 4983230072969 + 3 ^ 40 * 215861 * 2
def baseEnd_215861 : Nat := 21894409394624232403907

theorem tailTrace_215861 : CollatzResearch.WordTrace tailWord_215861 prefixEnd_215861 21894409394624232403907 := by
  unfold tailWord_215861
  simp only [CollatzResearch.WordTrace]
  refine ⟨7873097470979937968847437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5248731647319958645898291 7873097470979937968847437)
  ·
    refine ⟨2952411551617476738317789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7873097470979937968847437 2952411551617476738317789)
    ·
      refine ⟨1107154331856553776869171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2952411551617476738317789 1107154331856553776869171)
      ·
        refine ⟨1660731497784830665303757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1107154331856553776869171 1660731497784830665303757)
        ·
          refine ⟨622774311669311499488909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1660731497784830665303757 622774311669311499488909)
          ·
            refine ⟨233540366875991812308341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 622774311669311499488909 233540366875991812308341)
            ·
              refine ⟨21894409394624232403907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 233540366875991812308341 21894409394624232403907)
              ·
                rfl

theorem cell19_215861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 3, 5].length) (baseStart_215861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215861 prefixEnd_215861 := by exact prefixLift 215861
  have htrace : WordTrace (prefixWord ++ tailWord_215861) baseStart_215861 baseEnd_215861 := by
    simpa [prefixWord, tailWord_215861, baseEnd_215861] using wordTrace_append hprefix tailTrace_215861
  have hstable : (prefixWord ++ tailWord_215861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215861).length < 2 ^ (prefixWord ++ tailWord_215861).sum := by decide
  have hdescent : baseEnd_215861 < baseStart_215861 := by decide
  rcases family_descends (prefixWord ++ tailWord_215861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215876 : List Nat := [2, 3, 4, 2, 1, 1, 2, 4]
def baseStart_215876 : Nat := 118140960795 + 215876 * 2 ^ 59
def prefixEnd_215876 : Nat := 4983230072969 + 3 ^ 40 * 215876 * 2
def baseEnd_215876 : Nat := 65687792456357106878347

theorem tailTrace_215876 : CollatzResearch.WordTrace tailWord_215876 prefixEnd_215876 65687792456357106878347 := by
  unfold tailWord_215876
  simp only [CollatzResearch.WordTrace]
  refine ⟨3936822282962797765321741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5249096377283730353762321 3936822282962797765321741)
  ·
    refine ⟨1476308356111049161995653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3936822282962797765321741 1476308356111049161995653)
    ·
      refine ⟨276807816770821717874185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1476308356111049161995653 276807816770821717874185)
      ·
        refine ⟨207605862578116288405639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 276807816770821717874185 207605862578116288405639)
        ·
          refine ⟨311408793867174432608459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207605862578116288405639 311408793867174432608459)
          ·
            refine ⟨467113190800761648912689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311408793867174432608459 467113190800761648912689)
            ·
              refine ⟨350334893100571236684517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 467113190800761648912689 350334893100571236684517)
              ·
                refine ⟨65687792456357106878347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350334893100571236684517 65687792456357106878347)
                ·
                  rfl

theorem cell19_215876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 2, 4].length) (baseStart_215876 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215876 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215876 prefixEnd_215876 := by exact prefixLift 215876
  have htrace : WordTrace (prefixWord ++ tailWord_215876) baseStart_215876 baseEnd_215876 := by
    simpa [prefixWord, tailWord_215876, baseEnd_215876] using wordTrace_append hprefix tailTrace_215876
  have hstable : (prefixWord ++ tailWord_215876).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215876).length < 2 ^ (prefixWord ++ tailWord_215876).sum := by decide
  have hdescent : baseEnd_215876 < baseStart_215876 := by decide
  rcases family_descends (prefixWord ++ tailWord_215876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215918 : List Nat := [4, 1, 2, 3, 2, 7]
def baseStart_215918 : Nat := 118140960795 + 215918 * 2 ^ 59
def prefixEnd_215918 : Nat := 4983230072969 + 3 ^ 40 * 215918 * 2
def baseEnd_215918 : Nat := 7300063602145939327211

theorem tailTrace_215918 : CollatzResearch.WordTrace tailWord_215918 prefixEnd_215918 7300063602145939327211 := by
  unfold tailWord_215918
  simp only [CollatzResearch.WordTrace]
  refine ⟨984397053971679587959051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5250117621182291135781605 984397053971679587959051)
  ·
    refine ⟨1476595580957519381938577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 984397053971679587959051 1476595580957519381938577)
    ·
      refine ⟨1107446685718139536453933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1476595580957519381938577 1107446685718139536453933)
      ·
        refine ⟨415292507144302326170225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1107446685718139536453933 415292507144302326170225)
        ·
          refine ⟨311469380358226744627669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415292507144302326170225 311469380358226744627669)
          ·
            refine ⟨7300063602145939327211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 311469380358226744627669 7300063602145939327211)
            ·
              rfl

theorem cell19_215918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 7].length) (baseStart_215918 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215918 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215918 prefixEnd_215918 := by exact prefixLift 215918
  have htrace : WordTrace (prefixWord ++ tailWord_215918) baseStart_215918 baseEnd_215918 := by
    simpa [prefixWord, tailWord_215918, baseEnd_215918] using wordTrace_append hprefix tailTrace_215918
  have hstable : (prefixWord ++ tailWord_215918).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215918).length < 2 ^ (prefixWord ++ tailWord_215918).sum := by decide
  have hdescent : baseEnd_215918 < baseStart_215918 := by decide
  rcases family_descends (prefixWord ++ tailWord_215918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_215975 : List Nat := [1, 1, 6, 1, 3, 1, 6]
def baseStart_215975 : Nat := 118140960795 + 215975 * 2 ^ 59
def prefixEnd_215975 : Nat := 4983230072969 + 3 ^ 40 * 215975 * 2
def baseEnd_215975 : Nat := 21905972218251403559359

theorem tailTrace_215975 : CollatzResearch.WordTrace tailWord_215975 prefixEnd_215975 21905972218251403559359 := by
  unfold tailWord_215975
  simp only [CollatzResearch.WordTrace]
  refine ⟨7877255392566935438497379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5251503595044623625664919 7877255392566935438497379)
  ·
    refine ⟨11815883088850403157746069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7877255392566935438497379 11815883088850403157746069)
    ·
      refine ⟨553869519789862648019347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11815883088850403157746069 553869519789862648019347)
      ·
        refine ⟨830804279684793972029021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 553869519789862648019347 830804279684793972029021)
        ·
          refine ⟨311551604881797739510883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 830804279684793972029021 311551604881797739510883)
          ·
            refine ⟨467327407322696609266325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 311551604881797739510883 467327407322696609266325)
            ·
              refine ⟨21905972218251403559359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 467327407322696609266325 21905972218251403559359)
              ·
                rfl

theorem cell19_215975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_215975 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_215975 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_215975 prefixEnd_215975 := by exact prefixLift 215975
  have htrace : WordTrace (prefixWord ++ tailWord_215975) baseStart_215975 baseEnd_215975 := by
    simpa [prefixWord, tailWord_215975, baseEnd_215975] using wordTrace_append hprefix tailTrace_215975
  have hstable : (prefixWord ++ tailWord_215975).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_215975).length < 2 ^ (prefixWord ++ tailWord_215975).sum := by decide
  have hdescent : baseEnd_215975 < baseStart_215975 := by decide
  rcases family_descends (prefixWord ++ tailWord_215975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216015 : List Nat := [1, 1, 2, 1, 1, 7, 1, 5]
def baseStart_216015 : Nat := 118140960795 + 216015 * 2 ^ 59
def prefixEnd_216015 : Nat := 4983230072969 + 3 ^ 40 * 216015 * 2
def baseEnd_216015 : Nat := 65730088048045969789079

theorem tailTrace_216015 : CollatzResearch.WordTrace tailWord_216015 prefixEnd_216015 65730088048045969789079 := by
  unfold tailWord_216015
  simp only [CollatzResearch.WordTrace]
  refine ⟨7878714312422022269953499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5252476208281348179968999 7878714312422022269953499)
  ·
    refine ⟨11818071468633033404930249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7878714312422022269953499 11818071468633033404930249)
    ·
      refine ⟨8863553601474775053697687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11818071468633033404930249 8863553601474775053697687)
      ·
        refine ⟨13295330402212162580546531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8863553601474775053697687 13295330402212162580546531)
        ·
          refine ⟨19942995603318243870819797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13295330402212162580546531 19942995603318243870819797)
          ·
            refine ⟨467413959452771340722339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19942995603318243870819797 467413959452771340722339)
            ·
              refine ⟨701120939179157011083509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 467413959452771340722339 701120939179157011083509)
              ·
                refine ⟨65730088048045969789079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 701120939179157011083509 65730088048045969789079)
                ·
                  rfl

theorem cell19_216015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_216015 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216015 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216015 prefixEnd_216015 := by exact prefixLift 216015
  have htrace : WordTrace (prefixWord ++ tailWord_216015) baseStart_216015 baseEnd_216015 := by
    simpa [prefixWord, tailWord_216015, baseEnd_216015] using wordTrace_append hprefix tailTrace_216015
  have hstable : (prefixWord ++ tailWord_216015).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216015).length < 2 ^ (prefixWord ++ tailWord_216015).sum := by decide
  have hdescent : baseEnd_216015 < baseStart_216015 := by decide
  rcases family_descends (prefixWord ++ tailWord_216015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216072 : List Nat := [2, 1, 3, 2, 1, 3, 2, 5]
def baseStart_216072 : Nat := 118140960795 + 216072 * 2 ^ 59
def prefixEnd_216072 : Nat := 4983230072969 + 3 ^ 40 * 216072 * 2
def baseEnd_216072 : Nat := 65747432283486726522257

theorem tailTrace_216072 : CollatzResearch.WordTrace tailWord_216072 prefixEnd_216072 65747432283486726522257 := by
  unfold tailWord_216072
  simp only [CollatzResearch.WordTrace]
  refine ⟨3940396636607760502389235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5253862182143680669852313 3940396636607760502389235)
  ·
    refine ⟨5910594954911640753583853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3940396636607760502389235 5910594954911640753583853)
    ·
      refine ⟨2216473108091865282593945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5910594954911640753583853 2216473108091865282593945)
      ·
        refine ⟨1662354831068898961945459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2216473108091865282593945 1662354831068898961945459)
        ·
          refine ⟨2493532246603348442918189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1662354831068898961945459 2493532246603348442918189)
          ·
            refine ⟨935074592476255666094321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2493532246603348442918189 935074592476255666094321)
            ·
              refine ⟨701305944357191749570741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 935074592476255666094321 701305944357191749570741)
              ·
                refine ⟨65747432283486726522257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 701305944357191749570741 65747432283486726522257)
                ·
                  rfl

theorem cell19_216072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_216072 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216072 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216072 prefixEnd_216072 := by exact prefixLift 216072
  have htrace : WordTrace (prefixWord ++ tailWord_216072) baseStart_216072 baseEnd_216072 := by
    simpa [prefixWord, tailWord_216072, baseEnd_216072] using wordTrace_append hprefix tailTrace_216072
  have hstable : (prefixWord ++ tailWord_216072).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216072).length < 2 ^ (prefixWord ++ tailWord_216072).sum := by decide
  have hdescent : baseEnd_216072 < baseStart_216072 := by decide
  rcases family_descends (prefixWord ++ tailWord_216072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216106 : List Nat := [3, 1, 4, 1, 3, 2, 1, 4]
def baseStart_216106 : Nat := 118140960795 + 216106 * 2 ^ 59
def prefixEnd_216106 : Nat := 4983230072969 + 3 ^ 40 * 216106 * 2
def baseEnd_216106 : Nat := 65757777967784721766609

theorem tailTrace_216106 : CollatzResearch.WordTrace tailWord_216106 prefixEnd_216106 65757777967784721766609 := by
  unfold tailWord_216106
  simp only [CollatzResearch.WordTrace]
  refine ⟨1970508338773086202879043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5254688903394896541010781 1970508338773086202879043)
  ·
    refine ⟨2955762508159629304318565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1970508338773086202879043 2955762508159629304318565)
    ·
      refine ⟨554205470279930494559731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2955762508159629304318565 554205470279930494559731)
      ·
        refine ⟨831308205419895741839597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554205470279930494559731 831308205419895741839597)
        ·
          refine ⟨311740577032460903189849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 831308205419895741839597 311740577032460903189849)
          ·
            refine ⟨233805432774345677392387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 311740577032460903189849 233805432774345677392387)
            ·
              refine ⟨350708149161518516088581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233805432774345677392387 350708149161518516088581)
              ·
                refine ⟨65757777967784721766609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350708149161518516088581 65757777967784721766609)
                ·
                  rfl

theorem cell19_216106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 2, 1, 4].length) (baseStart_216106 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216106 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216106 prefixEnd_216106 := by exact prefixLift 216106
  have htrace : WordTrace (prefixWord ++ tailWord_216106) baseStart_216106 baseEnd_216106 := by
    simpa [prefixWord, tailWord_216106, baseEnd_216106] using wordTrace_append hprefix tailTrace_216106
  have hstable : (prefixWord ++ tailWord_216106).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216106).length < 2 ^ (prefixWord ++ tailWord_216106).sum := by decide
  have hdescent : baseEnd_216106 < baseStart_216106 := by decide
  rcases family_descends (prefixWord ++ tailWord_216106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216222 : List Nat := [4, 3, 1, 1, 2, 1, 1, 6]
def baseStart_216222 : Nat := 118140960795 + 216222 * 2 ^ 59
def prefixEnd_216222 : Nat := 4983230072969 + 3 ^ 40 * 216222 * 2
def baseEnd_216222 : Nat := 65793075008330823188515

theorem tailTrace_216222 : CollatzResearch.WordTrace tailWord_216222 prefixEnd_216222 65793075008330823188515 := by
  unfold tailWord_216222
  simp only [CollatzResearch.WordTrace]
  refine ⟨985783027834012077842365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5257509481781397748492613 985783027834012077842365)
  ·
    refine ⟨369668635437754529190887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 985783027834012077842365 369668635437754529190887)
    ·
      refine ⟨554502953156631793786331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 369668635437754529190887 554502953156631793786331)
      ·
        refine ⟨831754429734947690679497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554502953156631793786331 831754429734947690679497)
        ·
          refine ⟨623815822301210768009623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 831754429734947690679497 623815822301210768009623)
          ·
            refine ⟨935723733451816152014435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 623815822301210768009623 935723733451816152014435)
            ·
              refine ⟨1403585600177724228021653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 935723733451816152014435 1403585600177724228021653)
              ·
                refine ⟨65793075008330823188515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1403585600177724228021653 65793075008330823188515)
                ·
                  rfl

theorem cell19_216222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_216222 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216222 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216222 prefixEnd_216222 := by exact prefixLift 216222
  have htrace : WordTrace (prefixWord ++ tailWord_216222) baseStart_216222 baseEnd_216222 := by
    simpa [prefixWord, tailWord_216222, baseEnd_216222] using wordTrace_append hprefix tailTrace_216222
  have hstable : (prefixWord ++ tailWord_216222).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216222).length < 2 ^ (prefixWord ++ tailWord_216222).sum := by decide
  have hdescent : baseEnd_216222 < baseStart_216222 := by decide
  rcases family_descends (prefixWord ++ tailWord_216222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216224 : List Nat := [2, 1, 1, 4, 2, 1, 4, 4]
def baseStart_216224 : Nat := 118140960795 + 216224 * 2 ^ 59
def prefixEnd_216224 : Nat := 4983230072969 + 3 ^ 40 * 216224 * 2
def baseEnd_216224 : Nat := 65793683577995411144065

theorem tailTrace_216224 : CollatzResearch.WordTrace tailWord_216224 prefixEnd_216224 65793683577995411144065 := by
  unfold tailWord_216224
  simp only [CollatzResearch.WordTrace]
  refine ⟨3943168584332425482155863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5257558112443233976207817 3943168584332425482155863)
  ·
    refine ⟨5914752876498638223233795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3943168584332425482155863 5914752876498638223233795)
    ·
      refine ⟨8872129314747957334850693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5914752876498638223233795 8872129314747957334850693)
      ·
        refine ⟨1663524246515242000284505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8872129314747957334850693 1663524246515242000284505)
        ·
          refine ⟨1247643184886431500213379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1663524246515242000284505 1247643184886431500213379)
          ·
            refine ⟨1871464777329647250320069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1247643184886431500213379 1871464777329647250320069)
            ·
              refine ⟨350899645749308859435013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1871464777329647250320069 350899645749308859435013)
              ·
                refine ⟨65793683577995411144065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 350899645749308859435013 65793683577995411144065)
                ·
                  rfl

theorem cell19_216224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_216224 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216224 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216224 prefixEnd_216224 := by exact prefixLift 216224
  have htrace : WordTrace (prefixWord ++ tailWord_216224) baseStart_216224 baseEnd_216224 := by
    simpa [prefixWord, tailWord_216224, baseEnd_216224] using wordTrace_append hprefix tailTrace_216224
  have hstable : (prefixWord ++ tailWord_216224).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216224).length < 2 ^ (prefixWord ++ tailWord_216224).sum := by decide
  have hdescent : baseEnd_216224 < baseStart_216224 := by decide
  rcases family_descends (prefixWord ++ tailWord_216224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216258 : List Nat := [3, 5, 1, 1, 2, 7]
def baseStart_216258 : Nat := 118140960795 + 216258 * 2 ^ 59
def prefixEnd_216258 : Nat := 4983230072969 + 3 ^ 40 * 216258 * 2
def baseEnd_216258 : Nat := 7311558806921489598713

theorem tailTrace_216258 : CollatzResearch.WordTrace tailWord_216258 prefixEnd_216258 7311558806921489598713 := by
  unfold tailWord_216258
  simp only [CollatzResearch.WordTrace]
  refine ⟨1971894312635418692762357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5258384833694449847366285 1971894312635418692762357)
  ·
    refine ⟨184865091809570502446471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1971894312635418692762357 184865091809570502446471)
    ·
      refine ⟨277297637714355753669707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 184865091809570502446471 277297637714355753669707)
      ·
        refine ⟨415946456571533630504561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277297637714355753669707 415946456571533630504561)
        ·
          refine ⟨311959842428650222878421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 415946456571533630504561 311959842428650222878421)
          ·
            refine ⟨7311558806921489598713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 311959842428650222878421 7311558806921489598713)
            ·
              rfl

theorem cell19_216258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 7].length) (baseStart_216258 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216258 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216258 prefixEnd_216258 := by exact prefixLift 216258
  have htrace : WordTrace (prefixWord ++ tailWord_216258) baseStart_216258 baseEnd_216258 := by
    simpa [prefixWord, tailWord_216258, baseEnd_216258] using wordTrace_append hprefix tailTrace_216258
  have hstable : (prefixWord ++ tailWord_216258).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216258).length < 2 ^ (prefixWord ++ tailWord_216258).sum := by decide
  have hdescent : baseEnd_216258 < baseStart_216258 := by decide
  rcases family_descends (prefixWord ++ tailWord_216258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216260 : List Nat := [2, 3, 3, 1, 4, 6]
def baseStart_216260 : Nat := 118140960795 + 216260 * 2 ^ 59
def prefixEnd_216260 : Nat := 4983230072969 + 3 ^ 40 * 216260 * 2
def baseEnd_216260 : Nat := 7311626425773110482663

theorem tailTrace_216260 : CollatzResearch.WordTrace tailWord_216260 prefixEnd_216260 7311626425773110482663 := by
  unfold tailWord_216260
  simp only [CollatzResearch.WordTrace]
  refine ⟨3943825098267214556311117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5258433464356286075081489 3943825098267214556311117)
  ·
    refine ⟨1478934411850205458616669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3943825098267214556311117 1478934411850205458616669)
    ·
      refine ⟨554600404443827046981251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1478934411850205458616669 554600404443827046981251)
      ·
        refine ⟨831900606665740570471877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 554600404443827046981251 831900606665740570471877)
        ·
          refine ⟨155981363749826356963477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 831900606665740570471877 155981363749826356963477)
          ·
            refine ⟨7311626425773110482663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155981363749826356963477 7311626425773110482663)
            ·
              rfl

theorem cell19_216260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 4, 6].length) (baseStart_216260 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216260 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216260 prefixEnd_216260 := by exact prefixLift 216260
  have htrace : WordTrace (prefixWord ++ tailWord_216260) baseStart_216260 baseEnd_216260 := by
    simpa [prefixWord, tailWord_216260, baseEnd_216260] using wordTrace_append hprefix tailTrace_216260
  have hstable : (prefixWord ++ tailWord_216260).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216260).length < 2 ^ (prefixWord ++ tailWord_216260).sum := by decide
  have hdescent : baseEnd_216260 < baseStart_216260 := by decide
  rcases family_descends (prefixWord ++ tailWord_216260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216298 : List Nat := [3, 1, 3, 1, 1, 4, 3, 3]
def baseStart_216298 : Nat := 118140960795 + 216298 * 2 ^ 59
def prefixEnd_216298 : Nat := 4983230072969 + 3 ^ 40 * 216298 * 2
def baseEnd_216298 : Nat := 65816200655585165499419

theorem tailTrace_216298 : CollatzResearch.WordTrace tailWord_216298 prefixEnd_216298 65816200655585165499419 := by
  unfold tailWord_216298
  simp only [CollatzResearch.WordTrace]
  refine ⟨1972259042599190400626387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5259357446931174401670365 1972259042599190400626387)
  ·
    refine ⟨2958388563898785600939581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1972259042599190400626387 2958388563898785600939581)
    ·
      refine ⟨1109395711462044600352343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2958388563898785600939581 1109395711462044600352343)
      ·
        refine ⟨1664093567193066900528515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1109395711462044600352343 1664093567193066900528515)
        ·
          refine ⟨2496140350789600350792773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1664093567193066900528515 2496140350789600350792773)
          ·
            refine ⟨468026315773050065773645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2496140350789600350792773 468026315773050065773645)
            ·
              refine ⟨175509868414893774665117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 468026315773050065773645 175509868414893774665117)
              ·
                refine ⟨65816200655585165499419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175509868414893774665117 65816200655585165499419)
                ·
                  rfl

theorem cell19_216298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 3, 3].length) (baseStart_216298 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216298 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216298 prefixEnd_216298 := by exact prefixLift 216298
  have htrace : WordTrace (prefixWord ++ tailWord_216298) baseStart_216298 baseEnd_216298 := by
    simpa [prefixWord, tailWord_216298, baseEnd_216298] using wordTrace_append hprefix tailTrace_216298
  have hstable : (prefixWord ++ tailWord_216298).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216298).length < 2 ^ (prefixWord ++ tailWord_216298).sum := by decide
  have hdescent : baseEnd_216298 < baseStart_216298 := by decide
  rcases family_descends (prefixWord ++ tailWord_216298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216355 : List Nat := [1, 1, 1, 4, 2, 5, 2, 3]
def baseStart_216355 : Nat := 118140960795 + 216355 * 2 ^ 59
def prefixEnd_216355 : Nat := 4983230072969 + 3 ^ 40 * 216355 * 2
def baseEnd_216355 : Nat := 65833544891025922232597

theorem tailTrace_216355 : CollatzResearch.WordTrace tailWord_216355 prefixEnd_216355 65833544891025922232597 := by
  unfold tailWord_216355
  simp only [CollatzResearch.WordTrace]
  refine ⟨7891115131190260337330519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5260743420793506891553679 7891115131190260337330519)
  ·
    refine ⟨11836672696785390505995779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7891115131190260337330519 11836672696785390505995779)
    ·
      refine ⟨17755009045178085758993669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11836672696785390505995779 17755009045178085758993669)
      ·
        refine ⟨3329064195970891079811313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17755009045178085758993669 3329064195970891079811313)
        ·
          refine ⟨2496798146978168309858485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3329064195970891079811313 2496798146978168309858485)
          ·
            refine ⟨234074826279203279049233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2496798146978168309858485 234074826279203279049233)
            ·
              refine ⟨175556119709402459286925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234074826279203279049233 175556119709402459286925)
              ·
                refine ⟨65833544891025922232597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175556119709402459286925 65833544891025922232597)
                ·
                  rfl

theorem cell19_216355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 2, 3].length) (baseStart_216355 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216355 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216355 prefixEnd_216355 := by exact prefixLift 216355
  have htrace : WordTrace (prefixWord ++ tailWord_216355) baseStart_216355 baseEnd_216355 := by
    simpa [prefixWord, tailWord_216355, baseEnd_216355] using wordTrace_append hprefix tailTrace_216355
  have hstable : (prefixWord ++ tailWord_216355).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216355).length < 2 ^ (prefixWord ++ tailWord_216355).sum := by decide
  have hdescent : baseEnd_216355 < baseStart_216355 := by decide
  rcases family_descends (prefixWord ++ tailWord_216355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216357 : List Nat := [1, 3, 1, 2, 4, 2, 1, 5]
def baseStart_216357 : Nat := 118140960795 + 216357 * 2 ^ 59
def prefixEnd_216357 : Nat := 4983230072969 + 3 ^ 40 * 216357 * 2
def baseEnd_216357 : Nat := 65834153460690510188147

theorem tailTrace_216357 : CollatzResearch.WordTrace tailWord_216357 prefixEnd_216357 65834153460690510188147 := by
  unfold tailWord_216357
  simp only [CollatzResearch.WordTrace]
  refine ⟨7891188077183014678903325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5260792051455343119268883 7891188077183014678903325)
  ·
    refine ⟨2959195528943630504588747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7891188077183014678903325 2959195528943630504588747)
    ·
      refine ⟨4438793293415445756883121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2959195528943630504588747 4438793293415445756883121)
      ·
        refine ⟨3329094970061584317662341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4438793293415445756883121 3329094970061584317662341)
        ·
          refine ⟨624205306886547059561689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3329094970061584317662341 624205306886547059561689)
          ·
            refine ⟨468153980164910294671267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 624205306886547059561689 468153980164910294671267)
            ·
              refine ⟨702230970247365442006901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 468153980164910294671267 702230970247365442006901)
              ·
                refine ⟨65834153460690510188147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 702230970247365442006901 65834153460690510188147)
                ·
                  rfl

theorem cell19_216357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_216357 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216357 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216357 prefixEnd_216357 := by exact prefixLift 216357
  have htrace : WordTrace (prefixWord ++ tailWord_216357) baseStart_216357 baseEnd_216357 := by
    simpa [prefixWord, tailWord_216357, baseEnd_216357] using wordTrace_append hprefix tailTrace_216357
  have hstable : (prefixWord ++ tailWord_216357).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216357).length < 2 ^ (prefixWord ++ tailWord_216357).sum := by decide
  have hdescent : baseEnd_216357 < baseStart_216357 := by decide
  rcases family_descends (prefixWord ++ tailWord_216357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216446 : List Nat := [4, 2, 3, 2, 1, 2, 1, 4]
def baseStart_216446 : Nat := 118140960795 + 216446 * 2 ^ 59
def prefixEnd_216446 : Nat := 4983230072969 + 3 ^ 40 * 216446 * 2
def baseEnd_216446 : Nat := 65861234810764674210127

theorem tailTrace_216446 : CollatzResearch.WordTrace tailWord_216446 prefixEnd_216446 65861234810764674210127 := by
  unfold tailWord_216446
  simp only [CollatzResearch.WordTrace]
  refine ⟨986804271732572859861649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5262956115907055252595461 986804271732572859861649)
  ·
    refine ⟨740103203799429644896237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 986804271732572859861649 740103203799429644896237)
    ·
      refine ⟨277538701424786116836089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 740103203799429644896237 277538701424786116836089)
      ·
        refine ⟨208154026068589587627067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 277538701424786116836089 208154026068589587627067)
        ·
          refine ⟨312231039102884381440601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208154026068589587627067 312231039102884381440601)
          ·
            refine ⟨234173279327163286080451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 312231039102884381440601 234173279327163286080451)
            ·
              refine ⟨351259918990744929120677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234173279327163286080451 351259918990744929120677)
              ·
                refine ⟨65861234810764674210127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 351259918990744929120677 65861234810764674210127)
                ·
                  rfl

theorem cell19_216446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_216446 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216446 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216446 prefixEnd_216446 := by exact prefixLift 216446
  have htrace : WordTrace (prefixWord ++ tailWord_216446) baseStart_216446 baseEnd_216446 := by
    simpa [prefixWord, tailWord_216446, baseEnd_216446] using wordTrace_append hprefix tailTrace_216446
  have hstable : (prefixWord ++ tailWord_216446).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216446).length < 2 ^ (prefixWord ++ tailWord_216446).sum := by decide
  have hdescent : baseEnd_216446 < baseStart_216446 := by decide
  rcases family_descends (prefixWord ++ tailWord_216446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216452 : List Nat := [2, 3, 2, 1, 1, 3, 3, 4]
def baseStart_216452 : Nat := 118140960795 + 216452 * 2 ^ 59
def prefixEnd_216452 : Nat := 4983230072969 + 3 ^ 40 * 216452 * 2
def baseEnd_216452 : Nat := 65863060519758438076777

theorem tailTrace_216452 : CollatzResearch.WordTrace tailWord_216452 prefixEnd_216452 65863060519758438076777 := by
  unfold tailWord_216452
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947326505919422951805805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5263102007892563935741073 3947326505919422951805805)
  ·
    refine ⟨1480247439719783606927177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3947326505919422951805805 1480247439719783606927177)
    ·
      refine ⟨1110185579789837705195383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1480247439719783606927177 1110185579789837705195383)
      ·
        refine ⟨1665278369684756557793075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110185579789837705195383 1665278369684756557793075)
        ·
          refine ⟨2497917554527134836689613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1665278369684756557793075 2497917554527134836689613)
          ·
            refine ⟨936719082947675563758605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2497917554527134836689613 936719082947675563758605)
            ·
              refine ⟨351269656105378336409477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 936719082947675563758605 351269656105378336409477)
              ·
                refine ⟨65863060519758438076777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 351269656105378336409477 65863060519758438076777)
                ·
                  rfl

theorem cell19_216452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_216452 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216452 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216452 prefixEnd_216452 := by exact prefixLift 216452
  have htrace : WordTrace (prefixWord ++ tailWord_216452) baseStart_216452 baseEnd_216452 := by
    simpa [prefixWord, tailWord_216452, baseEnd_216452] using wordTrace_append hprefix tailTrace_216452
  have hstable : (prefixWord ++ tailWord_216452).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216452).length < 2 ^ (prefixWord ++ tailWord_216452).sum := by decide
  have hdescent : baseEnd_216452 < baseStart_216452 := by decide
  rcases family_descends (prefixWord ++ tailWord_216452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216488 : List Nat := [2, 1, 6, 1, 2, 1, 6]
def baseStart_216488 : Nat := 118140960795 + 216488 * 2 ^ 59
def prefixEnd_216488 : Nat := 4983230072969 + 3 ^ 40 * 216488 * 2
def baseEnd_216488 : Nat := 21958004924573673758893

theorem tailTrace_216488 : CollatzResearch.WordTrace tailWord_216488 prefixEnd_216488 21958004924573673758893 := by
  unfold tailWord_216488
  simp only [CollatzResearch.WordTrace]
  refine ⟨3947983019854212025961059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5263977359805616034614745 3947983019854212025961059)
  ·
    refine ⟨5921974529781318038941589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3947983019854212025961059 5921974529781318038941589)
    ·
      refine ⟨277592556083499283075387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5921974529781318038941589 277592556083499283075387)
      ·
        refine ⟨416388834125248924613081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 277592556083499283075387 416388834125248924613081)
        ·
          refine ⟨312291625593936693459811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 416388834125248924613081 312291625593936693459811)
          ·
            refine ⟨468437438390905040189717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312291625593936693459811 468437438390905040189717)
            ·
              refine ⟨21958004924573673758893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 468437438390905040189717 21958004924573673758893)
              ·
                rfl

theorem cell19_216488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_216488 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216488 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216488 prefixEnd_216488 := by exact prefixLift 216488
  have htrace : WordTrace (prefixWord ++ tailWord_216488) baseStart_216488 baseEnd_216488 := by
    simpa [prefixWord, tailWord_216488, baseEnd_216488] using wordTrace_append hprefix tailTrace_216488
  have hstable : (prefixWord ++ tailWord_216488).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216488).length < 2 ^ (prefixWord ++ tailWord_216488).sum := by decide
  have hdescent : baseEnd_216488 < baseStart_216488 := by decide
  rcases family_descends (prefixWord ++ tailWord_216488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216547 : List Nat := [1, 1, 1, 6, 2, 3, 5]
def baseStart_216547 : Nat := 118140960795 + 216547 * 2 ^ 59
def prefixEnd_216547 : Nat := 4983230072969 + 3 ^ 40 * 216547 * 2
def baseEnd_216547 : Nat := 21963989192942121988469

theorem tailTrace_216547 : CollatzResearch.WordTrace tailWord_216547 prefixEnd_216547 21963989192942121988469 := by
  unfold tailWord_216547
  simp only [CollatzResearch.WordTrace]
  refine ⟨7898117946494677128319895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5265411964329784752213263 7898117946494677128319895)
  ·
    refine ⟨11847176919742015692479843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7898117946494677128319895 11847176919742015692479843)
    ·
      refine ⟨17770765379613023538719765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11847176919742015692479843 17770765379613023538719765)
      ·
        refine ⟨833004627169360478377489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 17770765379613023538719765 833004627169360478377489)
        ·
          refine ⟨624753470377020358783117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 833004627169360478377489 624753470377020358783117)
          ·
            refine ⟨234282551391382634543669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 624753470377020358783117 234282551391382634543669)
            ·
              refine ⟨21963989192942121988469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 234282551391382634543669 21963989192942121988469)
              ·
                rfl

theorem cell19_216547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 5].length) (baseStart_216547 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216547 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216547 prefixEnd_216547 := by exact prefixLift 216547
  have htrace : WordTrace (prefixWord ++ tailWord_216547) baseStart_216547 baseEnd_216547 := by
    simpa [prefixWord, tailWord_216547, baseEnd_216547] using wordTrace_append hprefix tailTrace_216547
  have hstable : (prefixWord ++ tailWord_216547).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216547).length < 2 ^ (prefixWord ++ tailWord_216547).sum := by decide
  have hdescent : baseEnd_216547 < baseStart_216547 := by decide
  rcases family_descends (prefixWord ++ tailWord_216547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216566 : List Nat := [5, 1, 1, 1, 2, 2, 1, 6]
def baseStart_216566 : Nat := 118140960795 + 216566 * 2 ^ 59
def prefixEnd_216566 : Nat := 4983230072969 + 3 ^ 40 * 216566 * 2
def baseEnd_216566 : Nat := 65897748990639951543133

theorem tailTrace_216566 : CollatzResearch.WordTrace tailWord_216566 prefixEnd_216566 65897748990639951543133 := by
  unfold tailWord_216566
  simp only [CollatzResearch.WordTrace]
  refine ⟨493675683339115210828847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5265873955617228915507701 493675683339115210828847)
  ·
    refine ⟨740513525008672816243271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 493675683339115210828847 740513525008672816243271)
    ·
      refine ⟨1110770287513009224364907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 740513525008672816243271 1110770287513009224364907)
      ·
        refine ⟨1666155431269513836547361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1110770287513009224364907 1666155431269513836547361)
        ·
          refine ⟨1249616573452135377410521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1666155431269513836547361 1249616573452135377410521)
          ·
            refine ⟨937212430089101533057891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1249616573452135377410521 937212430089101533057891)
            ·
              refine ⟨1405818645133652299586837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937212430089101533057891 1405818645133652299586837)
              ·
                refine ⟨65897748990639951543133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1405818645133652299586837 65897748990639951543133)
                ·
                  rfl

theorem cell19_216566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_216566 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216566 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216566 prefixEnd_216566 := by exact prefixLift 216566
  have htrace : WordTrace (prefixWord ++ tailWord_216566) baseStart_216566 baseEnd_216566 := by
    simpa [prefixWord, tailWord_216566, baseEnd_216566] using wordTrace_append hprefix tailTrace_216566
  have hstable : (prefixWord ++ tailWord_216566).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216566).length < 2 ^ (prefixWord ++ tailWord_216566).sum := by decide
  have hdescent : baseEnd_216566 < baseStart_216566 := by decide
  rcases family_descends (prefixWord ++ tailWord_216566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216568 : List Nat := [2, 1, 2, 1, 1, 5, 1, 6]
def baseStart_216568 : Nat := 118140960795 + 216568 * 2 ^ 59
def prefixEnd_216568 : Nat := 4983230072969 + 3 ^ 40 * 216568 * 2
def baseEnd_216568 : Nat := 65898357560304539498683

theorem tailTrace_216568 : CollatzResearch.WordTrace tailWord_216568 prefixEnd_216568 65898357560304539498683 := by
  unfold tailWord_216568
  simp only [CollatzResearch.WordTrace]
  refine ⟨3949441939709298857417179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5265922586279065143222905 3949441939709298857417179)
  ·
    refine ⟨5924162909563948286125769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3949441939709298857417179 5924162909563948286125769)
    ·
      refine ⟨4443122182172961214594327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5924162909563948286125769 4443122182172961214594327)
      ·
        refine ⟨6664683273259441821891491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4443122182172961214594327 6664683273259441821891491)
        ·
          refine ⟨9997024909889162732837237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6664683273259441821891491 9997024909889162732837237)
          ·
            refine ⟨937221085302109006203491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9997024909889162732837237 937221085302109006203491)
            ·
              refine ⟨1405831627953163509305237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 937221085302109006203491 1405831627953163509305237)
              ·
                refine ⟨65898357560304539498683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1405831627953163509305237 65898357560304539498683)
                ·
                  rfl

theorem cell19_216568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_216568 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216568 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216568 prefixEnd_216568 := by exact prefixLift 216568
  have htrace : WordTrace (prefixWord ++ tailWord_216568) baseStart_216568 baseEnd_216568 := by
    simpa [prefixWord, tailWord_216568, baseEnd_216568] using wordTrace_append hprefix tailTrace_216568
  have hstable : (prefixWord ++ tailWord_216568).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216568).length < 2 ^ (prefixWord ++ tailWord_216568).sum := by decide
  have hdescent : baseEnd_216568 < baseStart_216568 := by decide
  rcases family_descends (prefixWord ++ tailWord_216568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216663 : List Nat := [1, 1, 3, 2, 2, 4, 6]
def baseStart_216663 : Nat := 118140960795 + 216663 * 2 ^ 59
def prefixEnd_216663 : Nat := 4983230072969 + 3 ^ 40 * 216663 * 2
def baseEnd_216663 : Nat := 21975754873124155795771

theorem tailTrace_216663 : CollatzResearch.WordTrace tailWord_216663 prefixEnd_216663 21975754873124155795771 := by
  unfold tailWord_216663
  simp only [CollatzResearch.WordTrace]
  refine ⟨7902348814074428939542643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5268232542716285959695095 7902348814074428939542643)
  ·
    refine ⟨11853523221111643409313965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7902348814074428939542643 11853523221111643409313965)
    ·
      refine ⟨4445071207916866278492737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11853523221111643409313965 4445071207916866278492737)
      ·
        refine ⟨3333803405937649708869553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4445071207916866278492737 3333803405937649708869553)
        ·
          refine ⟨2500352554453237281652165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3333803405937649708869553 2500352554453237281652165)
          ·
            refine ⟨468816103959981990309781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2500352554453237281652165 468816103959981990309781)
            ·
              refine ⟨21975754873124155795771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 468816103959981990309781 21975754873124155795771)
              ·
                rfl

theorem cell19_216663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_216663 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216663 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216663 prefixEnd_216663 := by exact prefixLift 216663
  have htrace : WordTrace (prefixWord ++ tailWord_216663) baseStart_216663 baseEnd_216663 := by
    simpa [prefixWord, tailWord_216663, baseEnd_216663] using wordTrace_append hprefix tailTrace_216663
  have hstable : (prefixWord ++ tailWord_216663).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216663).length < 2 ^ (prefixWord ++ tailWord_216663).sum := by decide
  have hdescent : baseEnd_216663 < baseStart_216663 := by decide
  rcases family_descends (prefixWord ++ tailWord_216663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216718 : List Nat := [4, 1, 1, 3, 1, 4, 5]
def baseStart_216718 : Nat := 118140960795 + 216718 * 2 ^ 59
def prefixEnd_216718 : Nat := 4983230072969 + 3 ^ 40 * 216718 * 2
def baseEnd_216718 : Nat := 21981333428382878721647

theorem tailTrace_216718 : CollatzResearch.WordTrace tailWord_216718 prefixEnd_216718 21981333428382878721647 := by
  unfold tailWord_216718
  simp only [CollatzResearch.WordTrace]
  refine ⟨988044353609396666599351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5269569885916782221863205 988044353609396666599351)
  ·
    refine ⟨1482066530414094999899027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 988044353609396666599351 1482066530414094999899027)
    ·
      refine ⟨2223099795621142499848541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1482066530414094999899027 2223099795621142499848541)
      ·
        refine ⟨833662423357928437443203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2223099795621142499848541 833662423357928437443203)
        ·
          refine ⟨1250493635036892656164805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 833662423357928437443203 1250493635036892656164805)
          ·
            refine ⟨234467556569417373030901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1250493635036892656164805 234467556569417373030901)
            ·
              refine ⟨21981333428382878721647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 234467556569417373030901 21981333428382878721647)
              ·
                rfl

theorem cell19_216718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 5].length) (baseStart_216718 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216718 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216718 prefixEnd_216718 := by exact prefixLift 216718
  have htrace : WordTrace (prefixWord ++ tailWord_216718) baseStart_216718 baseEnd_216718 := by
    simpa [prefixWord, tailWord_216718, baseEnd_216718] using wordTrace_append hprefix tailTrace_216718
  have hstable : (prefixWord ++ tailWord_216718).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216718).length < 2 ^ (prefixWord ++ tailWord_216718).sum := by decide
  have hdescent : baseEnd_216718 < baseStart_216718 := by decide
  rcases family_descends (prefixWord ++ tailWord_216718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216735 : List Nat := [1, 1, 2, 7, 1, 1, 2, 4]
def baseStart_216735 : Nat := 118140960795 + 216735 * 2 ^ 59
def prefixEnd_216735 : Nat := 4983230072969 + 3 ^ 40 * 216735 * 2
def baseEnd_216735 : Nat := 65949173127297633787117

theorem tailTrace_216735 : CollatzResearch.WordTrace tailWord_216735 prefixEnd_216735 65949173127297633787117 := by
  unfold tailWord_216735
  simp only [CollatzResearch.WordTrace]
  refine ⟨7904974869813585236163659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5269983246542390157442439 7904974869813585236163659)
  ·
    refine ⟨11857462304720377854245489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7904974869813585236163659 11857462304720377854245489)
    ·
      refine ⟨8893096728540283390684117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11857462304720377854245489 8893096728540283390684117)
      ·
        refine ⟨208431954575162891969159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 8893096728540283390684117 208431954575162891969159)
        ·
          refine ⟨312647931862744337953739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208431954575162891969159 312647931862744337953739)
          ·
            refine ⟨468971897794116506930609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312647931862744337953739 468971897794116506930609)
            ·
              refine ⟨351728923345587380197957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468971897794116506930609 351728923345587380197957)
              ·
                refine ⟨65949173127297633787117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 351728923345587380197957 65949173127297633787117)
                ·
                  rfl

theorem cell19_216735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 2, 4].length) (baseStart_216735 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216735 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216735 prefixEnd_216735 := by exact prefixLift 216735
  have htrace : WordTrace (prefixWord ++ tailWord_216735) baseStart_216735 baseEnd_216735 := by
    simpa [prefixWord, tailWord_216735, baseEnd_216735] using wordTrace_append hprefix tailTrace_216735
  have hstable : (prefixWord ++ tailWord_216735).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216735).length < 2 ^ (prefixWord ++ tailWord_216735).sum := by decide
  have hdescent : baseEnd_216735 < baseStart_216735 := by decide
  rcases family_descends (prefixWord ++ tailWord_216735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216737 : List Nat := [1, 2, 3, 3, 2, 2, 2, 4]
def baseStart_216737 : Nat := 118140960795 + 216737 * 2 ^ 59
def prefixEnd_216737 : Nat := 4983230072969 + 3 ^ 40 * 216737 * 2
def baseEnd_216737 : Nat := 65949781696962221742667

theorem tailTrace_216737 : CollatzResearch.WordTrace tailWord_216737 prefixEnd_216737 65949781696962221742667 := by
  unfold tailWord_216737
  simp only [CollatzResearch.WordTrace]
  refine ⟨7905047815806339577736465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5270031877204226385157643 7905047815806339577736465)
  ·
    refine ⟨5928785861854754683302349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7905047815806339577736465 5928785861854754683302349)
    ·
      refine ⟨2223294698195533006238381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5928785861854754683302349 2223294698195533006238381)
      ·
        refine ⟨833735511823324877339393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2223294698195533006238381 833735511823324877339393)
        ·
          refine ⟨625301633867493658004545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 833735511823324877339393 625301633867493658004545)
          ·
            refine ⟨468976225400620243503409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 625301633867493658004545 468976225400620243503409)
            ·
              refine ⟨351732169050465182627557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 468976225400620243503409 351732169050465182627557)
              ·
                refine ⟨65949781696962221742667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 351732169050465182627557 65949781696962221742667)
                ·
                  rfl

theorem cell19_216737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 4].length) (baseStart_216737 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216737 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216737 prefixEnd_216737 := by exact prefixLift 216737
  have htrace : WordTrace (prefixWord ++ tailWord_216737) baseStart_216737 baseEnd_216737 := by
    simpa [prefixWord, tailWord_216737, baseEnd_216737] using wordTrace_append hprefix tailTrace_216737
  have hstable : (prefixWord ++ tailWord_216737).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216737).length < 2 ^ (prefixWord ++ tailWord_216737).sum := by decide
  have hdescent : baseEnd_216737 < baseStart_216737 := by decide
  rcases family_descends (prefixWord ++ tailWord_216737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216739 : List Nat := [1, 1, 1, 4, 1, 1, 6, 4]
def baseStart_216739 : Nat := 118140960795 + 216739 * 2 ^ 59
def prefixEnd_216739 : Nat := 4983230072969 + 3 ^ 40 * 216739 * 2
def baseEnd_216739 : Nat := 65950390266626809698217

theorem tailTrace_216739 : CollatzResearch.WordTrace tailWord_216739 prefixEnd_216739 65950390266626809698217 := by
  unfold tailWord_216739
  simp only [CollatzResearch.WordTrace]
  refine ⟨7905120761799093919309271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5270080507866062612872847 7905120761799093919309271)
  ·
    refine ⟨11857681142698640878963907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7905120761799093919309271 11857681142698640878963907)
    ·
      refine ⟨17786521714047961318445861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11857681142698640878963907 17786521714047961318445861)
      ·
        refine ⟨3334972821383992747208599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17786521714047961318445861 3334972821383992747208599)
        ·
          refine ⟨5002459232075989120812899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3334972821383992747208599 5002459232075989120812899)
          ·
            refine ⟨7503688848113983681219349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5002459232075989120812899 7503688848113983681219349)
            ·
              refine ⟨351735414755342985057157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7503688848113983681219349 351735414755342985057157)
              ·
                refine ⟨65950390266626809698217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 351735414755342985057157 65950390266626809698217)
                ·
                  rfl

theorem cell19_216739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_216739 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216739 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216739 prefixEnd_216739 := by exact prefixLift 216739
  have htrace : WordTrace (prefixWord ++ tailWord_216739) baseStart_216739 baseEnd_216739 := by
    simpa [prefixWord, tailWord_216739, baseEnd_216739] using wordTrace_append hprefix tailTrace_216739
  have hstable : (prefixWord ++ tailWord_216739).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216739).length < 2 ^ (prefixWord ++ tailWord_216739).sum := by decide
  have hdescent : baseEnd_216739 < baseStart_216739 := by decide
  rcases family_descends (prefixWord ++ tailWord_216739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216794 : List Nat := [3, 1, 1, 2, 2, 5, 1, 4]
def baseStart_216794 : Nat := 118140960795 + 216794 * 2 ^ 59
def prefixEnd_216794 : Nat := 4983230072969 + 3 ^ 40 * 216794 * 2
def baseEnd_216794 : Nat := 65967125932402978475845

theorem tailTrace_216794 : CollatzResearch.WordTrace tailWord_216794 prefixEnd_216794 65967125932402978475845 := by
  unfold tailWord_216794
  simp only [CollatzResearch.WordTrace]
  refine ⟨1976781694149959578140359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5271417851066558875040957 1976781694149959578140359)
  ·
    refine ⟨2965172541224939367210539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1976781694149959578140359 2965172541224939367210539)
    ·
      refine ⟨4447758811837409050815809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2965172541224939367210539 4447758811837409050815809)
      ·
        refine ⟨3335819108878056788111857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4447758811837409050815809 3335819108878056788111857)
        ·
          refine ⟨2501864331658542591083893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3335819108878056788111857 2501864331658542591083893)
          ·
            refine ⟨234549781092988367914115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2501864331658542591083893 234549781092988367914115)
            ·
              refine ⟨351824671639482551871173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234549781092988367914115 351824671639482551871173)
              ·
                refine ⟨65967125932402978475845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 351824671639482551871173 65967125932402978475845)
                ·
                  rfl

theorem cell19_216794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_216794 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216794 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216794 prefixEnd_216794 := by exact prefixLift 216794
  have htrace : WordTrace (prefixWord ++ tailWord_216794) baseStart_216794 baseEnd_216794 := by
    simpa [prefixWord, tailWord_216794, baseEnd_216794] using wordTrace_append hprefix tailTrace_216794
  have hstable : (prefixWord ++ tailWord_216794).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216794).length < 2 ^ (prefixWord ++ tailWord_216794).sum := by decide
  have hdescent : baseEnd_216794 < baseStart_216794 := by decide
  rcases family_descends (prefixWord ++ tailWord_216794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216862 : List Nat := [4, 3, 2, 2, 2, 1, 2, 3]
def baseStart_216862 : Nat := 118140960795 + 216862 * 2 ^ 59
def prefixEnd_216862 : Nat := 4983230072969 + 3 ^ 40 * 216862 * 2
def baseEnd_216862 : Nat := 65987817300998968964549

theorem tailTrace_216862 : CollatzResearch.WordTrace tailWord_216862 prefixEnd_216862 65987817300998968964549 := by
  unfold tailWord_216862
  simp only [CollatzResearch.WordTrace]
  refine ⟨988700867544185740754605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5273071293568990617357893 988700867544185740754605)
  ·
    refine ⟨370762825329069652782977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 988700867544185740754605 370762825329069652782977)
    ·
      refine ⟨278072118996802239587233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 370762825329069652782977 278072118996802239587233)
      ·
        refine ⟨208554089247601679690425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 278072118996802239587233 208554089247601679690425)
        ·
          refine ⟨156415566935701259767819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208554089247601679690425 156415566935701259767819)
          ·
            refine ⟨234623350403551889651729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156415566935701259767819 234623350403551889651729)
            ·
              refine ⟨175967512802663917238797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234623350403551889651729 175967512802663917238797)
              ·
                refine ⟨65987817300998968964549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175967512802663917238797 65987817300998968964549)
                ·
                  rfl

theorem cell19_216862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_216862 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216862 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216862 prefixEnd_216862 := by exact prefixLift 216862
  have htrace : WordTrace (prefixWord ++ tailWord_216862) baseStart_216862 baseEnd_216862 := by
    simpa [prefixWord, tailWord_216862, baseEnd_216862] using wordTrace_append hprefix tailTrace_216862
  have hstable : (prefixWord ++ tailWord_216862).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216862).length < 2 ^ (prefixWord ++ tailWord_216862).sum := by decide
  have hdescent : baseEnd_216862 < baseStart_216862 := by decide
  rcases family_descends (prefixWord ++ tailWord_216862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216868 : List Nat := [2, 3, 1, 3, 2, 3, 2, 3]
def baseStart_216868 : Nat := 118140960795 + 216868 * 2 ^ 59
def prefixEnd_216868 : Nat := 4983230072969 + 3 ^ 40 * 216868 * 2
def baseEnd_216868 : Nat := 65989643009992732831199

theorem tailTrace_216868 : CollatzResearch.WordTrace tailWord_216868 prefixEnd_216868 65989643009992732831199 := by
  unfold tailWord_216868
  simp only [CollatzResearch.WordTrace]
  refine ⟨3954912889165874475377629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5273217185554499300503505 3954912889165874475377629)
  ·
    refine ⟨1483092333437202928266611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3954912889165874475377629 1483092333437202928266611)
    ·
      refine ⟨2224638500155804392399917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1483092333437202928266611 2224638500155804392399917)
      ·
        refine ⟨834239437558426647149969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2224638500155804392399917 834239437558426647149969)
        ·
          refine ⟨625679578168819985362477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 834239437558426647149969 625679578168819985362477)
          ·
            refine ⟨234629841813307494510929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 625679578168819985362477 234629841813307494510929)
            ·
              refine ⟨175972381359980620883197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234629841813307494510929 175972381359980620883197)
              ·
                refine ⟨65989643009992732831199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175972381359980620883197 65989643009992732831199)
                ·
                  rfl

theorem cell19_216868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 2, 3].length) (baseStart_216868 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216868 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216868 prefixEnd_216868 := by exact prefixLift 216868
  have htrace : WordTrace (prefixWord ++ tailWord_216868) baseStart_216868 baseEnd_216868 := by
    simpa [prefixWord, tailWord_216868, baseEnd_216868] using wordTrace_append hprefix tailTrace_216868
  have hstable : (prefixWord ++ tailWord_216868).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216868).length < 2 ^ (prefixWord ++ tailWord_216868).sum := by decide
  have hdescent : baseEnd_216868 < baseStart_216868 := by decide
  rcases family_descends (prefixWord ++ tailWord_216868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216908 : List Nat := [2, 2, 1, 3, 4, 1, 2, 4]
def baseStart_216908 : Nat := 118140960795 + 216908 * 2 ^ 59
def prefixEnd_216908 : Nat := 4983230072969 + 3 ^ 40 * 216908 * 2
def baseEnd_216908 : Nat := 66001814403284491942201

theorem tailTrace_216908 : CollatzResearch.WordTrace tailWord_216908 prefixEnd_216908 66001814403284491942201 := by
  unfold tailWord_216908
  simp only [CollatzResearch.WordTrace]
  refine ⟨3955642349093417891105689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5274189798791223854807585 3955642349093417891105689)
  ·
    refine ⟨2966731761820063418329267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3955642349093417891105689 2966731761820063418329267)
    ·
      refine ⟨4450097642730095127493901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2966731761820063418329267 4450097642730095127493901)
      ·
        refine ⟨1668786616023785672810213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4450097642730095127493901 1668786616023785672810213)
        ·
          refine ⟨312897490504459813651915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1668786616023785672810213 312897490504459813651915)
          ·
            refine ⟨469346235756689720477873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 312897490504459813651915 469346235756689720477873)
            ·
              refine ⟨352009676817517290358405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469346235756689720477873 352009676817517290358405)
              ·
                refine ⟨66001814403284491942201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352009676817517290358405 66001814403284491942201)
                ·
                  rfl

theorem cell19_216908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_216908 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216908 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216908 prefixEnd_216908 := by exact prefixLift 216908
  have htrace : WordTrace (prefixWord ++ tailWord_216908) baseStart_216908 baseEnd_216908 := by
    simpa [prefixWord, tailWord_216908, baseEnd_216908] using wordTrace_append hprefix tailTrace_216908
  have hstable : (prefixWord ++ tailWord_216908).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216908).length < 2 ^ (prefixWord ++ tailWord_216908).sum := by decide
  have hdescent : baseEnd_216908 < baseStart_216908 := by decide
  rcases family_descends (prefixWord ++ tailWord_216908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_216961 : List Nat := [1, 2, 4, 4, 2, 1, 1, 4]
def baseStart_216961 : Nat := 118140960795 + 216961 * 2 ^ 59
def prefixEnd_216961 : Nat := 4983230072969 + 3 ^ 40 * 216961 * 2
def baseEnd_216961 : Nat := 66017941499396072764279

theorem tailTrace_216961 : CollatzResearch.WordTrace tailWord_216961 prefixEnd_216961 66017941499396072764279 := by
  unfold tailWord_216961
  simp only [CollatzResearch.WordTrace]
  refine ⟨7913217766994825833890737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5275478511329883889260491 7913217766994825833890737)
  ·
    refine ⟨5934913325246119375418053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7913217766994825833890737 5934913325246119375418053)
    ·
      refine ⟨1112796248483647382890885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5934913325246119375418053 1112796248483647382890885)
      ·
        refine ⟨208649296590683884292041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1112796248483647382890885 208649296590683884292041)
        ·
          refine ⟨156486972443012913219031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 208649296590683884292041 156486972443012913219031)
          ·
            refine ⟨234730458664519369828547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156486972443012913219031 234730458664519369828547)
            ·
              refine ⟨352095687996779054742821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 234730458664519369828547 352095687996779054742821)
              ·
                refine ⟨66017941499396072764279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352095687996779054742821 66017941499396072764279)
                ·
                  rfl

theorem cell19_216961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 4].length) (baseStart_216961 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_216961 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_216961 prefixEnd_216961 := by exact prefixLift 216961
  have htrace : WordTrace (prefixWord ++ tailWord_216961) baseStart_216961 baseEnd_216961 := by
    simpa [prefixWord, tailWord_216961, baseEnd_216961] using wordTrace_append hprefix tailTrace_216961
  have hstable : (prefixWord ++ tailWord_216961).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_216961).length < 2 ^ (prefixWord ++ tailWord_216961).sum := by decide
  have hdescent : baseEnd_216961 < baseStart_216961 := by decide
  rcases family_descends (prefixWord ++ tailWord_216961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217007 : List Nat := [1, 1, 2, 1, 2, 2, 10]
def baseStart_217007 : Nat := 118140960795 + 217007 * 2 ^ 59
def prefixEnd_217007 : Nat := 4983230072969 + 3 ^ 40 * 217007 * 2
def baseEnd_217007 : Nat := 22010646200560531913977

theorem tailTrace_217007 : CollatzResearch.WordTrace tailWord_217007 prefixEnd_217007 22010646200560531913977 := by
  unfold tailWord_217007
  simp only [CollatzResearch.WordTrace]
  refine ⟨7914895524828175690065275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5276597016552117126710183 7914895524828175690065275)
  ·
    refine ⟨11872343287242263535097913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7914895524828175690065275 11872343287242263535097913)
    ·
      refine ⟨8904257465431697651323435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11872343287242263535097913 8904257465431697651323435)
      ·
        refine ⟨13356386198147546476985153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8904257465431697651323435 13356386198147546476985153)
        ·
          refine ⟨10017289648610659857738865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13356386198147546476985153 10017289648610659857738865)
          ·
            refine ⟨7512967236457994893304149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10017289648610659857738865 7512967236457994893304149)
            ·
              refine ⟨22010646200560531913977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7512967236457994893304149 22010646200560531913977)
              ·
                rfl

theorem cell19_217007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 10].length) (baseStart_217007 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217007 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217007 prefixEnd_217007 := by exact prefixLift 217007
  have htrace : WordTrace (prefixWord ++ tailWord_217007) baseStart_217007 baseEnd_217007 := by
    simpa [prefixWord, tailWord_217007, baseEnd_217007] using wordTrace_append hprefix tailTrace_217007
  have hstable : (prefixWord ++ tailWord_217007).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217007).length < 2 ^ (prefixWord ++ tailWord_217007).sum := by decide
  have hdescent : baseEnd_217007 < baseStart_217007 := by decide
  rcases family_descends (prefixWord ++ tailWord_217007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217058 : List Nat := [3, 3, 3, 1, 2, 2, 5]
def baseStart_217058 : Nat := 118140960795 + 217058 * 2 ^ 59
def prefixEnd_217058 : Nat := 4983230072969 + 3 ^ 40 * 217058 * 2
def baseEnd_217058 : Nat := 22015819042709529536153

theorem tailTrace_217058 : CollatzResearch.WordTrace tailWord_217058 prefixEnd_217058 22015819042709529536153 := by
  unfold tailWord_217058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1979188911910852850042957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5277837098428940933447885 1979188911910852850042957)
  ·
    refine ⟨742195841966569818766109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1979188911910852850042957 742195841966569818766109)
    ·
      refine ⟨278323440737463682037291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 742195841966569818766109 278323440737463682037291)
      ·
        refine ⟨417485161106195523055937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278323440737463682037291 417485161106195523055937)
        ·
          refine ⟨313113870829646642291953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 417485161106195523055937 313113870829646642291953)
          ·
            refine ⟨234835403122234981718965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313113870829646642291953 234835403122234981718965)
            ·
              refine ⟨22015819042709529536153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 234835403122234981718965 22015819042709529536153)
              ·
                rfl

theorem cell19_217058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 2, 5].length) (baseStart_217058 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217058 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217058 prefixEnd_217058 := by exact prefixLift 217058
  have htrace : WordTrace (prefixWord ++ tailWord_217058) baseStart_217058 baseEnd_217058 := by
    simpa [prefixWord, tailWord_217058, baseEnd_217058] using wordTrace_append hprefix tailTrace_217058
  have hstable : (prefixWord ++ tailWord_217058).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217058).length < 2 ^ (prefixWord ++ tailWord_217058).sum := by decide
  have hdescent : baseEnd_217058 < baseStart_217058 := by decide
  rcases family_descends (prefixWord ++ tailWord_217058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217081 : List Nat := [1, 2, 1, 3, 1, 5, 2, 4]
def baseStart_217081 : Nat := 118140960795 + 217081 * 2 ^ 59
def prefixEnd_217081 : Nat := 4983230072969 + 3 ^ 40 * 217081 * 2
def baseEnd_217081 : Nat := 66054455679271350097285

theorem tailTrace_217081 : CollatzResearch.WordTrace tailWord_217081 prefixEnd_217081 66054455679271350097285 := by
  unfold tailWord_217081
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917594526560086328259097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5278396351040057552172731 7917594526560086328259097)
  ·
    refine ⟨5938195894920064746194323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7917594526560086328259097 5938195894920064746194323)
    ·
      refine ⟨8907293842380097119291485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5938195894920064746194323 8907293842380097119291485)
      ·
        refine ⟨3340235190892536419734307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8907293842380097119291485 3340235190892536419734307)
        ·
          refine ⟨5010352786338804629601461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3340235190892536419734307 5010352786338804629601461)
          ·
            refine ⟨469720573719262934025137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5010352786338804629601461 469720573719262934025137)
            ·
              refine ⟨352290430289447200518853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 469720573719262934025137 352290430289447200518853)
              ·
                refine ⟨66054455679271350097285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352290430289447200518853 66054455679271350097285)
                ·
                  rfl

theorem cell19_217081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 2, 4].length) (baseStart_217081 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217081 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217081 prefixEnd_217081 := by exact prefixLift 217081
  have htrace : WordTrace (prefixWord ++ tailWord_217081) baseStart_217081 baseEnd_217081 := by
    simpa [prefixWord, tailWord_217081, baseEnd_217081] using wordTrace_append hprefix tailTrace_217081
  have hstable : (prefixWord ++ tailWord_217081).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217081).length < 2 ^ (prefixWord ++ tailWord_217081).sum := by decide
  have hdescent : baseEnd_217081 < baseStart_217081 := by decide
  rcases family_descends (prefixWord ++ tailWord_217081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217083 : List Nat := [1, 1, 1, 1, 1, 3, 5, 6]
def baseStart_217083 : Nat := 118140960795 + 217083 * 2 ^ 59
def prefixEnd_217083 : Nat := 4983230072969 + 3 ^ 40 * 217083 * 2
def baseEnd_217083 : Nat := 66055064248935938052835

theorem tailTrace_217083 : CollatzResearch.WordTrace tailWord_217083 prefixEnd_217083 66055064248935938052835 := by
  unfold tailWord_217083
  simp only [CollatzResearch.WordTrace]
  refine ⟨7917667472552840669831903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5278444981701893779887935 7917667472552840669831903)
  ·
    refine ⟨11876501208829261004747855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7917667472552840669831903 11876501208829261004747855)
    ·
      refine ⟨17814751813243891507121783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11876501208829261004747855 17814751813243891507121783)
      ·
        refine ⟨26722127719865837260682675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17814751813243891507121783 26722127719865837260682675)
        ·
          refine ⟨40083191579798755891024013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26722127719865837260682675 40083191579798755891024013)
          ·
            refine ⟨15031196842424533459134005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 40083191579798755891024013 15031196842424533459134005)
            ·
              refine ⟨1409174703977300011793813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 15031196842424533459134005 1409174703977300011793813)
              ·
                refine ⟨66055064248935938052835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1409174703977300011793813 66055064248935938052835)
                ·
                  rfl

theorem cell19_217083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_217083 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217083 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217083 prefixEnd_217083 := by exact prefixLift 217083
  have htrace : WordTrace (prefixWord ++ tailWord_217083) baseStart_217083 baseEnd_217083 := by
    simpa [prefixWord, tailWord_217083, baseEnd_217083] using wordTrace_append hprefix tailTrace_217083
  have hstable : (prefixWord ++ tailWord_217083).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217083).length < 2 ^ (prefixWord ++ tailWord_217083).sum := by decide
  have hdescent : baseEnd_217083 < baseStart_217083 := by decide
  rcases family_descends (prefixWord ++ tailWord_217083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217121 : List Nat := [1, 2, 3, 2, 11]
def baseStart_217121 : Nat := 118140960795 + 217121 * 2 ^ 59
def prefixEnd_217121 : Nat := 4983230072969 + 3 ^ 40 * 217121 * 2
def baseEnd_217121 : Nat := 2446912113798633674381

theorem tailTrace_217121 : CollatzResearch.WordTrace tailWord_217121 prefixEnd_217121 2446912113798633674381 := by
  unfold tailWord_217121
  simp only [CollatzResearch.WordTrace]
  refine ⟨7919053446415173159715217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5279368964276782106476811 7919053446415173159715217)
  ·
    refine ⟨5939290084811379869786413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7919053446415173159715217 5939290084811379869786413)
    ·
      refine ⟨2227233781804267451169905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5939290084811379869786413 2227233781804267451169905)
      ·
        refine ⟨1670425336353200588377429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2227233781804267451169905 1670425336353200588377429)
        ·
          refine ⟨2446912113798633674381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 1670425336353200588377429 2446912113798633674381)
          ·
            rfl

theorem cell19_217121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 11].length) (baseStart_217121 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217121 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217121 prefixEnd_217121 := by exact prefixLift 217121
  have htrace : WordTrace (prefixWord ++ tailWord_217121) baseStart_217121 baseEnd_217121 := by
    simpa [prefixWord, tailWord_217121, baseEnd_217121] using wordTrace_append hprefix tailTrace_217121
  have hstable : (prefixWord ++ tailWord_217121).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217121).length < 2 ^ (prefixWord ++ tailWord_217121).sum := by decide
  have hdescent : baseEnd_217121 < baseStart_217121 := by decide
  rcases family_descends (prefixWord ++ tailWord_217121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217138 : List Nat := [3, 2, 1, 1, 2, 3, 3, 4]
def baseStart_217138 : Nat := 118140960795 + 217138 * 2 ^ 59
def prefixEnd_217138 : Nat := 4983230072969 + 3 ^ 40 * 217138 * 2
def baseEnd_217138 : Nat := 66071799914712106830463

theorem tailTrace_217138 : CollatzResearch.WordTrace tailWord_217138 prefixEnd_217138 66071799914712106830463 := by
  unfold tailWord_217138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1979918371838396265771017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5279782324902390042056045 1979918371838396265771017)
  ·
    refine ⟨1484938778878797199328263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1979918371838396265771017 1484938778878797199328263)
    ·
      refine ⟨2227408168318195798992395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1484938778878797199328263 2227408168318195798992395)
      ·
        refine ⟨3341112252477293698488593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2227408168318195798992395 3341112252477293698488593)
        ·
          refine ⟨2505834189357970273866445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3341112252477293698488593 2505834189357970273866445)
          ·
            refine ⟨939687821009238852699917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2505834189357970273866445 939687821009238852699917)
            ·
              refine ⟨352382932878464569762469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 939687821009238852699917 352382932878464569762469)
              ·
                refine ⟨66071799914712106830463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352382932878464569762469 66071799914712106830463)
                ·
                  rfl

theorem cell19_217138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 4].length) (baseStart_217138 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217138 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217138 prefixEnd_217138 := by exact prefixLift 217138
  have htrace : WordTrace (prefixWord ++ tailWord_217138) baseStart_217138 baseEnd_217138 := by
    simpa [prefixWord, tailWord_217138, baseEnd_217138] using wordTrace_append hprefix tailTrace_217138
  have hstable : (prefixWord ++ tailWord_217138).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217138).length < 2 ^ (prefixWord ++ tailWord_217138).sum := by decide
  have hdescent : baseEnd_217138 < baseStart_217138 := by decide
  rcases family_descends (prefixWord ++ tailWord_217138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217178 : List Nat := [3, 1, 1, 2, 1, 1, 10]
def baseStart_217178 : Nat := 118140960795 + 217178 * 2 ^ 59
def prefixEnd_217178 : Nat := 4983230072969 + 3 ^ 40 * 217178 * 2
def baseEnd_217178 : Nat := 22027990436001288647155

theorem tailTrace_217178 : CollatzResearch.WordTrace tailWord_217178 prefixEnd_217178 22027990436001288647155 := by
  unfold tailWord_217178
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980283101802167973635047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5280754938139114596360125 1980283101802167973635047)
  ·
    refine ⟨2970424652703251960452571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1980283101802167973635047 2970424652703251960452571)
    ·
      refine ⟨4455636979054877940678857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2970424652703251960452571 4455636979054877940678857)
      ·
        refine ⟨3341727734291158455509143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4455636979054877940678857 3341727734291158455509143)
        ·
          refine ⟨5012591601436737683263715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3341727734291158455509143 5012591601436737683263715)
          ·
            refine ⟨7518887402155106524895573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5012591601436737683263715 7518887402155106524895573)
            ·
              refine ⟨22027990436001288647155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7518887402155106524895573 22027990436001288647155)
              ·
                rfl

theorem cell19_217178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_217178 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217178 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217178 prefixEnd_217178 := by exact prefixLift 217178
  have htrace : WordTrace (prefixWord ++ tailWord_217178) baseStart_217178 baseEnd_217178 := by
    simpa [prefixWord, tailWord_217178, baseEnd_217178] using wordTrace_append hprefix tailTrace_217178
  have hstable : (prefixWord ++ tailWord_217178).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217178).length < 2 ^ (prefixWord ++ tailWord_217178).sum := by decide
  have hdescent : baseEnd_217178 < baseStart_217178 := by decide
  rcases family_descends (prefixWord ++ tailWord_217178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217212 : List Nat := [2, 2, 2, 1, 1, 6, 2, 3]
def baseStart_217212 : Nat := 118140960795 + 217212 * 2 ^ 59
def prefixEnd_217212 : Nat := 4983230072969 + 3 ^ 40 * 217212 * 2
def baseEnd_217212 : Nat := 66094316992301861185817

theorem tailTrace_217212 : CollatzResearch.WordTrace tailWord_217212 prefixEnd_217212 66094316992301861185817 := by
  unfold tailWord_217212
  simp only [CollatzResearch.WordTrace]
  refine ⟨3961186244542747850638945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5281581659390330467518593 3961186244542747850638945)
  ·
    refine ⟨2970889683407060887979209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3961186244542747850638945 2970889683407060887979209)
    ·
      refine ⟨2228167262555295665984407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2970889683407060887979209 2228167262555295665984407)
      ·
        refine ⟨3342250893832943498976611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2228167262555295665984407 3342250893832943498976611)
        ·
          refine ⟨5013376340749415248464917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3342250893832943498976611 5013376340749415248464917)
          ·
            refine ⟨235002015972628839771793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5013376340749415248464917 235002015972628839771793)
            ·
              refine ⟨176251511979471629828845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235002015972628839771793 176251511979471629828845)
              ·
                refine ⟨66094316992301861185817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176251511979471629828845 66094316992301861185817)
                ·
                  rfl

theorem cell19_217212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_217212 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217212 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217212 prefixEnd_217212 := by exact prefixLift 217212
  have htrace : WordTrace (prefixWord ++ tailWord_217212) baseStart_217212 baseEnd_217212 := by
    simpa [prefixWord, tailWord_217212, baseEnd_217212] using wordTrace_append hprefix tailTrace_217212
  have hstable : (prefixWord ++ tailWord_217212).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217212).length < 2 ^ (prefixWord ++ tailWord_217212).sum := by decide
  have hdescent : baseEnd_217212 < baseStart_217212 := by decide
  rcases family_descends (prefixWord ++ tailWord_217212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217250 : List Nat := [3, 3, 1, 3, 1, 2, 2, 4]
def baseStart_217250 : Nat := 118140960795 + 217250 * 2 ^ 59
def prefixEnd_217250 : Nat := 4983230072969 + 3 ^ 40 * 217250 * 2
def baseEnd_217250 : Nat := 66105879815929032341269

theorem tailTrace_217250 : CollatzResearch.WordTrace tailWord_217250 prefixEnd_217250 66105879815929032341269 := by
  unfold tailWord_217250
  simp only [CollatzResearch.WordTrace]
  refine ⟨1980939615736957047790301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5282505641965218794107469 1980939615736957047790301)
  ·
    refine ⟨742852355901358892921363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1980939615736957047790301 742852355901358892921363)
    ·
      refine ⟨1114278533852038339382045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 742852355901358892921363 1114278533852038339382045)
      ·
        refine ⟨417854450194514377268267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1114278533852038339382045 417854450194514377268267)
        ·
          refine ⟨626781675291771565902401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 417854450194514377268267 626781675291771565902401)
          ·
            refine ⟨470086256468828674426801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 626781675291771565902401 470086256468828674426801)
            ·
              refine ⟨352564692351621505820101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 470086256468828674426801 352564692351621505820101)
              ·
                refine ⟨66105879815929032341269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352564692351621505820101 66105879815929032341269)
                ·
                  rfl

theorem cell19_217250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_217250 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217250 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217250 prefixEnd_217250 := by exact prefixLift 217250
  have htrace : WordTrace (prefixWord ++ tailWord_217250) baseStart_217250 baseEnd_217250 := by
    simpa [prefixWord, tailWord_217250, baseEnd_217250] using wordTrace_append hprefix tailTrace_217250
  have hstable : (prefixWord ++ tailWord_217250).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217250).length < 2 ^ (prefixWord ++ tailWord_217250).sum := by decide
  have hdescent : baseEnd_217250 < baseStart_217250 := by decide
  rcases family_descends (prefixWord ++ tailWord_217250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217273 : List Nat := [1, 2, 1, 4, 1, 2, 1, 7]
def baseStart_217273 : Nat := 118140960795 + 217273 * 2 ^ 59
def prefixEnd_217273 : Nat := 4983230072969 + 3 ^ 40 * 217273 * 2
def baseEnd_217273 : Nat := 66112878367071793830095

theorem tailTrace_217273 : CollatzResearch.WordTrace tailWord_217273 prefixEnd_217273 66112878367071793830095 := by
  unfold tailWord_217273
  simp only [CollatzResearch.WordTrace]
  refine ⟨7924597341864503119248473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5283064894576335412832315 7924597341864503119248473)
  ·
    refine ⟨5943448006398377339436355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7924597341864503119248473 5943448006398377339436355)
    ·
      refine ⟨8915172009597566009154533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5943448006398377339436355 8915172009597566009154533)
      ·
        refine ⟨1671594751799543626716475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8915172009597566009154533 1671594751799543626716475)
        ·
          refine ⟨2507392127699315440074713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1671594751799543626716475 2507392127699315440074713)
          ·
            refine ⟨1880544095774486580056035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2507392127699315440074713 1880544095774486580056035)
            ·
              refine ⟨2820816143661729870084053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1880544095774486580056035 2820816143661729870084053)
              ·
                refine ⟨66112878367071793830095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2820816143661729870084053 66112878367071793830095)
                ·
                  rfl

theorem cell19_217273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 7].length) (baseStart_217273 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217273 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217273 prefixEnd_217273 := by exact prefixLift 217273
  have htrace : WordTrace (prefixWord ++ tailWord_217273) baseStart_217273 baseEnd_217273 := by
    simpa [prefixWord, tailWord_217273, baseEnd_217273] using wordTrace_append hprefix tailTrace_217273
  have hstable : (prefixWord ++ tailWord_217273).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217273).length < 2 ^ (prefixWord ++ tailWord_217273).sum := by decide
  have hdescent : baseEnd_217273 < baseStart_217273 := by decide
  rcases family_descends (prefixWord ++ tailWord_217273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217368 : List Nat := [2, 1, 2, 3, 1, 2, 2, 6]
def baseStart_217368 : Nat := 118140960795 + 217368 * 2 ^ 59
def prefixEnd_217368 : Nat := 4983230072969 + 3 ^ 40 * 217368 * 2
def baseEnd_217368 : Nat := 66141785426139721718725

theorem tailTrace_217368 : CollatzResearch.WordTrace tailWord_217368 prefixEnd_217368 66141785426139721718725 := by
  unfold tailWord_217368
  simp only [CollatzResearch.WordTrace]
  refine ⟨3964031138260167171978379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5285374851013556229304505 3964031138260167171978379)
  ·
    refine ⟨5946046707390250757967569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3964031138260167171978379 5946046707390250757967569)
    ·
      refine ⟨4459535030542688068475677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5946046707390250757967569 4459535030542688068475677)
      ·
        refine ⟨1672325636453508025678379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4459535030542688068475677 1672325636453508025678379)
        ·
          refine ⟨2508488454680262038517569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1672325636453508025678379 2508488454680262038517569)
          ·
            refine ⟨1881366341010196528888177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2508488454680262038517569 1881366341010196528888177)
            ·
              refine ⟨1411024755757647396666133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1881366341010196528888177 1411024755757647396666133)
              ·
                refine ⟨66141785426139721718725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1411024755757647396666133 66141785426139721718725)
                ·
                  rfl

theorem cell19_217368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_217368 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217368 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217368 prefixEnd_217368 := by exact prefixLift 217368
  have htrace : WordTrace (prefixWord ++ tailWord_217368) baseStart_217368 baseEnd_217368 := by
    simpa [prefixWord, tailWord_217368, baseEnd_217368] using wordTrace_append hprefix tailTrace_217368
  have hstable : (prefixWord ++ tailWord_217368).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217368).length < 2 ^ (prefixWord ++ tailWord_217368).sum := by decide
  have hdescent : baseEnd_217368 < baseStart_217368 := by decide
  rcases family_descends (prefixWord ++ tailWord_217368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217381 : List Nat := [1, 3, 1, 2, 6, 1, 2, 3]
def baseStart_217381 : Nat := 118140960795 + 217381 * 2 ^ 59
def prefixEnd_217381 : Nat := 4983230072969 + 3 ^ 40 * 217381 * 2
def baseEnd_217381 : Nat := 66145741128959543429801

theorem tailTrace_217381 : CollatzResearch.WordTrace tailWord_217381 prefixEnd_217381 66145741128959543429801 := by
  unfold tailWord_217381
  simp only [CollatzResearch.WordTrace]
  refine ⟨7928536425473237564179997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5285690950315491709453331 7928536425473237564179997)
  ·
    refine ⟨2973201159552464086567499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7928536425473237564179997 2973201159552464086567499)
    ·
      refine ⟨4459801739328696129851249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2973201159552464086567499 4459801739328696129851249)
      ·
        refine ⟨3344851304496522097388437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4459801739328696129851249 3344851304496522097388437)
        ·
          refine ⟨156789904898274473315083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3344851304496522097388437 156789904898274473315083)
          ·
            refine ⟨235184857347411709972625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156789904898274473315083 235184857347411709972625)
            ·
              refine ⟨176388643010558782479469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235184857347411709972625 176388643010558782479469)
              ·
                refine ⟨66145741128959543429801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176388643010558782479469 66145741128959543429801)
                ·
                  rfl

theorem cell19_217381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 2, 3].length) (baseStart_217381 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217381 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217381 prefixEnd_217381 := by exact prefixLift 217381
  have htrace : WordTrace (prefixWord ++ tailWord_217381) baseStart_217381 baseEnd_217381 := by
    simpa [prefixWord, tailWord_217381, baseEnd_217381] using wordTrace_append hprefix tailTrace_217381
  have hstable : (prefixWord ++ tailWord_217381).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217381).length < 2 ^ (prefixWord ++ tailWord_217381).sum := by decide
  have hdescent : baseEnd_217381 < baseStart_217381 := by decide
  rcases family_descends (prefixWord ++ tailWord_217381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217425 : List Nat := [1, 2, 2, 1, 4, 2, 1, 6]
def baseStart_217425 : Nat := 118140960795 + 217425 * 2 ^ 59
def prefixEnd_217425 : Nat := 4983230072969 + 3 ^ 40 * 217425 * 2
def baseEnd_217425 : Nat := 66159129661580478451903

theorem tailTrace_217425 : CollatzResearch.WordTrace tailWord_217425 prefixEnd_217425 66159129661580478451903 := by
  unfold tailWord_217425
  simp only [CollatzResearch.WordTrace]
  refine ⟨7930141237313833078781729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5286760824875888719187819 7930141237313833078781729)
  ·
    refine ⟨5947605927985374809086297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7930141237313833078781729 5947605927985374809086297)
    ·
      refine ⟨4460704445989031106814723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5947605927985374809086297 4460704445989031106814723)
      ·
        refine ⟨6691056668983546660222085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4460704445989031106814723 6691056668983546660222085)
        ·
          refine ⟨1254573125434414998791641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6691056668983546660222085 1254573125434414998791641)
          ·
            refine ⟨940929844075811249093731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1254573125434414998791641 940929844075811249093731)
            ·
              refine ⟨1411394766113716873640597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 940929844075811249093731 1411394766113716873640597)
              ·
                refine ⟨66159129661580478451903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1411394766113716873640597 66159129661580478451903)
                ·
                  rfl

theorem cell19_217425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_217425 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217425 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217425 prefixEnd_217425 := by exact prefixLift 217425
  have htrace : WordTrace (prefixWord ++ tailWord_217425) baseStart_217425 baseEnd_217425 := by
    simpa [prefixWord, tailWord_217425, baseEnd_217425] using wordTrace_append hprefix tailTrace_217425
  have hstable : (prefixWord ++ tailWord_217425).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217425).length < 2 ^ (prefixWord ++ tailWord_217425).sum := by decide
  have hdescent : baseEnd_217425 < baseStart_217425 := by decide
  rcases family_descends (prefixWord ++ tailWord_217425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217442 : List Nat := [3, 3, 2, 1, 1, 2, 2, 5]
def baseStart_217442 : Nat := 118140960795 + 217442 * 2 ^ 59
def prefixEnd_217442 : Nat := 4983230072969 + 3 ^ 40 * 217442 * 2
def baseEnd_217442 : Nat := 66164302503729476074079

theorem tailTrace_217442 : CollatzResearch.WordTrace tailWord_217442 prefixEnd_217442 66164302503729476074079 := by
  unfold tailWord_217442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1982690319563061245537645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5287174185501496654767053 1982690319563061245537645)
  ·
    refine ⟨743508869836147967076617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1982690319563061245537645 743508869836147967076617)
    ·
      refine ⟨557631652377110975307463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 743508869836147967076617 557631652377110975307463)
      ·
        refine ⟨836447478565666462961195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 557631652377110975307463 836447478565666462961195)
        ·
          refine ⟨1254671217848499694441793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 836447478565666462961195 1254671217848499694441793)
          ·
            refine ⟨941003413386374770831345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1254671217848499694441793 941003413386374770831345)
            ·
              refine ⟨705752560039781078123509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 941003413386374770831345 705752560039781078123509)
              ·
                refine ⟨66164302503729476074079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 705752560039781078123509 66164302503729476074079)
                ·
                  rfl

theorem cell19_217442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_217442 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217442 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217442 prefixEnd_217442 := by exact prefixLift 217442
  have htrace : WordTrace (prefixWord ++ tailWord_217442) baseStart_217442 baseEnd_217442 := by
    simpa [prefixWord, tailWord_217442, baseEnd_217442] using wordTrace_append hprefix tailTrace_217442
  have hstable : (prefixWord ++ tailWord_217442).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217442).length < 2 ^ (prefixWord ++ tailWord_217442).sum := by decide
  have hdescent : baseEnd_217442 < baseStart_217442 := by decide
  rcases family_descends (prefixWord ++ tailWord_217442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217444 : List Nat := [2, 3, 1, 1, 3, 1, 1, 7]
def baseStart_217444 : Nat := 118140960795 + 217444 * 2 ^ 59
def prefixEnd_217444 : Nat := 4983230072969 + 3 ^ 40 * 217444 * 2
def baseEnd_217444 : Nat := 66164911073394064029629

theorem tailTrace_217444 : CollatzResearch.WordTrace tailWord_217444 prefixEnd_217444 66164911073394064029629 := by
  unfold tailWord_217444
  simp only [CollatzResearch.WordTrace]
  refine ⟨3965417112122499661861693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5287222816163332882482257 3965417112122499661861693)
  ·
    refine ⟨1487031417045937373198135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3965417112122499661861693 1487031417045937373198135)
    ·
      refine ⟨2230547125568906059797203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1487031417045937373198135 2230547125568906059797203)
      ·
        refine ⟨3345820688353359089695805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2230547125568906059797203 3345820688353359089695805)
        ·
          refine ⟨1254682758132509658635927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3345820688353359089695805 1254682758132509658635927)
          ·
            refine ⟨1882024137198764487953891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1254682758132509658635927 1882024137198764487953891)
            ·
              refine ⟨2823036205798146731930837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1882024137198764487953891 2823036205798146731930837)
              ·
                refine ⟨66164911073394064029629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2823036205798146731930837 66164911073394064029629)
                ·
                  rfl

theorem cell19_217444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_217444 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217444 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217444 prefixEnd_217444 := by exact prefixLift 217444
  have htrace : WordTrace (prefixWord ++ tailWord_217444) baseStart_217444 baseEnd_217444 := by
    simpa [prefixWord, tailWord_217444, baseEnd_217444] using wordTrace_append hprefix tailTrace_217444
  have hstable : (prefixWord ++ tailWord_217444).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217444).length < 2 ^ (prefixWord ++ tailWord_217444).sum := by decide
  have hdescent : baseEnd_217444 < baseStart_217444 := by decide
  rcases family_descends (prefixWord ++ tailWord_217444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217474 : List Nat := [3, 4, 2, 1, 3, 1, 1, 4]
def baseStart_217474 : Nat := 118140960795 + 217474 * 2 ^ 59
def prefixEnd_217474 : Nat := 4983230072969 + 3 ^ 40 * 217474 * 2
def baseEnd_217474 : Nat := 66174039618362883362881

theorem tailTrace_217474 : CollatzResearch.WordTrace tailWord_217474 prefixEnd_217474 66174039618362883362881 := by
  unfold tailWord_217474
  simp only [CollatzResearch.WordTrace]
  refine ⟨1982982103534078611828869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5287952276090876298210317 1982982103534078611828869)
  ·
    refine ⟨371809144412639739717913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1982982103534078611828869 371809144412639739717913)
    ·
      refine ⟨278856858309479804788435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 371809144412639739717913 278856858309479804788435)
      ·
        refine ⟨418285287464219707182653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 278856858309479804788435 418285287464219707182653)
        ·
          refine ⟨156856982799082390193495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418285287464219707182653 156856982799082390193495)
          ·
            refine ⟨235285474198623585290243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156856982799082390193495 235285474198623585290243)
            ·
              refine ⟨352928211297935377935365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235285474198623585290243 352928211297935377935365)
              ·
                refine ⟨66174039618362883362881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 352928211297935377935365 66174039618362883362881)
                ·
                  rfl

theorem cell19_217474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_217474 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217474 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217474 prefixEnd_217474 := by exact prefixLift 217474
  have htrace : WordTrace (prefixWord ++ tailWord_217474) baseStart_217474 baseEnd_217474 := by
    simpa [prefixWord, tailWord_217474, baseEnd_217474] using wordTrace_append hprefix tailTrace_217474
  have hstable : (prefixWord ++ tailWord_217474).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217474).length < 2 ^ (prefixWord ++ tailWord_217474).sum := by decide
  have hdescent : baseEnd_217474 < baseStart_217474 := by decide
  rcases family_descends (prefixWord ++ tailWord_217474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217514 : List Nat := [3, 1, 6, 1, 1, 1, 6]
def baseStart_217514 : Nat := 118140960795 + 217514 * 2 ^ 59
def prefixEnd_217514 : Nat := 4983230072969 + 3 ^ 40 * 217514 * 2
def baseEnd_217514 : Nat := 22062070337218214157961

theorem tailTrace_217514 : CollatzResearch.WordTrace tailWord_217514 prefixEnd_217514 22062070337218214157961 := by
  unfold tailWord_217514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1983346833497850319692899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5288924889327600852514397 1983346833497850319692899)
  ·
    refine ⟨2975020250246775479539349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1983346833497850319692899 2975020250246775479539349)
    ·
      refine ⟨139454074230317600603407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2975020250246775479539349 139454074230317600603407)
      ·
        refine ⟨209181111345476400905111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139454074230317600603407 209181111345476400905111)
        ·
          refine ⟨313771667018214601357667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209181111345476400905111 313771667018214601357667)
          ·
            refine ⟨470657500527321902036501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313771667018214601357667 470657500527321902036501)
            ·
              refine ⟨22062070337218214157961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 470657500527321902036501 22062070337218214157961)
              ·
                rfl

theorem cell19_217514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 6].length) (baseStart_217514 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217514 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217514 prefixEnd_217514 := by exact prefixLift 217514
  have htrace : WordTrace (prefixWord ++ tailWord_217514) baseStart_217514 baseEnd_217514 := by
    simpa [prefixWord, tailWord_217514, baseEnd_217514] using wordTrace_append hprefix tailTrace_217514
  have hstable : (prefixWord ++ tailWord_217514).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217514).length < 2 ^ (prefixWord ++ tailWord_217514).sum := by decide
  have hdescent : baseEnd_217514 < baseStart_217514 := by decide
  rcases family_descends (prefixWord ++ tailWord_217514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217554 : List Nat := [3, 2, 2, 4, 1, 1, 1, 5]
def baseStart_217554 : Nat := 118140960795 + 217554 * 2 ^ 59
def prefixEnd_217554 : Nat := 4983230072969 + 3 ^ 40 * 217554 * 2
def baseEnd_217554 : Nat := 66198382404946401584885

theorem tailTrace_217554 : CollatzResearch.WordTrace tailWord_217554 prefixEnd_217554 66198382404946401584885 := by
  unfold tailWord_217554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1983711563461622027556929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5289897502564325406818477 1983711563461622027556929)
  ·
    refine ⟨1487783672596216520667697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1983711563461622027556929 1487783672596216520667697)
    ·
      refine ⟨1115837754447162390500773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1487783672596216520667697 1115837754447162390500773)
      ·
        refine ⟨209219578958842948218895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1115837754447162390500773 209219578958842948218895)
        ·
          refine ⟨313829368438264422328343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209219578958842948218895 313829368438264422328343)
          ·
            refine ⟨470744052657396633492515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 313829368438264422328343 470744052657396633492515)
            ·
              refine ⟨706116078986094950238773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470744052657396633492515 706116078986094950238773)
              ·
                refine ⟨66198382404946401584885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 706116078986094950238773 66198382404946401584885)
                ·
                  rfl

theorem cell19_217554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_217554 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217554 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217554 prefixEnd_217554 := by exact prefixLift 217554
  have htrace : WordTrace (prefixWord ++ tailWord_217554) baseStart_217554 baseEnd_217554 := by
    simpa [prefixWord, tailWord_217554, baseEnd_217554] using wordTrace_append hprefix tailTrace_217554
  have hstable : (prefixWord ++ tailWord_217554).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217554).length < 2 ^ (prefixWord ++ tailWord_217554).sum := by decide
  have hdescent : baseEnd_217554 < baseStart_217554 := by decide
  rcases family_descends (prefixWord ++ tailWord_217554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217556 : List Nat := [2, 4, 1, 2, 2, 2, 1, 5]
def baseStart_217556 : Nat := 118140960795 + 217556 * 2 ^ 59
def prefixEnd_217556 : Nat := 4983230072969 + 3 ^ 40 * 217556 * 2
def baseEnd_217556 : Nat := 66198990974610989540435

theorem tailTrace_217556 : CollatzResearch.WordTrace tailWord_217556 prefixEnd_217556 66198990974610989540435 := by
  unfold tailWord_217556
  simp only [CollatzResearch.WordTrace]
  refine ⟨3967459599919621225900261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5289946133226161634533681 3967459599919621225900261)
  ·
    refine ⟨743898674984928979856299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3967459599919621225900261 743898674984928979856299)
    ·
      refine ⟨1115848012477393469784449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 743898674984928979856299 1115848012477393469784449)
      ·
        refine ⟨836886009358045102338337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1115848012477393469784449 836886009358045102338337)
        ·
          refine ⟨627664507018533826753753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 836886009358045102338337 627664507018533826753753)
          ·
            refine ⟨470748380263900370065315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 627664507018533826753753 470748380263900370065315)
            ·
              refine ⟨706122570395850555097973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 470748380263900370065315 706122570395850555097973)
              ·
                refine ⟨66198990974610989540435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 706122570395850555097973 66198990974610989540435)
                ·
                  rfl

theorem cell19_217556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_217556 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217556 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217556 prefixEnd_217556 := by exact prefixLift 217556
  have htrace : WordTrace (prefixWord ++ tailWord_217556) baseStart_217556 baseEnd_217556 := by
    simpa [prefixWord, tailWord_217556, baseEnd_217556] using wordTrace_append hprefix tailTrace_217556
  have hstable : (prefixWord ++ tailWord_217556).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217556).length < 2 ^ (prefixWord ++ tailWord_217556).sum := by decide
  have hdescent : baseEnd_217556 < baseStart_217556 := by decide
  rcases family_descends (prefixWord ++ tailWord_217556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217573 : List Nat := [1, 3, 1, 5, 3, 1, 5]
def baseStart_217573 : Nat := 118140960795 + 217573 * 2 ^ 59
def prefixEnd_217573 : Nat := 4983230072969 + 3 ^ 40 * 217573 * 2
def baseEnd_217573 : Nat := 22068054605586662387537

theorem tailTrace_217573 : CollatzResearch.WordTrace tailWord_217573 prefixEnd_217573 22068054605586662387537 := by
  unfold tailWord_217573
  simp only [CollatzResearch.WordTrace]
  refine ⟨7935539240777654355169373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5290359493851769570112915 7935539240777654355169373)
  ·
    refine ⟨2975827215291620383188515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7935539240777654355169373 2975827215291620383188515)
    ·
      refine ⟨4463740822937430574782773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2975827215291620383188515 4463740822937430574782773)
      ·
        refine ⟨418475702150384116385885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4463740822937430574782773 418475702150384116385885)
        ·
          refine ⟨156928388306394043644707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418475702150384116385885 156928388306394043644707)
          ·
            refine ⟨235392582459591065467061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156928388306394043644707 235392582459591065467061)
            ·
              refine ⟨22068054605586662387537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235392582459591065467061 22068054605586662387537)
              ·
                rfl

theorem cell19_217573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 3, 1, 5].length) (baseStart_217573 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217573 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217573 prefixEnd_217573 := by exact prefixLift 217573
  have htrace : WordTrace (prefixWord ++ tailWord_217573) baseStart_217573 baseEnd_217573 := by
    simpa [prefixWord, tailWord_217573, baseEnd_217573] using wordTrace_append hprefix tailTrace_217573
  have hstable : (prefixWord ++ tailWord_217573).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217573).length < 2 ^ (prefixWord ++ tailWord_217573).sum := by decide
  have hdescent : baseEnd_217573 < baseStart_217573 := by decide
  rcases family_descends (prefixWord ++ tailWord_217573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217632 : List Nat := [2, 1, 1, 6, 3, 6]
def baseStart_217632 : Nat := 118140960795 + 217632 * 2 ^ 59
def prefixEnd_217632 : Nat := 4983230072969 + 3 ^ 40 * 217632 * 2
def baseEnd_217632 : Nat := 7358012957985036872371

theorem tailTrace_217632 : CollatzResearch.WordTrace tailWord_217632 prefixEnd_217632 7358012957985036872371 := by
  unfold tailWord_217632
  simp only [CollatzResearch.WordTrace]
  refine ⟨3968845573781953715783575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5291794098375938287711433 3968845573781953715783575)
  ·
    refine ⟨5953268360672930573675363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3968845573781953715783575 5953268360672930573675363)
    ·
      refine ⟨8929902541009395860513045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5953268360672930573675363 8929902541009395860513045)
      ·
        refine ⟨418589181609815430961549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8929902541009395860513045 418589181609815430961549)
        ·
          refine ⟨156970943103680786610581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 418589181609815430961549 156970943103680786610581)
          ·
            refine ⟨7358012957985036872371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 156970943103680786610581 7358012957985036872371)
            ·
              rfl

theorem cell19_217632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 3, 6].length) (baseStart_217632 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217632 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217632 prefixEnd_217632 := by exact prefixLift 217632
  have htrace : WordTrace (prefixWord ++ tailWord_217632) baseStart_217632 baseEnd_217632 := by
    simpa [prefixWord, tailWord_217632, baseEnd_217632] using wordTrace_append hprefix tailTrace_217632
  have hstable : (prefixWord ++ tailWord_217632).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217632).length < 2 ^ (prefixWord ++ tailWord_217632).sum := by decide
  have hdescent : baseEnd_217632 < baseStart_217632 := by decide
  rcases family_descends (prefixWord ++ tailWord_217632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217645 : List Nat := [1, 5, 4, 1, 1, 2, 1, 4]
def baseStart_217645 : Nat := 118140960795 + 217645 * 2 ^ 59
def prefixEnd_217645 : Nat := 4983230072969 + 3 ^ 40 * 217645 * 2
def baseEnd_217645 : Nat := 66226072324685153562415

theorem tailTrace_217645 : CollatzResearch.WordTrace tailWord_217645 prefixEnd_217645 66226072324685153562415 := by
  unfold tailWord_217645
  simp only [CollatzResearch.WordTrace]
  refine ⟨7938165296516810651790389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5292110197677873767860259 7938165296516810651790389)
  ·
    refine ⟨744202996548450998605349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7938165296516810651790389 744202996548450998605349)
    ·
      refine ⟨139538061852834562238503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 744202996548450998605349 139538061852834562238503)
      ·
        refine ⟨209307092779251843357755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139538061852834562238503 209307092779251843357755)
        ·
          refine ⟨313960639168877765036633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 209307092779251843357755 313960639168877765036633)
          ·
            refine ⟨235470479376658323777475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 313960639168877765036633 235470479376658323777475)
            ·
              refine ⟨353205719064987485666213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235470479376658323777475 353205719064987485666213)
              ·
                refine ⟨66226072324685153562415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 353205719064987485666213 66226072324685153562415)
                ·
                  rfl

theorem cell19_217645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 4].length) (baseStart_217645 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217645 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217645 prefixEnd_217645 := by exact prefixLift 217645
  have htrace : WordTrace (prefixWord ++ tailWord_217645) baseStart_217645 baseEnd_217645 := by
    simpa [prefixWord, tailWord_217645, baseEnd_217645] using wordTrace_append hprefix tailTrace_217645
  have hstable : (prefixWord ++ tailWord_217645).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217645).length < 2 ^ (prefixWord ++ tailWord_217645).sum := by decide
  have hdescent : baseEnd_217645 < baseStart_217645 := by decide
  rcases family_descends (prefixWord ++ tailWord_217645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217725 : List Nat := [1, 4, 1, 1, 5, 2, 2, 3]
def baseStart_217725 : Nat := 118140960795 + 217725 * 2 ^ 59
def prefixEnd_217725 : Nat := 4983230072969 + 3 ^ 40 * 217725 * 2
def baseEnd_217725 : Nat := 66250415111268671784419

theorem tailTrace_217725 : CollatzResearch.WordTrace tailWord_217725 prefixEnd_217725 66250415111268671784419 := by
  unfold tailWord_217725
  simp only [CollatzResearch.WordTrace]
  refine ⟨7941083136226984314702629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5294055424151322876468419 7941083136226984314702629)
  ·
    refine ⟨1488953088042559559006743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7941083136226984314702629 1488953088042559559006743)
    ·
      refine ⟨2233429632063839338510115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1488953088042559559006743 2233429632063839338510115)
      ·
        refine ⟨3350144448095759007765173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2233429632063839338510115 3350144448095759007765173)
        ·
          refine ⟨314076042008977406977985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3350144448095759007765173 314076042008977406977985)
          ·
            refine ⟨235557031506733055233489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314076042008977406977985 235557031506733055233489)
            ·
              refine ⟨176667773630049791425117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235557031506733055233489 176667773630049791425117)
              ·
                refine ⟨66250415111268671784419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176667773630049791425117 66250415111268671784419)
                ·
                  rfl

theorem cell19_217725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 2, 3].length) (baseStart_217725 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217725 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217725 prefixEnd_217725 := by exact prefixLift 217725
  have htrace : WordTrace (prefixWord ++ tailWord_217725) baseStart_217725 baseEnd_217725 := by
    simpa [prefixWord, tailWord_217725, baseEnd_217725] using wordTrace_append hprefix tailTrace_217725
  have hstable : (prefixWord ++ tailWord_217725).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217725).length < 2 ^ (prefixWord ++ tailWord_217725).sum := by decide
  have hdescent : baseEnd_217725 < baseStart_217725 := by decide
  rcases family_descends (prefixWord ++ tailWord_217725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217729 : List Nat := [1, 2, 4, 2, 1, 1, 3, 5]
def baseStart_217729 : Nat := 118140960795 + 217729 * 2 ^ 59
def prefixEnd_217729 : Nat := 4983230072969 + 3 ^ 40 * 217729 * 2
def baseEnd_217729 : Nat := 66251632250597847695519

theorem tailTrace_217729 : CollatzResearch.WordTrace tailWord_217729 prefixEnd_217729 66251632250597847695519 := by
  unfold tailWord_217729
  simp only [CollatzResearch.WordTrace]
  refine ⟨7941229028212492997848241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5294152685474995331898827 7941229028212492997848241)
  ·
    refine ⟨5955921771159369748386181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7941229028212492997848241 5955921771159369748386181)
    ·
      refine ⟨1116735332092381827822409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5955921771159369748386181 1116735332092381827822409)
      ·
        refine ⟨837551499069286370866807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1116735332092381827822409 837551499069286370866807)
        ·
          refine ⟨1256327248603929556300211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 837551499069286370866807 1256327248603929556300211)
          ·
            refine ⟨1884490872905894334450317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1256327248603929556300211 1884490872905894334450317)
            ·
              refine ⟨706684077339710375418869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1884490872905894334450317 706684077339710375418869)
              ·
                refine ⟨66251632250597847695519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 706684077339710375418869 66251632250597847695519)
                ·
                  rfl

theorem cell19_217729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 5].length) (baseStart_217729 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217729 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217729 prefixEnd_217729 := by exact prefixLift 217729
  have htrace : WordTrace (prefixWord ++ tailWord_217729) baseStart_217729 baseEnd_217729 := by
    simpa [prefixWord, tailWord_217729, baseEnd_217729] using wordTrace_append hprefix tailTrace_217729
  have hstable : (prefixWord ++ tailWord_217729).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217729).length < 2 ^ (prefixWord ++ tailWord_217729).sum := by decide
  have hdescent : baseEnd_217729 < baseStart_217729 := by decide
  rcases family_descends (prefixWord ++ tailWord_217729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217746 : List Nat := [3, 2, 3, 1, 2, 3, 5]
def baseStart_217746 : Nat := 118140960795 + 217746 * 2 ^ 59
def prefixEnd_217746 : Nat := 4983230072969 + 3 ^ 40 * 217746 * 2
def baseEnd_217746 : Nat := 22085601697582281772565

theorem tailTrace_217746 : CollatzResearch.WordTrace tailWord_217746 prefixEnd_217746 22085601697582281772565 := by
  unfold tailWord_217746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1985462267287726225304273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5294566046100603267478061 1985462267287726225304273)
  ·
    refine ⟨1489096700465794668978205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1985462267287726225304273 1489096700465794668978205)
    ·
      refine ⟨558411262674673000866827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1489096700465794668978205 558411262674673000866827)
      ·
        refine ⟨837616894012009501300241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 558411262674673000866827 837616894012009501300241)
        ·
          refine ⟨628212670509007125975181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 837616894012009501300241 628212670509007125975181)
          ·
            refine ⟨235579751440877672240693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 628212670509007125975181 235579751440877672240693)
            ·
              refine ⟨22085601697582281772565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235579751440877672240693 22085601697582281772565)
              ·
                rfl

theorem cell19_217746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_217746 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217746 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217746 prefixEnd_217746 := by exact prefixLift 217746
  have htrace : WordTrace (prefixWord ++ tailWord_217746) baseStart_217746 baseEnd_217746 := by
    simpa [prefixWord, tailWord_217746, baseEnd_217746] using wordTrace_append hprefix tailTrace_217746
  have hstable : (prefixWord ++ tailWord_217746).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217746).length < 2 ^ (prefixWord ++ tailWord_217746).sum := by decide
  have hdescent : baseEnd_217746 < baseStart_217746 := by decide
  rcases family_descends (prefixWord ++ tailWord_217746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217769 : List Nat := [1, 2, 1, 1, 1, 1, 2, 10]
def baseStart_217769 : Nat := 118140960795 + 217769 * 2 ^ 59
def prefixEnd_217769 : Nat := 4983230072969 + 3 ^ 40 * 217769 * 2
def baseEnd_217769 : Nat := 66263803643889606806521

theorem tailTrace_217769 : CollatzResearch.WordTrace tailWord_217769 prefixEnd_217769 66263803643889606806521 := by
  unfold tailWord_217769
  simp only [CollatzResearch.WordTrace]
  refine ⟨7942687948067579829304361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5295125298711719886202907 7942687948067579829304361)
  ·
    refine ⟨5957015961050684871978271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7942687948067579829304361 5957015961050684871978271)
    ·
      refine ⟨8935523941576027307967407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5957015961050684871978271 8935523941576027307967407)
      ·
        refine ⟨13403285912364040961951111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8935523941576027307967407 13403285912364040961951111)
        ·
          refine ⟨20104928868546061442926667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13403285912364040961951111 20104928868546061442926667)
          ·
            refine ⟨30157393302819092164390001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20104928868546061442926667 30157393302819092164390001)
            ·
              refine ⟨22618044977114319123292501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 30157393302819092164390001 22618044977114319123292501)
              ·
                refine ⟨66263803643889606806521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22618044977114319123292501 66263803643889606806521)
                ·
                  rfl

theorem cell19_217769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_217769 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217769 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217769 prefixEnd_217769 := by exact prefixLift 217769
  have htrace : WordTrace (prefixWord ++ tailWord_217769) baseStart_217769 baseEnd_217769 := by
    simpa [prefixWord, tailWord_217769, baseEnd_217769] using wordTrace_append hprefix tailTrace_217769
  have hstable : (prefixWord ++ tailWord_217769).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217769).length < 2 ^ (prefixWord ++ tailWord_217769).sum := by decide
  have hdescent : baseEnd_217769 < baseStart_217769 := by decide
  rcases family_descends (prefixWord ++ tailWord_217769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217820 : List Nat := [2, 2, 5, 1, 1, 3, 1, 4]
def baseStart_217820 : Nat := 118140960795 + 217820 * 2 ^ 59
def prefixEnd_217820 : Nat := 4983230072969 + 3 ^ 40 * 217820 * 2
def baseEnd_217820 : Nat := 66279322170336599673049

theorem tailTrace_217820 : CollatzResearch.WordTrace tailWord_217820 prefixEnd_217820 66279322170336599673049 := by
  unfold tailWord_217820
  simp only [CollatzResearch.WordTrace]
  refine ⟨3972274035441407769705457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5296365380588543692940609 3972274035441407769705457)
  ·
    refine ⟨2979205526581055827279093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3972274035441407769705457 2979205526581055827279093)
    ·
      refine ⟨279300518116973983807415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2979205526581055827279093 279300518116973983807415)
      ·
        refine ⟨418950777175460975711123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 279300518116973983807415 418950777175460975711123)
        ·
          refine ⟨628426165763191463566685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 418950777175460975711123 628426165763191463566685)
          ·
            refine ⟨235659812161196798837507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 628426165763191463566685 235659812161196798837507)
            ·
              refine ⟨353489718241795198256261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 235659812161196798837507 353489718241795198256261)
              ·
                refine ⟨66279322170336599673049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 353489718241795198256261 66279322170336599673049)
                ·
                  rfl

theorem cell19_217820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_217820 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217820 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217820 prefixEnd_217820 := by exact prefixLift 217820
  have htrace : WordTrace (prefixWord ++ tailWord_217820) baseStart_217820 baseEnd_217820 := by
    simpa [prefixWord, tailWord_217820, baseEnd_217820] using wordTrace_append hprefix tailTrace_217820
  have hstable : (prefixWord ++ tailWord_217820).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217820).length < 2 ^ (prefixWord ++ tailWord_217820).sum := by decide
  have hdescent : baseEnd_217820 < baseStart_217820 := by decide
  rcases family_descends (prefixWord ++ tailWord_217820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217917 : List Nat := [1, 4, 1, 4, 2, 2, 5]
def baseStart_217917 : Nat := 118140960795 + 217917 * 2 ^ 59
def prefixEnd_217917 : Nat := 4983230072969 + 3 ^ 40 * 217917 * 2
def baseEnd_217917 : Nat := 22102945933023038505743

theorem tailTrace_217917 : CollatzResearch.WordTrace tailWord_217917 prefixEnd_217917 22102945933023038505743 := by
  unfold tailWord_217917
  simp only [CollatzResearch.WordTrace]
  refine ⟨7948085951531401105692005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5298723967687600737128003 7948085951531401105692005)
  ·
    refine ⟨1490266115912137707317251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7948085951531401105692005 1490266115912137707317251)
    ·
      refine ⟨2235399173868206560975877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1490266115912137707317251 2235399173868206560975877)
      ·
        refine ⟨419137345100288730182977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2235399173868206560975877 419137345100288730182977)
        ·
          refine ⟨314353008825216547637233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 419137345100288730182977 314353008825216547637233)
          ·
            refine ⟨235764756618912410727925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 314353008825216547637233 235764756618912410727925)
            ·
              refine ⟨22102945933023038505743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235764756618912410727925 22102945933023038505743)
              ·
                rfl

theorem cell19_217917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_217917 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217917 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217917 prefixEnd_217917 := by exact prefixLift 217917
  have htrace : WordTrace (prefixWord ++ tailWord_217917) baseStart_217917 baseEnd_217917 := by
    simpa [prefixWord, tailWord_217917, baseEnd_217917] using wordTrace_append hprefix tailTrace_217917
  have hstable : (prefixWord ++ tailWord_217917).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217917).length < 2 ^ (prefixWord ++ tailWord_217917).sum := by decide
  have hdescent : baseEnd_217917 < baseStart_217917 := by decide
  rcases family_descends (prefixWord ++ tailWord_217917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217919 : List Nat := [1, 1, 2, 2, 5, 3, 5]
def baseStart_217919 : Nat := 118140960795 + 217919 * 2 ^ 59
def prefixEnd_217919 : Nat := 4983230072969 + 3 ^ 40 * 217919 * 2
def baseEnd_217919 : Nat := 22103148789577901157593

theorem tailTrace_217919 : CollatzResearch.WordTrace tailWord_217919 prefixEnd_217919 22103148789577901157593 := by
  unfold tailWord_217919
  simp only [CollatzResearch.WordTrace]
  refine ⟨7948158897524155447264811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5298772598349436964843207 7948158897524155447264811)
  ·
    refine ⟨11922238346286233170897217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7948158897524155447264811 11922238346286233170897217)
    ·
      refine ⟨8941678759714674878172913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11922238346286233170897217 8941678759714674878172913)
      ·
        refine ⟨6706259069786006158629685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8941678759714674878172913 6706259069786006158629685)
        ·
          refine ⟨628711787792438077371533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6706259069786006158629685 628711787792438077371533)
          ·
            refine ⟨235766920422164279014325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 628711787792438077371533 235766920422164279014325)
            ·
              refine ⟨22103148789577901157593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235766920422164279014325 22103148789577901157593)
              ·
                rfl

theorem cell19_217919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_217919 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217919 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217919 prefixEnd_217919 := by exact prefixLift 217919
  have htrace : WordTrace (prefixWord ++ tailWord_217919) baseStart_217919 baseEnd_217919 := by
    simpa [prefixWord, tailWord_217919, baseEnd_217919] using wordTrace_append hprefix tailTrace_217919
  have hstable : (prefixWord ++ tailWord_217919).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217919).length < 2 ^ (prefixWord ++ tailWord_217919).sum := by decide
  have hdescent : baseEnd_217919 < baseStart_217919 := by decide
  rcases family_descends (prefixWord ++ tailWord_217919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_217938 : List Nat := [3, 2, 2, 1, 1, 2, 4, 4]
def baseStart_217938 : Nat := 118140960795 + 217938 * 2 ^ 59
def prefixEnd_217938 : Nat := 4983230072969 + 3 ^ 40 * 217938 * 2
def baseEnd_217938 : Nat := 66315227780547289050505

theorem tailTrace_217938 : CollatzResearch.WordTrace tailWord_217938 prefixEnd_217938 66315227780547289050505 := by
  unfold tailWord_217938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1987212971113830423051617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5299234589636881128137645 1987212971113830423051617)
  ·
    refine ⟨1490409728335372817288713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1987212971113830423051617 1490409728335372817288713)
    ·
      refine ⟨1117807296251529612966535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1490409728335372817288713 1117807296251529612966535)
      ·
        refine ⟨1676710944377294419449803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1117807296251529612966535 1676710944377294419449803)
        ·
          refine ⟨2515066416565941629174705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1676710944377294419449803 2515066416565941629174705)
          ·
            refine ⟨1886299812424456221881029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2515066416565941629174705 1886299812424456221881029)
            ·
              refine ⟨353681214829585541602693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1886299812424456221881029 353681214829585541602693)
              ·
                refine ⟨66315227780547289050505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 353681214829585541602693 66315227780547289050505)
                ·
                  rfl

theorem cell19_217938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 4, 4].length) (baseStart_217938 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_217938 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_217938 prefixEnd_217938 := by exact prefixLift 217938
  have htrace : WordTrace (prefixWord ++ tailWord_217938) baseStart_217938 baseEnd_217938 := by
    simpa [prefixWord, tailWord_217938, baseEnd_217938] using wordTrace_append hprefix tailTrace_217938
  have hstable : (prefixWord ++ tailWord_217938).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_217938).length < 2 ^ (prefixWord ++ tailWord_217938).sum := by decide
  have hdescent : baseEnd_217938 < baseStart_217938 := by decide
  rcases family_descends (prefixWord ++ tailWord_217938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218016 : List Nat := [2, 1, 1, 4, 1, 1, 2, 7]
def baseStart_218016 : Nat := 118140960795 + 218016 * 2 ^ 59
def prefixEnd_218016 : Nat := 4983230072969 + 3 ^ 40 * 218016 * 2
def baseEnd_218016 : Nat := 66338961997466219316959

theorem tailTrace_218016 : CollatzResearch.WordTrace tailWord_218016 prefixEnd_218016 66338961997466219316959 := by
  unfold tailWord_218016
  simp only [CollatzResearch.WordTrace]
  refine ⟨3975848389086370506772951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5301131185448494009030601 3975848389086370506772951)
  ·
    refine ⟨5963772583629555760159427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3975848389086370506772951 5963772583629555760159427)
    ·
      refine ⟨8945658875444333640239141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5963772583629555760159427 8945658875444333640239141)
      ·
        refine ⟨1677311039145812557544839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8945658875444333640239141 1677311039145812557544839)
        ·
          refine ⟨2515966558718718836317259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1677311039145812557544839 2515966558718718836317259)
          ·
            refine ⟨3773949838078078254475889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2515966558718718836317259 3773949838078078254475889)
            ·
              refine ⟨2830462378558558690856917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3773949838078078254475889 2830462378558558690856917)
              ·
                refine ⟨66338961997466219316959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2830462378558558690856917 66338961997466219316959)
                ·
                  rfl

theorem cell19_218016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_218016 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218016 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218016 prefixEnd_218016 := by exact prefixLift 218016
  have htrace : WordTrace (prefixWord ++ tailWord_218016) baseStart_218016 baseEnd_218016 := by
    simpa [prefixWord, tailWord_218016, baseEnd_218016] using wordTrace_append hprefix tailTrace_218016
  have hstable : (prefixWord ++ tailWord_218016).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218016).length < 2 ^ (prefixWord ++ tailWord_218016).sum := by decide
  have hdescent : baseEnd_218016 < baseStart_218016 := by decide
  rcases family_descends (prefixWord ++ tailWord_218016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218033 : List Nat := [1, 2, 2, 4, 3, 1, 6]
def baseStart_218033 : Nat := 118140960795 + 218033 * 2 ^ 59
def prefixEnd_218033 : Nat := 4983230072969 + 3 ^ 40 * 218033 * 2
def baseEnd_218033 : Nat := 22114711613205072313045

theorem tailTrace_218033 : CollatzResearch.WordTrace tailWord_218033 prefixEnd_218033 22114711613205072313045 := by
  unfold tailWord_218033
  simp only [CollatzResearch.WordTrace]
  refine ⟨7952316819111152916914753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5301544546074101944609835 7952316819111152916914753)
  ·
    refine ⟨5964237614333364687686065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7952316819111152916914753 5964237614333364687686065)
    ·
      refine ⟨4473178210750023515764549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5964237614333364687686065 4473178210750023515764549)
      ·
        refine ⟨838720914515629409205853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4473178210750023515764549 838720914515629409205853)
        ·
          refine ⟨314520342943361028452195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 838720914515629409205853 314520342943361028452195)
          ·
            refine ⟨471780514415041542678293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314520342943361028452195 471780514415041542678293)
            ·
              refine ⟨22114711613205072313045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 471780514415041542678293 22114711613205072313045)
              ·
                rfl

theorem cell19_218033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 6].length) (baseStart_218033 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218033 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218033 prefixEnd_218033 := by exact prefixLift 218033
  have htrace : WordTrace (prefixWord ++ tailWord_218033) baseStart_218033 baseEnd_218033 := by
    simpa [prefixWord, tailWord_218033, baseEnd_218033] using wordTrace_append hprefix tailTrace_218033
  have hstable : (prefixWord ++ tailWord_218033).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218033).length < 2 ^ (prefixWord ++ tailWord_218033).sum := by decide
  have hdescent : baseEnd_218033 < baseStart_218033 := by decide
  rcases family_descends (prefixWord ++ tailWord_218033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218061 : List Nat := [1, 6, 3, 1, 2, 1, 2, 3]
def baseStart_218061 : Nat := 118140960795 + 218061 * 2 ^ 59
def prefixEnd_218061 : Nat := 4983230072969 + 3 ^ 40 * 218061 * 2
def baseEnd_218061 : Nat := 66352654814919448316837

theorem tailTrace_218061 : CollatzResearch.WordTrace tailWord_218061 prefixEnd_218061 66352654814919448316837 := by
  unfold tailWord_218061
  simp only [CollatzResearch.WordTrace]
  refine ⟨7953338063009713698934037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5302225375339809132622691 7953338063009713698934037)
  ·
    refine ⟨372812721703580329637533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7953338063009713698934037 372812721703580329637533)
    ·
      refine ⟨139804770638842623614075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 372812721703580329637533 139804770638842623614075)
      ·
        refine ⟨209707155958263935421113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 139804770638842623614075 209707155958263935421113)
        ·
          refine ⟨157280366968697951565835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 209707155958263935421113 157280366968697951565835)
          ·
            refine ⟨235920550453046927348753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157280366968697951565835 235920550453046927348753)
            ·
              refine ⟨176940412839785195511565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 235920550453046927348753 176940412839785195511565)
              ·
                refine ⟨66352654814919448316837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 176940412839785195511565 66352654814919448316837)
                ·
                  rfl

theorem cell19_218061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 3].length) (baseStart_218061 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218061 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218061 prefixEnd_218061 := by exact prefixLift 218061
  have htrace : WordTrace (prefixWord ++ tailWord_218061) baseStart_218061 baseEnd_218061 := by
    simpa [prefixWord, tailWord_218061, baseEnd_218061] using wordTrace_append hprefix tailTrace_218061
  have hstable : (prefixWord ++ tailWord_218061).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218061).length < 2 ^ (prefixWord ++ tailWord_218061).sum := by decide
  have hdescent : baseEnd_218061 < baseStart_218061 := by decide
  rcases family_descends (prefixWord ++ tailWord_218061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218090 : List Nat := [3, 1, 3, 1, 2, 4, 5]
def baseStart_218090 : Nat := 118140960795 + 218090 * 2 ^ 59
def prefixEnd_218090 : Nat := 4983230072969 + 3 ^ 40 * 218090 * 2
def baseEnd_218090 : Nat := 22120493025018657890771

theorem tailTrace_218090 : CollatzResearch.WordTrace tailWord_218090 prefixEnd_218090 22120493025018657890771 := by
  unfold tailWord_218090
  simp only [CollatzResearch.WordTrace]
  refine ⟨1988598944976162912934931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5302930519936434434493149 1988598944976162912934931)
  ·
    refine ⟨2982898417464244369402397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1988598944976162912934931 2982898417464244369402397)
    ·
      refine ⟨1118586906549091638525899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2982898417464244369402397 1118586906549091638525899)
      ·
        refine ⟨1677880359823637457788849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1118586906549091638525899 1677880359823637457788849)
        ·
          refine ⟨1258410269867728093341637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1677880359823637457788849 1258410269867728093341637)
          ·
            refine ⟨235951925600199017501557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1258410269867728093341637 235951925600199017501557)
            ·
              refine ⟨22120493025018657890771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 235951925600199017501557 22120493025018657890771)
              ·
                rfl

theorem cell19_218090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_218090 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218090 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218090 prefixEnd_218090 := by exact prefixLift 218090
  have htrace : WordTrace (prefixWord ++ tailWord_218090) baseStart_218090 baseEnd_218090 := by
    simpa [prefixWord, tailWord_218090, baseEnd_218090] using wordTrace_append hprefix tailTrace_218090
  have hstable : (prefixWord ++ tailWord_218090).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218090).length < 2 ^ (prefixWord ++ tailWord_218090).sum := by decide
  have hdescent : baseEnd_218090 < baseStart_218090 := by decide
  rcases family_descends (prefixWord ++ tailWord_218090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218164 : List Nat := [2, 5, 1, 2, 1, 1, 3, 4]
def baseStart_218164 : Nat := 118140960795 + 218164 * 2 ^ 59
def prefixEnd_218164 : Nat := 4983230072969 + 3 ^ 40 * 218164 * 2
def baseEnd_218164 : Nat := 66383996152645728027667

theorem tailTrace_218164 : CollatzResearch.WordTrace tailWord_218164 prefixEnd_218164 66383996152645728027667 := by
  unfold tailWord_218164
  simp only [CollatzResearch.WordTrace]
  refine ⟨3978547390818281144966773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5304729854424374859955697 3978547390818281144966773)
  ·
    refine ⟨372988817889213857340635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3978547390818281144966773 372988817889213857340635)
    ·
      refine ⟨559483226833820786010953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 372988817889213857340635 559483226833820786010953)
      ·
        refine ⟨419612420125365589508215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559483226833820786010953 419612420125365589508215)
        ·
          refine ⟨629418630188048384262323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 419612420125365589508215 629418630188048384262323)
          ·
            refine ⟨944127945282072576393485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629418630188048384262323 944127945282072576393485)
            ·
              refine ⟨354047979480777216147557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 944127945282072576393485 354047979480777216147557)
              ·
                refine ⟨66383996152645728027667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 354047979480777216147557 66383996152645728027667)
                ·
                  rfl

theorem cell19_218164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_218164 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218164 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218164 prefixEnd_218164 := by exact prefixLift 218164
  have htrace : WordTrace (prefixWord ++ tailWord_218164) baseStart_218164 baseEnd_218164 := by
    simpa [prefixWord, tailWord_218164, baseEnd_218164] using wordTrace_append hprefix tailTrace_218164
  have hstable : (prefixWord ++ tailWord_218164).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218164).length < 2 ^ (prefixWord ++ tailWord_218164).sum := by decide
  have hdescent : baseEnd_218164 < baseStart_218164 := by decide
  rcases family_descends (prefixWord ++ tailWord_218164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218263 : List Nat := [1, 1, 3, 3, 3, 1, 7]
def baseStart_218263 : Nat := 118140960795 + 218263 * 2 ^ 59
def prefixEnd_218263 : Nat := 4983230072969 + 3 ^ 40 * 218263 * 2
def baseEnd_218263 : Nat := 22138040117014277275799

theorem tailTrace_218263 : CollatzResearch.WordTrace tailWord_218263 prefixEnd_218263 22138040117014277275799 := by
  unfold tailWord_218263
  simp only [CollatzResearch.WordTrace]
  refine ⟨7960705608277902197787443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5307137072185268131858295 7960705608277902197787443)
  ·
    refine ⟨11941058412416853296681165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7960705608277902197787443 11941058412416853296681165)
    ·
      refine ⟨4477896904656319986255437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11941058412416853296681165 4477896904656319986255437)
      ·
        refine ⟨1679211339246119994845789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4477896904656319986255437 1679211339246119994845789)
        ·
          refine ⟨629704252217294998067171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1679211339246119994845789 629704252217294998067171)
          ·
            refine ⟨944556378325942497100757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 629704252217294998067171 944556378325942497100757)
            ·
              refine ⟨22138040117014277275799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 944556378325942497100757 22138040117014277275799)
              ·
                rfl

theorem cell19_218263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_218263 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218263 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218263 prefixEnd_218263 := by exact prefixLift 218263
  have htrace : WordTrace (prefixWord ++ tailWord_218263) baseStart_218263 baseEnd_218263 := by
    simpa [prefixWord, tailWord_218263, baseEnd_218263] using wordTrace_append hprefix tailTrace_218263
  have hstable : (prefixWord ++ tailWord_218263).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218263).length < 2 ^ (prefixWord ++ tailWord_218263).sum := by decide
  have hdescent : baseEnd_218263 < baseStart_218263 := by decide
  rcases family_descends (prefixWord ++ tailWord_218263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218301 : List Nat := [1, 4, 1, 2, 1, 1, 4, 5]
def baseStart_218301 : Nat := 118140960795 + 218301 * 2 ^ 59
def prefixEnd_218301 : Nat := 4983230072969 + 3 ^ 40 * 218301 * 2
def baseEnd_218301 : Nat := 66425683174670002982849

theorem tailTrace_218301 : CollatzResearch.WordTrace tailWord_218301 prefixEnd_218301 66425683174670002982849 := by
  unfold tailWord_218301
  simp only [CollatzResearch.WordTrace]
  refine ⟨7962091582140234687670757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5308061054760156458447171 7962091582140234687670757)
  ·
    refine ⟨1492892171651294003938267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7962091582140234687670757 1492892171651294003938267)
    ·
      refine ⟨2239338257476941005907401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1492892171651294003938267 2239338257476941005907401)
      ·
        refine ⟨1679503693107705754430551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2239338257476941005907401 1679503693107705754430551)
        ·
          refine ⟨2519255539661558631645827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1679503693107705754430551 2519255539661558631645827)
          ·
            refine ⟨3778883309492337947468741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2519255539661558631645827 3778883309492337947468741)
            ·
              refine ⟨708540620529813365150389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3778883309492337947468741 708540620529813365150389)
              ·
                refine ⟨66425683174670002982849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 708540620529813365150389 66425683174670002982849)
                ·
                  rfl

theorem cell19_218301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_218301 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218301 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218301 prefixEnd_218301 := by exact prefixLift 218301
  have htrace : WordTrace (prefixWord ++ tailWord_218301) baseStart_218301 baseEnd_218301 := by
    simpa [prefixWord, tailWord_218301, baseEnd_218301] using wordTrace_append hprefix tailTrace_218301
  have hstable : (prefixWord ++ tailWord_218301).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218301).length < 2 ^ (prefixWord ++ tailWord_218301).sum := by decide
  have hdescent : baseEnd_218301 < baseStart_218301 := by decide
  rcases family_descends (prefixWord ++ tailWord_218301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218318 : List Nat := [4, 1, 1, 1, 6, 6]
def baseStart_218318 : Nat := 118140960795 + 218318 * 2 ^ 59
def prefixEnd_218318 : Nat := 4983230072969 + 3 ^ 40 * 218318 * 2
def baseEnd_218318 : Nat := 7381206224091000067225

theorem tailTrace_218318 : CollatzResearch.WordTrace tailWord_218318 prefixEnd_218318 7381206224091000067225 := by
  unfold tailWord_218318
  simp only [CollatzResearch.WordTrace]
  refine ⟨995338952884830823879951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5308474415385764394026405 995338952884830823879951)
  ·
    refine ⟨1493008429327246235819927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 995338952884830823879951 1493008429327246235819927)
    ·
      refine ⟨2239512643990869353729891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493008429327246235819927 2239512643990869353729891)
      ·
        refine ⟨3359268965986304030594837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2239512643990869353729891 3359268965986304030594837)
        ·
          refine ⟨157465732780608001434133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3359268965986304030594837 157465732780608001434133)
          ·
            refine ⟨7381206224091000067225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157465732780608001434133 7381206224091000067225)
            ·
              rfl

theorem cell19_218318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 6, 6].length) (baseStart_218318 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218318 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218318 prefixEnd_218318 := by exact prefixLift 218318
  have htrace : WordTrace (prefixWord ++ tailWord_218318) baseStart_218318 baseEnd_218318 := by
    simpa [prefixWord, tailWord_218318, baseEnd_218318] using wordTrace_append hprefix tailTrace_218318
  have hstable : (prefixWord ++ tailWord_218318).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218318).length < 2 ^ (prefixWord ++ tailWord_218318).sum := by decide
  have hdescent : baseEnd_218318 < baseStart_218318 := by decide
  rcases family_descends (prefixWord ++ tailWord_218318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218333 : List Nat := [1, 4, 3, 2, 3, 1, 1, 4]
def baseStart_218333 : Nat := 118140960795 + 218333 * 2 ^ 59
def prefixEnd_218333 : Nat := 4983230072969 + 3 ^ 40 * 218333 * 2
def baseEnd_218333 : Nat := 66435420289303410271651

theorem tailTrace_218333 : CollatzResearch.WordTrace tailWord_218333 prefixEnd_218333 66435420289303410271651 := by
  unfold tailWord_218333
  simp only [CollatzResearch.WordTrace]
  refine ⟨7963258718024304152835653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5308839145349536101890435 7963258718024304152835653)
  ·
    refine ⟨1493111009629557028656685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7963258718024304152835653 1493111009629557028656685)
    ·
      refine ⟨559916628611083885746257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1493111009629557028656685 559916628611083885746257)
      ·
        refine ⟨419937471458312914309693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 559916628611083885746257 419937471458312914309693)
        ·
          refine ⟨157476551796867342866135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 419937471458312914309693 157476551796867342866135)
          ·
            refine ⟨236214827695301014299203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157476551796867342866135 236214827695301014299203)
            ·
              refine ⟨354322241542951521448805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236214827695301014299203 354322241542951521448805)
              ·
                refine ⟨66435420289303410271651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 354322241542951521448805 66435420289303410271651)
                ·
                  rfl

theorem cell19_218333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 4].length) (baseStart_218333 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218333 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218333 prefixEnd_218333 := by exact prefixLift 218333
  have htrace : WordTrace (prefixWord ++ tailWord_218333) baseStart_218333 baseEnd_218333 := by
    simpa [prefixWord, tailWord_218333, baseEnd_218333] using wordTrace_append hprefix tailTrace_218333
  have hstable : (prefixWord ++ tailWord_218333).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218333).length < 2 ^ (prefixWord ++ tailWord_218333).sum := by decide
  have hdescent : baseEnd_218333 < baseStart_218333 := by decide
  rcases family_descends (prefixWord ++ tailWord_218333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218337 : List Nat := [1, 2, 3, 1, 3, 4, 1, 4]
def baseStart_218337 : Nat := 118140960795 + 218337 * 2 ^ 59
def prefixEnd_218337 : Nat := 4983230072969 + 3 ^ 40 * 218337 * 2
def baseEnd_218337 : Nat := 66436637428632586182751

theorem tailTrace_218337 : CollatzResearch.WordTrace tailWord_218337 prefixEnd_218337 66436637428632586182751 := by
  unfold tailWord_218337
  simp only [CollatzResearch.WordTrace]
  refine ⟨7963404610009812835981265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5308936406673208557320843 7963404610009812835981265)
  ·
    refine ⟨5972553457507359626985949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7963404610009812835981265 5972553457507359626985949)
    ·
      refine ⟨2239707546565259860119731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5972553457507359626985949 2239707546565259860119731)
      ·
        refine ⟨3359561319847889790179597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2239707546565259860119731 3359561319847889790179597)
        ·
          refine ⟨1259835494942958671317349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3359561319847889790179597 1259835494942958671317349)
          ·
            refine ⟨236219155301804750872003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1259835494942958671317349 236219155301804750872003)
            ·
              refine ⟨354328732952707126308005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236219155301804750872003 354328732952707126308005)
              ·
                refine ⟨66436637428632586182751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 354328732952707126308005 66436637428632586182751)
                ·
                  rfl

theorem cell19_218337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 4].length) (baseStart_218337 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218337 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218337 prefixEnd_218337 := by exact prefixLift 218337
  have htrace : WordTrace (prefixWord ++ tailWord_218337) baseStart_218337 baseEnd_218337 := by
    simpa [prefixWord, tailWord_218337, baseEnd_218337] using wordTrace_append hprefix tailTrace_218337
  have hstable : (prefixWord ++ tailWord_218337).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218337).length < 2 ^ (prefixWord ++ tailWord_218337).sum := by decide
  have hdescent : baseEnd_218337 < baseStart_218337 := by decide
  rcases family_descends (prefixWord ++ tailWord_218337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218354 : List Nat := [3, 2, 1, 3, 3, 1, 3, 3]
def baseStart_218354 : Nat := 118140960795 + 218354 * 2 ^ 59
def prefixEnd_218354 : Nat := 4983230072969 + 3 ^ 40 * 218354 * 2
def baseEnd_218354 : Nat := 66441810270781583804927

theorem tailTrace_218354 : CollatzResearch.WordTrace tailWord_218354 prefixEnd_218354 66441810270781583804927 := by
  unfold tailWord_218354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1991006162737056184837529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5309349767298816492900077 1991006162737056184837529)
  ·
    refine ⟨1493254622052792138628147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1991006162737056184837529 1493254622052792138628147)
    ·
      refine ⟨2239881933079188207942221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1493254622052792138628147 2239881933079188207942221)
      ·
        refine ⟨839955724904695577978333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2239881933079188207942221 839955724904695577978333)
        ·
          refine ⟨314983396839260841741875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 839955724904695577978333 314983396839260841741875)
          ·
            refine ⟨472475095258891262612813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 314983396839260841741875 472475095258891262612813)
            ·
              refine ⟨177178160722084223479805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 472475095258891262612813 177178160722084223479805)
              ·
                refine ⟨66441810270781583804927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177178160722084223479805 66441810270781583804927)
                ·
                  rfl

theorem cell19_218354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_218354 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218354 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218354 prefixEnd_218354 := by exact prefixLift 218354
  have htrace : WordTrace (prefixWord ++ tailWord_218354) baseStart_218354 baseEnd_218354 := by
    simpa [prefixWord, tailWord_218354, baseEnd_218354] using wordTrace_append hprefix tailTrace_218354
  have hstable : (prefixWord ++ tailWord_218354).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218354).length < 2 ^ (prefixWord ++ tailWord_218354).sum := by decide
  have hdescent : baseEnd_218354 < baseStart_218354 := by decide
  rcases family_descends (prefixWord ++ tailWord_218354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218453 : List Nat := [1, 3, 2, 2, 3, 1, 1, 6]
def baseStart_218453 : Nat := 118140960795 + 218453 * 2 ^ 59
def prefixEnd_218453 : Nat := 4983230072969 + 3 ^ 40 * 218453 * 2
def baseEnd_218453 : Nat := 66471934469178687604657

theorem tailTrace_218453 : CollatzResearch.WordTrace tailWord_218453 prefixEnd_218453 66471934469178687604657 := by
  unfold tailWord_218453
  simp only [CollatzResearch.WordTrace]
  refine ⟨7967635477589564647204013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5311756985059709764802675 7967635477589564647204013)
  ·
    refine ⟨2987863304096086742701505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7967635477589564647204013 2987863304096086742701505)
    ·
      refine ⟨2240897478072065057026129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2987863304096086742701505 2240897478072065057026129)
      ·
        refine ⟨1680673108554048792769597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2240897478072065057026129 1680673108554048792769597)
        ·
          refine ⟨630252415707768297288599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1680673108554048792769597 630252415707768297288599)
          ·
            refine ⟨945378623561652445932899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630252415707768297288599 945378623561652445932899)
            ·
              refine ⟨1418067935342478668899349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 945378623561652445932899 1418067935342478668899349)
              ·
                refine ⟨66471934469178687604657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1418067935342478668899349 66471934469178687604657)
                ·
                  rfl

theorem cell19_218453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 6].length) (baseStart_218453 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218453 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218453 prefixEnd_218453 := by exact prefixLift 218453
  have htrace : WordTrace (prefixWord ++ tailWord_218453) baseStart_218453 baseEnd_218453 := by
    simpa [prefixWord, tailWord_218453, baseEnd_218453] using wordTrace_append hprefix tailTrace_218453
  have hstable : (prefixWord ++ tailWord_218453).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218453).length < 2 ^ (prefixWord ++ tailWord_218453).sum := by decide
  have hdescent : baseEnd_218453 < baseStart_218453 := by decide
  rcases family_descends (prefixWord ++ tailWord_218453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218527 : List Nat := [1, 1, 2, 5, 1, 3, 3, 3]
def baseStart_218527 : Nat := 118140960795 + 218527 * 2 ^ 59
def prefixEnd_218527 : Nat := 4983230072969 + 3 ^ 40 * 218527 * 2
def baseEnd_218527 : Nat := 66494451546768441960011

theorem tailTrace_218527 : CollatzResearch.WordTrace tailWord_218527 prefixEnd_218527 66494451546768441960011 := by
  unfold tailWord_218527
  simp only [CollatzResearch.WordTrace]
  refine ⟨7970334479321475285397835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5313556319547650190265223 7970334479321475285397835)
  ·
    refine ⟨11955501718982212928096753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7970334479321475285397835 11955501718982212928096753)
    ·
      refine ⟨8966626289236659696072565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11955501718982212928096753 8966626289236659696072565)
      ·
        refine ⟨840621214615936846506803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8966626289236659696072565 840621214615936846506803)
        ·
          refine ⟨1260931821923905269760205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840621214615936846506803 1260931821923905269760205)
          ·
            refine ⟨472849433221464476160077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1260931821923905269760205 472849433221464476160077)
            ·
              refine ⟨177318537458049178560029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 472849433221464476160077 177318537458049178560029)
              ·
                refine ⟨66494451546768441960011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177318537458049178560029 66494451546768441960011)
                ·
                  rfl

theorem cell19_218527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 3].length) (baseStart_218527 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218527 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218527 prefixEnd_218527 := by exact prefixLift 218527
  have htrace : WordTrace (prefixWord ++ tailWord_218527) baseStart_218527 baseEnd_218527 := by
    simpa [prefixWord, tailWord_218527, baseEnd_218527] using wordTrace_append hprefix tailTrace_218527
  have hstable : (prefixWord ++ tailWord_218527).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218527).length < 2 ^ (prefixWord ++ tailWord_218527).sum := by decide
  have hdescent : baseEnd_218527 < baseStart_218527 := by decide
  rcases family_descends (prefixWord ++ tailWord_218527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218569 : List Nat := [1, 2, 1, 1, 2, 1, 3, 8]
def baseStart_218569 : Nat := 118140960795 + 218569 * 2 ^ 59
def prefixEnd_218569 : Nat := 4983230072969 + 3 ^ 40 * 218569 * 2
def baseEnd_218569 : Nat := 66507231509724789026563

theorem tailTrace_218569 : CollatzResearch.WordTrace tailWord_218569 prefixEnd_218569 66507231509724789026563 := by
  unfold tailWord_218569
  simp only [CollatzResearch.WordTrace]
  refine ⟨7971866345169316458426761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5314577563446210972284507 7971866345169316458426761)
  ·
    refine ⟨5978899758876987343820071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7971866345169316458426761 5978899758876987343820071)
    ·
      refine ⟨8968349638315481015730107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5978899758876987343820071 8968349638315481015730107)
      ·
        refine ⟨13452524457473221523595161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8968349638315481015730107 13452524457473221523595161)
        ·
          refine ⟨10089393343104916142696371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13452524457473221523595161 10089393343104916142696371)
          ·
            refine ⟨15134090014657374214044557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10089393343104916142696371 15134090014657374214044557)
            ·
              refine ⟨5675283755496515330266709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15134090014657374214044557 5675283755496515330266709)
              ·
                refine ⟨66507231509724789026563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5675283755496515330266709 66507231509724789026563)
                ·
                  rfl

theorem cell19_218569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 8].length) (baseStart_218569 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218569 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218569 prefixEnd_218569 := by exact prefixLift 218569
  have htrace : WordTrace (prefixWord ++ tailWord_218569) baseStart_218569 baseEnd_218569 := by
    simpa [prefixWord, tailWord_218569, baseEnd_218569] using wordTrace_append hprefix tailTrace_218569
  have hstable : (prefixWord ++ tailWord_218569).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218569).length < 2 ^ (prefixWord ++ tailWord_218569).sum := by decide
  have hdescent : baseEnd_218569 < baseStart_218569 := by decide
  rcases family_descends (prefixWord ++ tailWord_218569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218580 : List Nat := [2, 4, 1, 2, 4, 1, 2, 3]
def baseStart_218580 : Nat := 118140960795 + 218580 * 2 ^ 59
def prefixEnd_218580 : Nat := 4983230072969 + 3 ^ 40 * 218580 * 2
def baseEnd_218580 : Nat := 66510578642880022782089

theorem tailTrace_218580 : CollatzResearch.WordTrace tailWord_218580 prefixEnd_218580 66510578642880022782089 := by
  unfold tailWord_218580
  simp only [CollatzResearch.WordTrace]
  refine ⟨3986133774064732668538597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5314845032086310224718129 3986133774064732668538597)
  ·
    refine ⟨747400082637137375350987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3986133774064732668538597 747400082637137375350987)
    ·
      refine ⟨1121100123955706063026481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 747400082637137375350987 1121100123955706063026481)
      ·
        refine ⟨840825092966779547269861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1121100123955706063026481 840825092966779547269861)
        ·
          refine ⟨157654704931271165113099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 840825092966779547269861 157654704931271165113099)
          ·
            refine ⟨236482057396906747669649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157654704931271165113099 236482057396906747669649)
            ·
              refine ⟨177361543047680060752237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236482057396906747669649 177361543047680060752237)
              ·
                refine ⟨66510578642880022782089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177361543047680060752237 66510578642880022782089)
                ·
                  rfl

theorem cell19_218580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 3].length) (baseStart_218580 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218580 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218580 prefixEnd_218580 := by exact prefixLift 218580
  have htrace : WordTrace (prefixWord ++ tailWord_218580) baseStart_218580 baseEnd_218580 := by
    simpa [prefixWord, tailWord_218580, baseEnd_218580] using wordTrace_append hprefix tailTrace_218580
  have hstable : (prefixWord ++ tailWord_218580).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218580).length < 2 ^ (prefixWord ++ tailWord_218580).sum := by decide
  have hdescent : baseEnd_218580 < baseStart_218580 := by decide
  rcases family_descends (prefixWord ++ tailWord_218580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218582 : List Nat := [5, 2, 1, 1, 1, 2, 4, 3]
def baseStart_218582 : Nat := 118140960795 + 218582 * 2 ^ 59
def prefixEnd_218582 : Nat := 4983230072969 + 3 ^ 40 * 218582 * 2
def baseEnd_218582 : Nat := 66511187212544610737639

theorem tailTrace_218582 : CollatzResearch.WordTrace tailWord_218582 prefixEnd_218582 66511187212544610737639 := by
  unfold tailWord_218582
  simp only [CollatzResearch.WordTrace]
  refine ⟨498271280882638729915625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5314893662748146452433333 498271280882638729915625)
  ·
    refine ⟨373703460661979047436719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 498271280882638729915625 373703460661979047436719)
    ·
      refine ⟨560555190992968571155079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373703460661979047436719 560555190992968571155079)
      ·
        refine ⟨840832786489452856732619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560555190992968571155079 840832786489452856732619)
        ·
          refine ⟨1261249179734179285098929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 840832786489452856732619 1261249179734179285098929)
          ·
            refine ⟨945936884800634463824197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261249179734179285098929 945936884800634463824197)
            ·
              refine ⟨177363165900118961967037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 945936884800634463824197 177363165900118961967037)
              ·
                refine ⟨66511187212544610737639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177363165900118961967037 66511187212544610737639)
                ·
                  rfl

theorem cell19_218582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_218582 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218582 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218582 prefixEnd_218582 := by exact prefixLift 218582
  have htrace : WordTrace (prefixWord ++ tailWord_218582) baseStart_218582 baseEnd_218582 := by
    simpa [prefixWord, tailWord_218582, baseEnd_218582] using wordTrace_append hprefix tailTrace_218582
  have hstable : (prefixWord ++ tailWord_218582).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218582).length < 2 ^ (prefixWord ++ tailWord_218582).sum := by decide
  have hdescent : baseEnd_218582 < baseStart_218582 := by decide
  rcases family_descends (prefixWord ++ tailWord_218582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218586 : List Nat := [3, 1, 1, 2, 3, 3, 1, 5]
def baseStart_218586 : Nat := 118140960795 + 218586 * 2 ^ 59
def prefixEnd_218586 : Nat := 4983230072969 + 3 ^ 40 * 218586 * 2
def baseEnd_218586 : Nat := 66512404351873786648739

theorem tailTrace_218586 : CollatzResearch.WordTrace tailWord_218586 prefixEnd_218586 66512404351873786648739 := by
  unfold tailWord_218586
  simp only [CollatzResearch.WordTrace]
  refine ⟨1993121596526932090448903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5314990924071818907863741 1993121596526932090448903)
  ·
    refine ⟨2989682394790398135673355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1993121596526932090448903 2989682394790398135673355)
    ·
      refine ⟨4484523592185597203510033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2989682394790398135673355 4484523592185597203510033)
      ·
        refine ⟨3363392694139197902632525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4484523592185597203510033 3363392694139197902632525)
        ·
          refine ⟨1261272260302199213487197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3363392694139197902632525 1261272260302199213487197)
          ·
            refine ⟨472977097613324705057699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1261272260302199213487197 472977097613324705057699)
            ·
              refine ⟨709465646419987057586549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 472977097613324705057699 709465646419987057586549)
              ·
                refine ⟨66512404351873786648739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 709465646419987057586549 66512404351873786648739)
                ·
                  rfl

theorem cell19_218586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 5].length) (baseStart_218586 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218586 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218586 prefixEnd_218586 := by exact prefixLift 218586
  have htrace : WordTrace (prefixWord ++ tailWord_218586) baseStart_218586 baseEnd_218586 := by
    simpa [prefixWord, tailWord_218586, baseEnd_218586] using wordTrace_append hprefix tailTrace_218586
  have hstable : (prefixWord ++ tailWord_218586).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218586).length < 2 ^ (prefixWord ++ tailWord_218586).sum := by decide
  have hdescent : baseEnd_218586 < baseStart_218586 := by decide
  rcases family_descends (prefixWord ++ tailWord_218586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218607 : List Nat := [1, 1, 2, 1, 4, 1, 9]
def baseStart_218607 : Nat := 118140960795 + 218607 * 2 ^ 59
def prefixEnd_218607 : Nat := 4983230072969 + 3 ^ 40 * 218607 * 2
def baseEnd_218607 : Nat := 22172931444450653394005

theorem tailTrace_218607 : CollatzResearch.WordTrace tailWord_218607 prefixEnd_218607 22172931444450653394005 := by
  unfold tailWord_218607
  simp only [CollatzResearch.WordTrace]
  refine ⟨7973252319031648948310075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5315501546021099298873383 7973252319031648948310075)
  ·
    refine ⟨11959878478547473422465113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7973252319031648948310075 11959878478547473422465113)
    ·
      refine ⟨8969908858910605066848835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11959878478547473422465113 8969908858910605066848835)
      ·
        refine ⟨13454863288365907600273253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8969908858910605066848835 13454863288365907600273253)
        ·
          refine ⟨2522786866568607675051235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13454863288365907600273253 2522786866568607675051235)
          ·
            refine ⟨3784180299852911512576853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2522786866568607675051235 3784180299852911512576853)
            ·
              refine ⟨22172931444450653394005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3784180299852911512576853 22172931444450653394005)
              ·
                rfl

theorem cell19_218607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 9].length) (baseStart_218607 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218607 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218607 prefixEnd_218607 := by exact prefixLift 218607
  have htrace : WordTrace (prefixWord ++ tailWord_218607) baseStart_218607 baseEnd_218607 := by
    simpa [prefixWord, tailWord_218607, baseEnd_218607] using wordTrace_append hprefix tailTrace_218607
  have hstable : (prefixWord ++ tailWord_218607).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218607).length < 2 ^ (prefixWord ++ tailWord_218607).sum := by decide
  have hdescent : baseEnd_218607 < baseStart_218607 := by decide
  rcases family_descends (prefixWord ++ tailWord_218607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218681 : List Nat := [1, 2, 1, 5, 1, 2, 3, 4]
def baseStart_218681 : Nat := 118140960795 + 218681 * 2 ^ 59
def prefixEnd_218681 : Nat := 4983230072969 + 3 ^ 40 * 218681 * 2
def baseEnd_218681 : Nat := 66541311410941714537369

theorem tailTrace_218681 : CollatzResearch.WordTrace tailWord_218681 prefixEnd_218681 66541311410941714537369 := by
  unfold tailWord_218681
  simp only [CollatzResearch.WordTrace]
  refine ⟨7975951320763559586503897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5317300880509039724335931 7975951320763559586503897)
  ·
    refine ⟨5981963490572669689877923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7975951320763559586503897 5981963490572669689877923)
    ·
      refine ⟨8972945235859004534816885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5981963490572669689877923 8972945235859004534816885)
      ·
        refine ⟨841213615861781675139083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8972945235859004534816885 841213615861781675139083)
        ·
          refine ⟨1261820423792672512708625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841213615861781675139083 1261820423792672512708625)
          ·
            refine ⟨946365317844504384531469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261820423792672512708625 946365317844504384531469)
            ·
              refine ⟨354886994191689144199301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946365317844504384531469 354886994191689144199301)
              ·
                refine ⟨66541311410941714537369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 354886994191689144199301 66541311410941714537369)
                ·
                  rfl

theorem cell19_218681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 3, 4].length) (baseStart_218681 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218681 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218681 prefixEnd_218681 := by exact prefixLift 218681
  have htrace : WordTrace (prefixWord ++ tailWord_218681) baseStart_218681 baseEnd_218681 := by
    simpa [prefixWord, tailWord_218681, baseEnd_218681] using wordTrace_append hprefix tailTrace_218681
  have hstable : (prefixWord ++ tailWord_218681).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218681).length < 2 ^ (prefixWord ++ tailWord_218681).sum := by decide
  have hdescent : baseEnd_218681 < baseStart_218681 := by decide
  rcases family_descends (prefixWord ++ tailWord_218681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218694 : List Nat := [6, 1, 1, 1, 3, 1, 3, 3]
def baseStart_218694 : Nat := 118140960795 + 218694 * 2 ^ 59
def prefixEnd_218694 : Nat := 4983230072969 + 3 ^ 40 * 218694 * 2
def baseEnd_218694 : Nat := 66545267113761536248445

theorem tailTrace_218694 : CollatzResearch.WordTrace tailWord_218694 prefixEnd_218694 66545267113761536248445 := by
  unfold tailWord_218694
  simp only [CollatzResearch.WordTrace]
  refine ⟨249263295928639462710223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 5317616979810975204484757 249263295928639462710223)
  ·
    refine ⟨373894943892959194065335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249263295928639462710223 373894943892959194065335)
    ·
      refine ⟨560842415839438791098003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373894943892959194065335 560842415839438791098003)
      ·
        refine ⟨841263623759158186647005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560842415839438791098003 841263623759158186647005)
        ·
          refine ⟨315473858909684319992627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 841263623759158186647005 315473858909684319992627)
          ·
            refine ⟨473210788364526479988941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315473858909684319992627 473210788364526479988941)
            ·
              refine ⟨177454045636697429995853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473210788364526479988941 177454045636697429995853)
              ·
                refine ⟨66545267113761536248445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177454045636697429995853 66545267113761536248445)
                ·
                  rfl

theorem cell19_218694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_218694 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218694 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218694 prefixEnd_218694 := by exact prefixLift 218694
  have htrace : WordTrace (prefixWord ++ tailWord_218694) baseStart_218694 baseEnd_218694 := by
    simpa [prefixWord, tailWord_218694, baseEnd_218694] using wordTrace_append hprefix tailTrace_218694
  have hstable : (prefixWord ++ tailWord_218694).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218694).length < 2 ^ (prefixWord ++ tailWord_218694).sum := by decide
  have hdescent : baseEnd_218694 < baseStart_218694 := by decide
  rcases family_descends (prefixWord ++ tailWord_218694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218721 : List Nat := [1, 2, 3, 1, 1, 3, 8]
def baseStart_218721 : Nat := 118140960795 + 218721 * 2 ^ 59
def prefixEnd_218721 : Nat := 4983230072969 + 3 ^ 40 * 218721 * 2
def baseEnd_218721 : Nat := 22184494268077824549457

theorem tailTrace_218721 : CollatzResearch.WordTrace tailWord_218721 prefixEnd_218721 22184494268077824549457 := by
  unfold tailWord_218721
  simp only [CollatzResearch.WordTrace]
  refine ⟨7977410240618646417960017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5318273493745764278640011 7977410240618646417960017)
  ·
    refine ⟨5983057680463984813470013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7977410240618646417960017 5983057680463984813470013)
    ·
      refine ⟨2243646630173994305051255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5983057680463984813470013 2243646630173994305051255)
      ·
        refine ⟨3365469945260991457576883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2243646630173994305051255 3365469945260991457576883)
        ·
          refine ⟨5048204917891487186365325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3365469945260991457576883 5048204917891487186365325)
          ·
            refine ⟨1893076844209307694886997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5048204917891487186365325 1893076844209307694886997)
            ·
              refine ⟨22184494268077824549457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1893076844209307694886997 22184494268077824549457)
              ·
                rfl

theorem cell19_218721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_218721 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218721 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218721 prefixEnd_218721 := by exact prefixLift 218721
  have htrace : WordTrace (prefixWord ++ tailWord_218721) baseStart_218721 baseEnd_218721 := by
    simpa [prefixWord, tailWord_218721, baseEnd_218721] using wordTrace_append hprefix tailTrace_218721
  have hstable : (prefixWord ++ tailWord_218721).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218721).length < 2 ^ (prefixWord ++ tailWord_218721).sum := by decide
  have hdescent : baseEnd_218721 < baseStart_218721 := by decide
  rcases family_descends (prefixWord ++ tailWord_218721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218772 : List Nat := [2, 4, 2, 2, 3, 1, 5]
def baseStart_218772 : Nat := 118140960795 + 218772 * 2 ^ 59
def prefixEnd_218772 : Nat := 4983230072969 + 3 ^ 40 * 218772 * 2
def baseEnd_218772 : Nat := 22189667110226822171633

theorem tailTrace_218772 : CollatzResearch.WordTrace tailWord_218772 prefixEnd_218772 22189667110226822171633 := by
  unfold tailWord_218772
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989635181716941064033285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5319513575622588085377713 3989635181716941064033285)
  ·
    refine ⟨748056596571926449506241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3989635181716941064033285 748056596571926449506241)
    ·
      refine ⟨561042447428944837129681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 748056596571926449506241 561042447428944837129681)
      ·
        refine ⟨420781835571708627847261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561042447428944837129681 420781835571708627847261)
        ·
          refine ⟨157793188339390735442723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 420781835571708627847261 157793188339390735442723)
          ·
            refine ⟨236689782509086103164085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157793188339390735442723 236689782509086103164085)
            ·
              refine ⟨22189667110226822171633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236689782509086103164085 22189667110226822171633)
              ·
                rfl

theorem cell19_218772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 3, 1, 5].length) (baseStart_218772 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218772 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218772 prefixEnd_218772 := by exact prefixLift 218772
  have htrace : WordTrace (prefixWord ++ tailWord_218772) baseStart_218772 baseEnd_218772 := by
    simpa [prefixWord, tailWord_218772, baseEnd_218772] using wordTrace_append hprefix tailTrace_218772
  have hstable : (prefixWord ++ tailWord_218772).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218772).length < 2 ^ (prefixWord ++ tailWord_218772).sum := by decide
  have hdescent : baseEnd_218772 < baseStart_218772 := by decide
  rcases family_descends (prefixWord ++ tailWord_218772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218776 : List Nat := [2, 1, 2, 4, 1, 4, 5]
def baseStart_218776 : Nat := 118140960795 + 218776 * 2 ^ 59
def prefixEnd_218776 : Nat := 4983230072969 + 3 ^ 40 * 218776 * 2
def baseEnd_218776 : Nat := 22190072823336547475333

theorem tailTrace_218776 : CollatzResearch.WordTrace tailWord_218776 prefixEnd_218776 22190072823336547475333 := by
  unfold tailWord_218776
  simp only [CollatzResearch.WordTrace]
  refine ⟨3989708127709695405606091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5319610836946260540808121 3989708127709695405606091)
  ·
    refine ⟨5984562191564543108409137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3989708127709695405606091 5984562191564543108409137)
    ·
      refine ⟨4488421643673407331306853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5984562191564543108409137 4488421643673407331306853)
      ·
        refine ⟨841579058188763874620035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4488421643673407331306853 841579058188763874620035)
        ·
          refine ⟨1262368587283145811930053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841579058188763874620035 1262368587283145811930053)
          ·
            refine ⟨236694110115589839736885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1262368587283145811930053 236694110115589839736885)
            ·
              refine ⟨22190072823336547475333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236694110115589839736885 22190072823336547475333)
              ·
                rfl

theorem cell19_218776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 5].length) (baseStart_218776 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218776 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218776 prefixEnd_218776 := by exact prefixLift 218776
  have htrace : WordTrace (prefixWord ++ tailWord_218776) baseStart_218776 baseEnd_218776 := by
    simpa [prefixWord, tailWord_218776, baseEnd_218776] using wordTrace_append hprefix tailTrace_218776
  have hstable : (prefixWord ++ tailWord_218776).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218776).length < 2 ^ (prefixWord ++ tailWord_218776).sum := by decide
  have hdescent : baseEnd_218776 < baseStart_218776 := by decide
  rcases family_descends (prefixWord ++ tailWord_218776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218814 : List Nat := [4, 2, 1, 1, 2, 2, 2, 5]
def baseStart_218814 : Nat := 118140960795 + 218814 * 2 ^ 59
def prefixEnd_218814 : Nat := 4983230072969 + 3 ^ 40 * 218814 * 2
def baseEnd_218814 : Nat := 66581781293636813581451

theorem tailTrace_218814 : CollatzResearch.WordTrace tailWord_218814 prefixEnd_218814 66581781293636813581451 := by
  unfold tailWord_218814
  simp only [CollatzResearch.WordTrace]
  refine ⟨997600278660215412636937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5320534819521148867396997 997600278660215412636937)
  ·
    refine ⟨748200208995161559477703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 997600278660215412636937 748200208995161559477703)
    ·
      refine ⟨1122300313492742339216555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 748200208995161559477703 1122300313492742339216555)
      ·
        refine ⟨1683450470239113508824833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1122300313492742339216555 1683450470239113508824833)
        ·
          refine ⟨1262587852679335131618625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1683450470239113508824833 1262587852679335131618625)
          ·
            refine ⟨946940889509501348713969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1262587852679335131618625 946940889509501348713969)
            ·
              refine ⟨710205667132126011535477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 946940889509501348713969 710205667132126011535477)
              ·
                refine ⟨66581781293636813581451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 710205667132126011535477 66581781293636813581451)
                ·
                  rfl

theorem cell19_218814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_218814 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218814 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218814 prefixEnd_218814 := by exact prefixLift 218814
  have htrace : WordTrace (prefixWord ++ tailWord_218814) baseStart_218814 baseEnd_218814 := by
    simpa [prefixWord, tailWord_218814, baseEnd_218814] using wordTrace_append hprefix tailTrace_218814
  have hstable : (prefixWord ++ tailWord_218814).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218814).length < 2 ^ (prefixWord ++ tailWord_218814).sum := by decide
  have hdescent : baseEnd_218814 < baseStart_218814 := by decide
  rcases family_descends (prefixWord ++ tailWord_218814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218816 : List Nat := [2, 1, 1, 2, 4, 1, 1, 7]
def baseStart_218816 : Nat := 118140960795 + 218816 * 2 ^ 59
def prefixEnd_218816 : Nat := 4983230072969 + 3 ^ 40 * 218816 * 2
def baseEnd_218816 : Nat := 66582389863301401537001

theorem tailTrace_218816 : CollatzResearch.WordTrace tailWord_218816 prefixEnd_218816 66582389863301401537001 := by
  unfold tailWord_218816
  simp only [CollatzResearch.WordTrace]
  refine ⟨3990437587637238821334151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5320583450182985095112201 3990437587637238821334151)
  ·
    refine ⟨5985656381455858232001227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3990437587637238821334151 5985656381455858232001227)
    ·
      refine ⟨8978484572183787348001841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5985656381455858232001227 8978484572183787348001841)
      ·
        refine ⟨6733863429137840511001381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8978484572183787348001841 6733863429137840511001381)
        ·
          refine ⟨1262599392963345095812759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6733863429137840511001381 1262599392963345095812759)
          ·
            refine ⟨1893899089445017643719139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1262599392963345095812759 1893899089445017643719139)
            ·
              refine ⟨2840848634167526465578709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1893899089445017643719139 2840848634167526465578709)
              ·
                refine ⟨66582389863301401537001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2840848634167526465578709 66582389863301401537001)
                ·
                  rfl

theorem cell19_218816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 7].length) (baseStart_218816 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218816 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218816 prefixEnd_218816 := by exact prefixLift 218816
  have htrace : WordTrace (prefixWord ++ tailWord_218816) baseStart_218816 baseEnd_218816 := by
    simpa [prefixWord, tailWord_218816, baseEnd_218816] using wordTrace_append hprefix tailTrace_218816
  have hstable : (prefixWord ++ tailWord_218816).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218816).length < 2 ^ (prefixWord ++ tailWord_218816).sum := by decide
  have hdescent : baseEnd_218816 < baseStart_218816 := by decide
  rcases family_descends (prefixWord ++ tailWord_218816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218911 : List Nat := [1, 1, 2, 4, 2, 1, 2, 6]
def baseStart_218911 : Nat := 118140960795 + 218911 * 2 ^ 59
def prefixEnd_218911 : Nat := 4983230072969 + 3 ^ 40 * 218911 * 2
def baseEnd_218911 : Nat := 66611296922369329425631

theorem tailTrace_218911 : CollatzResearch.WordTrace tailWord_218911 prefixEnd_218911 66611296922369329425631 := by
  unfold tailWord_218911
  simp only [CollatzResearch.WordTrace]
  refine ⟨7984340109930308867376587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5322893406620205911584391 7984340109930308867376587)
  ·
    refine ⟨11976510164895463301064881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7984340109930308867376587 11976510164895463301064881)
    ·
      refine ⟨8982382623671597475798661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11976510164895463301064881 8982382623671597475798661)
      ·
        refine ⟨1684196741938424526712249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8982382623671597475798661 1684196741938424526712249)
        ·
          refine ⟨1263147556453818395034187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1684196741938424526712249 1263147556453818395034187)
          ·
            refine ⟨1894721334680727592551281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1263147556453818395034187 1894721334680727592551281)
            ·
              refine ⟨1421041001010545694413461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1894721334680727592551281 1421041001010545694413461)
              ·
                refine ⟨66611296922369329425631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1421041001010545694413461 66611296922369329425631)
                ·
                  rfl

theorem cell19_218911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 6].length) (baseStart_218911 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218911 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218911 prefixEnd_218911 := by exact prefixLift 218911
  have htrace : WordTrace (prefixWord ++ tailWord_218911) baseStart_218911 baseEnd_218911 := by
    simpa [prefixWord, tailWord_218911, baseEnd_218911] using wordTrace_append hprefix tailTrace_218911
  have hstable : (prefixWord ++ tailWord_218911).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218911).length < 2 ^ (prefixWord ++ tailWord_218911).sum := by decide
  have hdescent : baseEnd_218911 < baseStart_218911 := by decide
  rcases family_descends (prefixWord ++ tailWord_218911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_218926 : List Nat := [4, 1, 3, 2, 2, 1, 1, 5]
def baseStart_218926 : Nat := 118140960795 + 218926 * 2 ^ 59
def prefixEnd_218926 : Nat := 4983230072969 + 3 ^ 40 * 218926 * 2
def baseEnd_218926 : Nat := 66615861194853739092257

theorem tailTrace_218926 : CollatzResearch.WordTrace tailWord_218926 prefixEnd_218926 66615861194853739092257 := by
  unfold tailWord_218926
  simp only [CollatzResearch.WordTrace]
  refine ⟨998110900609495803646579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5323258136583977619448421 998110900609495803646579)
  ·
    refine ⟨1497166350914243705469869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 998110900609495803646579 1497166350914243705469869)
    ·
      refine ⟨561437381592841389551201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1497166350914243705469869 561437381592841389551201)
      ·
        refine ⟨421078036194631042163401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 561437381592841389551201 421078036194631042163401)
        ·
          refine ⟨315808527145973281622551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421078036194631042163401 315808527145973281622551)
          ·
            refine ⟨473712790718959922433827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315808527145973281622551 473712790718959922433827)
            ·
              refine ⟨710569186078439883650741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473712790718959922433827 710569186078439883650741)
              ·
                refine ⟨66615861194853739092257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 710569186078439883650741 66615861194853739092257)
                ·
                  rfl

theorem cell19_218926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_218926 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_218926 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_218926 prefixEnd_218926 := by exact prefixLift 218926
  have htrace : WordTrace (prefixWord ++ tailWord_218926) baseStart_218926 baseEnd_218926 := by
    simpa [prefixWord, tailWord_218926, baseEnd_218926] using wordTrace_append hprefix tailTrace_218926
  have hstable : (prefixWord ++ tailWord_218926).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_218926).length < 2 ^ (prefixWord ++ tailWord_218926).sum := by decide
  have hdescent : baseEnd_218926 < baseStart_218926 := by decide
  rcases family_descends (prefixWord ++ tailWord_218926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219025 : List Nat := [1, 2, 2, 1, 1, 1, 7, 4]
def baseStart_219025 : Nat := 118140960795 + 219025 * 2 ^ 59
def prefixEnd_219025 : Nat := 4983230072969 + 3 ^ 40 * 219025 * 2
def baseEnd_219025 : Nat := 66645985393250842891987

theorem tailTrace_219025 : CollatzResearch.WordTrace tailWord_219025 prefixEnd_219025 66645985393250842891987 := by
  unfold tailWord_219025
  simp only [CollatzResearch.WordTrace]
  refine ⟨7988498031517306337026529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5325665354344870891351019 7988498031517306337026529)
  ·
    refine ⟨5991373523637979752769897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7988498031517306337026529 5991373523637979752769897)
    ·
      refine ⟨4493530142728484814577423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5991373523637979752769897 4493530142728484814577423)
      ·
        refine ⟨6740295214092727221866135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4493530142728484814577423 6740295214092727221866135)
        ·
          refine ⟨10110442821139090832799203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6740295214092727221866135 10110442821139090832799203)
          ·
            refine ⟨15165664231708636249198805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10110442821139090832799203 15165664231708636249198805)
            ·
              refine ⟨355445255430671162090597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 15165664231708636249198805 355445255430671162090597)
              ·
                refine ⟨66645985393250842891987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355445255430671162090597 66645985393250842891987)
                ·
                  rfl

theorem cell19_219025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 7, 4].length) (baseStart_219025 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219025 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219025 prefixEnd_219025 := by exact prefixLift 219025
  have htrace : WordTrace (prefixWord ++ tailWord_219025) baseStart_219025 baseEnd_219025 := by
    simpa [prefixWord, tailWord_219025, baseEnd_219025] using wordTrace_append hprefix tailTrace_219025
  have hstable : (prefixWord ++ tailWord_219025).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219025).length < 2 ^ (prefixWord ++ tailWord_219025).sum := by decide
  have hdescent : baseEnd_219025 < baseStart_219025 := by decide
  rcases family_descends (prefixWord ++ tailWord_219025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219097 : List Nat := [1, 2, 1, 2, 6, 2, 2, 3]
def baseStart_219097 : Nat := 118140960795 + 219097 * 2 ^ 59
def prefixEnd_219097 : Nat := 4983230072969 + 3 ^ 40 * 219097 * 2
def baseEnd_219097 : Nat := 66667893901176009291791

theorem tailTrace_219097 : CollatzResearch.WordTrace tailWord_219097 prefixEnd_219097 66667893901176009291791 := by
  unfold tailWord_219097
  simp only [CollatzResearch.WordTrace]
  refine ⟨7991124087256462633647545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5327416058170975089098363 7991124087256462633647545)
  ·
    refine ⟨5993343065442346975235659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7991124087256462633647545 5993343065442346975235659)
    ·
      refine ⟨8990014598163520462853489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5993343065442346975235659 8990014598163520462853489)
      ·
        refine ⟨6742510948622640347140117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8990014598163520462853489 6742510948622640347140117)
        ·
          refine ⟨316055200716686266272193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 6742510948622640347140117 316055200716686266272193)
          ·
            refine ⟨237041400537514699704145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316055200716686266272193 237041400537514699704145)
            ·
              refine ⟨177781050403136024778109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237041400537514699704145 177781050403136024778109)
              ·
                refine ⟨66667893901176009291791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177781050403136024778109 66667893901176009291791)
                ·
                  rfl

theorem cell19_219097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 3].length) (baseStart_219097 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219097 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219097 prefixEnd_219097 := by exact prefixLift 219097
  have htrace : WordTrace (prefixWord ++ tailWord_219097) baseStart_219097 baseEnd_219097 := by
    simpa [prefixWord, tailWord_219097, baseEnd_219097] using wordTrace_append hprefix tailTrace_219097
  have hstable : (prefixWord ++ tailWord_219097).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219097).length < 2 ^ (prefixWord ++ tailWord_219097).sum := by decide
  have hdescent : baseEnd_219097 < baseStart_219097 := by decide
  rcases family_descends (prefixWord ++ tailWord_219097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219118 : List Nat := [4, 1, 2, 1, 3, 3, 5]
def baseStart_219118 : Nat := 118140960795 + 219118 * 2 ^ 59
def prefixEnd_219118 : Nat := 4983230072969 + 3 ^ 40 * 219118 * 2
def baseEnd_219118 : Nat := 22224761294218060941689

theorem tailTrace_219118 : CollatzResearch.WordTrace tailWord_219118 prefixEnd_219118 22224761294218060941689 := by
  unfold tailWord_219118
  simp only [CollatzResearch.WordTrace]
  refine ⟨998986252522547902520251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5327926680120255480108005 998986252522547902520251)
  ·
    refine ⟨1498479378783821853780377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 998986252522547902520251 1498479378783821853780377)
    ·
      refine ⟨1123859534087866390335283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1498479378783821853780377 1123859534087866390335283)
      ·
        refine ⟨1685789301131799585502925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1123859534087866390335283 1685789301131799585502925)
        ·
          refine ⟨632170987924424844563597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1685789301131799585502925 632170987924424844563597)
          ·
            refine ⟨237064120471659316711349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632170987924424844563597 237064120471659316711349)
            ·
              refine ⟨22224761294218060941689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237064120471659316711349 22224761294218060941689)
              ·
                rfl

theorem cell19_219118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 5].length) (baseStart_219118 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219118 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219118 prefixEnd_219118 := by exact prefixLift 219118
  have htrace : WordTrace (prefixWord ++ tailWord_219118) baseStart_219118 baseEnd_219118 := by
    simpa [prefixWord, tailWord_219118, baseEnd_219118] using wordTrace_append hprefix tailTrace_219118
  have hstable : (prefixWord ++ tailWord_219118).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219118).length < 2 ^ (prefixWord ++ tailWord_219118).sum := by decide
  have hdescent : baseEnd_219118 < baseStart_219118 := by decide
  rcases family_descends (prefixWord ++ tailWord_219118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219175 : List Nat := [1, 1, 7, 1, 2, 7]
def baseStart_219175 : Nat := 118140960795 + 219175 * 2 ^ 59
def prefixEnd_219175 : Nat := 4983230072969 + 3 ^ 40 * 219175 * 2
def baseEnd_219175 : Nat := 7410180902010548839805

theorem tailTrace_219175 : CollatzResearch.WordTrace tailWord_219175 prefixEnd_219175 7410180902010548839805 := by
  unfold tailWord_219175
  simp only [CollatzResearch.WordTrace]
  refine ⟨7993968980973881954986979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5329312653982587969991319 7993968980973881954986979)
  ·
    refine ⟨11990953471460822932480469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7993968980973881954986979 11990953471460822932480469)
    ·
      refine ⟨281037971987363037480011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11990953471460822932480469 281037971987363037480011)
      ·
        refine ⟨421556957981044556220017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281037971987363037480011 421556957981044556220017)
        ·
          refine ⟨316167718485783417165013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421556957981044556220017 316167718485783417165013)
          ·
            refine ⟨7410180902010548839805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 316167718485783417165013 7410180902010548839805)
            ·
              rfl

theorem cell19_219175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 7].length) (baseStart_219175 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219175 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219175 prefixEnd_219175 := by exact prefixLift 219175
  have htrace : WordTrace (prefixWord ++ tailWord_219175) baseStart_219175 baseEnd_219175 := by
    simpa [prefixWord, tailWord_219175, baseEnd_219175] using wordTrace_append hprefix tailTrace_219175
  have hstable : (prefixWord ++ tailWord_219175).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219175).length < 2 ^ (prefixWord ++ tailWord_219175).sum := by decide
  have hdescent : baseEnd_219175 < baseStart_219175 := by decide
  rcases family_descends (prefixWord ++ tailWord_219175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219192 : List Nat := [2, 1, 2, 1, 7, 1, 1, 4]
def baseStart_219192 : Nat := 118140960795 + 219192 * 2 ^ 59
def prefixEnd_219192 : Nat := 4983230072969 + 3 ^ 40 * 219192 * 2
def baseEnd_219192 : Nat := 66696800960243937180421

theorem tailTrace_219192 : CollatzResearch.WordTrace tailWord_219192 prefixEnd_219192 66696800960243937180421 := by
  unfold tailWord_219192
  simp only [CollatzResearch.WordTrace]
  refine ⟨3997294510956146929177915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5329726014608195905570553 3997294510956146929177915)
  ·
    refine ⟨5995941766434220393766873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3997294510956146929177915 5995941766434220393766873)
    ·
      refine ⟨4496956324825665295325155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5995941766434220393766873 4496956324825665295325155)
      ·
        refine ⟨6745434487238497942987733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4496956324825665295325155 6745434487238497942987733)
        ·
          refine ⟨158096120794652295538775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 6745434487238497942987733 158096120794652295538775)
          ·
            refine ⟨237144181191978443308163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158096120794652295538775 237144181191978443308163)
            ·
              refine ⟨355716271787967664962245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237144181191978443308163 355716271787967664962245)
              ·
                refine ⟨66696800960243937180421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355716271787967664962245 66696800960243937180421)
                ·
                  rfl

theorem cell19_219192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_219192 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219192 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219192 prefixEnd_219192 := by exact prefixLift 219192
  have htrace : WordTrace (prefixWord ++ tailWord_219192) baseStart_219192 baseEnd_219192 := by
    simpa [prefixWord, tailWord_219192, baseEnd_219192] using wordTrace_append hprefix tailTrace_219192
  have hstable : (prefixWord ++ tailWord_219192).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219192).length < 2 ^ (prefixWord ++ tailWord_219192).sum := by decide
  have hdescent : baseEnd_219192 < baseStart_219192 := by decide
  rcases family_descends (prefixWord ++ tailWord_219192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219306 : List Nat := [3, 1, 5, 1, 2, 1, 2, 4]
def baseStart_219306 : Nat := 118140960795 + 219306 * 2 ^ 59
def prefixEnd_219306 : Nat := 4983230072969 + 3 ^ 40 * 219306 * 2
def baseEnd_219306 : Nat := 66731489431125450646777

theorem tailTrace_219306 : CollatzResearch.WordTrace tailWord_219306 prefixEnd_219306 66731489431125450646777 := by
  unfold tailWord_219306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1999686735874822832001443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5332497962332860885337181 1999686735874822832001443)
  ·
    refine ⟨2999530103812234248002165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1999686735874822832001443 2999530103812234248002165)
    ·
      refine ⟨281205947232396960750203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2999530103812234248002165 281205947232396960750203)
      ·
        refine ⟨421808920848595441125305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281205947232396960750203 421808920848595441125305)
        ·
          refine ⟨316356690636446580843979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 421808920848595441125305 316356690636446580843979)
          ·
            refine ⟨474535035954669871265969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316356690636446580843979 474535035954669871265969)
            ·
              refine ⟨355901276966002403449477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 474535035954669871265969 355901276966002403449477)
              ·
                refine ⟨66731489431125450646777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355901276966002403449477 66731489431125450646777)
                ·
                  rfl

theorem cell19_219306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 2, 4].length) (baseStart_219306 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219306 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219306 prefixEnd_219306 := by exact prefixLift 219306
  have htrace : WordTrace (prefixWord ++ tailWord_219306) baseStart_219306 baseEnd_219306 := by
    simpa [prefixWord, tailWord_219306, baseEnd_219306] using wordTrace_append hprefix tailTrace_219306
  have hstable : (prefixWord ++ tailWord_219306).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219306).length < 2 ^ (prefixWord ++ tailWord_219306).sum := by decide
  have hdescent : baseEnd_219306 < baseStart_219306 := by decide
  rcases family_descends (prefixWord ++ tailWord_219306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219363 : List Nat := [1, 1, 1, 8, 1, 2, 1, 4]
def baseStart_219363 : Nat := 118140960795 + 219363 * 2 ^ 59
def prefixEnd_219363 : Nat := 4983230072969 + 3 ^ 40 * 219363 * 2
def baseEnd_219363 : Nat := 66748833666566207379955

theorem tailTrace_219363 : CollatzResearch.WordTrace tailWord_219363 prefixEnd_219363 66748833666566207379955 := by
  unfold tailWord_219363
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000825904292790062830743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5333883936195193375220495 8000825904292790062830743)
  ·
    refine ⟨12001238856439185094246115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8000825904292790062830743 12001238856439185094246115)
    ·
      refine ⟨18001858284658777641369173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12001238856439185094246115 18001858284658777641369173)
      ·
        refine ⟨210959276773345050484795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 18001858284658777641369173 210959276773345050484795)
        ·
          refine ⟨316438915160017575727193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210959276773345050484795 316438915160017575727193)
          ·
            refine ⟨237329186370013181795395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316438915160017575727193 237329186370013181795395)
            ·
              refine ⟨355993779555019772693093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237329186370013181795395 355993779555019772693093)
              ·
                refine ⟨66748833666566207379955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355993779555019772693093 66748833666566207379955)
                ·
                  rfl

theorem cell19_219363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 2, 1, 4].length) (baseStart_219363 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219363 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219363 prefixEnd_219363 := by exact prefixLift 219363
  have htrace : WordTrace (prefixWord ++ tailWord_219363) baseStart_219363 baseEnd_219363 := by
    simpa [prefixWord, tailWord_219363, baseEnd_219363] using wordTrace_append hprefix tailTrace_219363
  have hstable : (prefixWord ++ tailWord_219363).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219363).length < 2 ^ (prefixWord ++ tailWord_219363).sum := by decide
  have hdescent : baseEnd_219363 < baseStart_219363 := by decide
  rcases family_descends (prefixWord ++ tailWord_219363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219365 : List Nat := [1, 3, 1, 4, 2, 3, 1, 4]
def baseStart_219365 : Nat := 118140960795 + 219365 * 2 ^ 59
def prefixEnd_219365 : Nat := 4983230072969 + 3 ^ 40 * 219365 * 2
def baseEnd_219365 : Nat := 66749442236230795335505

theorem tailTrace_219365 : CollatzResearch.WordTrace tailWord_219365 prefixEnd_219365 66749442236230795335505 := by
  unfold tailWord_219365
  simp only [CollatzResearch.WordTrace]
  refine ⟨8000898850285544404403549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5333932566857029602935699 8000898850285544404403549)
  ·
    refine ⟨3000337068857079151651331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8000898850285544404403549 3000337068857079151651331)
    ·
      refine ⟨4500505603285618727476997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3000337068857079151651331 4500505603285618727476997)
      ·
        refine ⟨843844800616053511401937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4500505603285618727476997 843844800616053511401937)
        ·
          refine ⟨632883600462040133551453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 843844800616053511401937 632883600462040133551453)
          ·
            refine ⟨237331350173265050081795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 632883600462040133551453 237331350173265050081795)
            ·
              refine ⟨355997025259897575122693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237331350173265050081795 355997025259897575122693)
              ·
                refine ⟨66749442236230795335505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 355997025259897575122693 66749442236230795335505)
                ·
                  rfl

theorem cell19_219365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_219365 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219365 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219365 prefixEnd_219365 := by exact prefixLift 219365
  have htrace : WordTrace (prefixWord ++ tailWord_219365) baseStart_219365 baseEnd_219365 := by
    simpa [prefixWord, tailWord_219365, baseEnd_219365] using wordTrace_append hprefix tailTrace_219365
  have hstable : (prefixWord ++ tailWord_219365).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219365).length < 2 ^ (prefixWord ++ tailWord_219365).sum := by decide
  have hdescent : baseEnd_219365 < baseStart_219365 := by decide
  rcases family_descends (prefixWord ++ tailWord_219365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219437 : List Nat := [1, 5, 3, 1, 2, 2, 2, 3]
def baseStart_219437 : Nat := 118140960795 + 219437 * 2 ^ 59
def prefixEnd_219437 : Nat := 4983230072969 + 3 ^ 40 * 219437 * 2
def baseEnd_219437 : Nat := 66771350744155961735309

theorem tailTrace_219437 : CollatzResearch.WordTrace tailWord_219437 prefixEnd_219437 66771350744155961735309 := by
  unfold tailWord_219437
  simp only [CollatzResearch.WordTrace]
  refine ⟨8003524906024700701024565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5335683270683133800683043 8003524906024700701024565)
  ·
    refine ⟨750330459939815690721053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 8003524906024700701024565 750330459939815690721053)
    ·
      refine ⟨281373922477430884020395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 750330459939815690721053 281373922477430884020395)
      ·
        refine ⟨422060883716146326030593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 281373922477430884020395 422060883716146326030593)
        ·
          refine ⟨316545662787109744522945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 422060883716146326030593 316545662787109744522945)
          ·
            refine ⟨237409247090332308392209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 316545662787109744522945 237409247090332308392209)
            ·
              refine ⟨178056935317749231294157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 237409247090332308392209 178056935317749231294157)
              ·
                refine ⟨66771350744155961735309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178056935317749231294157 66771350744155961735309)
                ·
                  rfl

theorem cell19_219437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 2, 3].length) (baseStart_219437 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219437 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219437 prefixEnd_219437 := by exact prefixLift 219437
  have htrace : WordTrace (prefixWord ++ tailWord_219437) baseStart_219437 baseEnd_219437 := by
    simpa [prefixWord, tailWord_219437, baseEnd_219437] using wordTrace_append hprefix tailTrace_219437
  have hstable : (prefixWord ++ tailWord_219437).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219437).length < 2 ^ (prefixWord ++ tailWord_219437).sum := by decide
  have hdescent : baseEnd_219437 < baseStart_219437 := by decide
  rcases family_descends (prefixWord ++ tailWord_219437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219464 : List Nat := [2, 1, 3, 1, 1, 2, 9]
def baseStart_219464 : Nat := 118140960795 + 219464 * 2 ^ 59
def prefixEnd_219464 : Nat := 4983230072969 + 3 ^ 40 * 219464 * 2
def baseEnd_219464 : Nat := 22259855478209299711745

theorem tailTrace_219464 : CollatzResearch.WordTrace tailWord_219464 prefixEnd_219464 22259855478209299711745 := by
  unfold tailWord_219464
  simp only [CollatzResearch.WordTrace]
  refine ⟨4002254838463442156128723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5336339784617922874838297 4002254838463442156128723)
  ·
    refine ⟨6003382257695163234193085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4002254838463442156128723 6003382257695163234193085)
    ·
      refine ⟨2251268346635686212822407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6003382257695163234193085 2251268346635686212822407)
      ·
        refine ⟨3376902519953529319233611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2251268346635686212822407 3376902519953529319233611)
        ·
          refine ⟨5065353779930293978850417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3376902519953529319233611 5065353779930293978850417)
          ·
            refine ⟨3799015334947720484137813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5065353779930293978850417 3799015334947720484137813)
            ·
              refine ⟨22259855478209299711745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3799015334947720484137813 22259855478209299711745)
              ·
                rfl

theorem cell19_219464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 9].length) (baseStart_219464 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219464 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219464 prefixEnd_219464 := by exact prefixLift 219464
  have htrace : WordTrace (prefixWord ++ tailWord_219464) baseStart_219464 baseEnd_219464 := by
    simpa [prefixWord, tailWord_219464, baseEnd_219464] using wordTrace_append hprefix tailTrace_219464
  have hstable : (prefixWord ++ tailWord_219464).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219464).length < 2 ^ (prefixWord ++ tailWord_219464).sum := by decide
  have hdescent : baseEnd_219464 < baseStart_219464 := by decide
  rcases family_descends (prefixWord ++ tailWord_219464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219553 : List Nat := [1, 2, 3, 5, 1, 1, 3, 3]
def baseStart_219553 : Nat := 118140960795 + 219553 * 2 ^ 59
def prefixEnd_219553 : Nat := 4983230072969 + 3 ^ 40 * 219553 * 2
def baseEnd_219553 : Nat := 66806647784702063157215

theorem tailTrace_219553 : CollatzResearch.WordTrace tailWord_219553 prefixEnd_219553 66806647784702063157215 := by
  unfold tailWord_219553
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007755773604452512247313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5338503849069635008164875 8007755773604452512247313)
  ·
    refine ⟨6005816830203339384185485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8007755773604452512247313 6005816830203339384185485)
    ·
      refine ⟨2252181311326252269069557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6005816830203339384185485 2252181311326252269069557)
      ·
        refine ⟨211141997936836150225271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2252181311326252269069557 211141997936836150225271)
        ·
          refine ⟨316712996905254225337907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211141997936836150225271 316712996905254225337907)
          ·
            refine ⟨475069495357881338006861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316712996905254225337907 475069495357881338006861)
            ·
              refine ⟨178151060759205501752573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475069495357881338006861 178151060759205501752573)
              ·
                refine ⟨66806647784702063157215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178151060759205501752573 66806647784702063157215)
                ·
                  rfl

theorem cell19_219553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 3, 3].length) (baseStart_219553 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219553 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219553 prefixEnd_219553 := by exact prefixLift 219553
  have htrace : WordTrace (prefixWord ++ tailWord_219553) baseStart_219553 baseEnd_219553 := by
    simpa [prefixWord, tailWord_219553, baseEnd_219553] using wordTrace_append hprefix tailTrace_219553
  have hstable : (prefixWord ++ tailWord_219553).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219553).length < 2 ^ (prefixWord ++ tailWord_219553).sum := by decide
  have hdescent : baseEnd_219553 < baseStart_219553 := by decide
  rcases family_descends (prefixWord ++ tailWord_219553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219557 : List Nat := [1, 3, 1, 2, 1, 1, 7, 3]
def baseStart_219557 : Nat := 118140960795 + 219557 * 2 ^ 59
def prefixEnd_219557 : Nat := 4983230072969 + 3 ^ 40 * 219557 * 2
def baseEnd_219557 : Nat := 66807864924031239068315

theorem tailTrace_219557 : CollatzResearch.WordTrace tailWord_219557 prefixEnd_219557 66807864924031239068315 := by
  unfold tailWord_219557
  simp only [CollatzResearch.WordTrace]
  refine ⟨8007901665589961195392925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5338601110393307463595283 8007901665589961195392925)
  ·
    refine ⟨3002963124596235448272347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8007901665589961195392925 3002963124596235448272347)
    ·
      refine ⟨4504444686894353172408521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3002963124596235448272347 4504444686894353172408521)
      ·
        refine ⟨3378333515170764879306391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4504444686894353172408521 3378333515170764879306391)
        ·
          refine ⟨5067500272756147318959587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3378333515170764879306391 5067500272756147318959587)
          ·
            refine ⟨7601250409134220978439381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5067500272756147318959587 7601250409134220978439381)
            ·
              refine ⟨178154306464083304182173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 7601250409134220978439381 178154306464083304182173)
              ·
                refine ⟨66807864924031239068315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178154306464083304182173 66807864924031239068315)
                ·
                  rfl

theorem cell19_219557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 7, 3].length) (baseStart_219557 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219557 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219557 prefixEnd_219557 := by exact prefixLift 219557
  have htrace : WordTrace (prefixWord ++ tailWord_219557) baseStart_219557 baseEnd_219557 := by
    simpa [prefixWord, tailWord_219557, baseEnd_219557] using wordTrace_append hprefix tailTrace_219557
  have hstable : (prefixWord ++ tailWord_219557).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219557).length < 2 ^ (prefixWord ++ tailWord_219557).sum := by decide
  have hdescent : baseEnd_219557 < baseStart_219557 := by decide
  rcases family_descends (prefixWord ++ tailWord_219557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219572 : List Nat := [2, 5, 2, 2, 1, 1, 6]
def baseStart_219572 : Nat := 118140960795 + 219572 * 2 ^ 59
def prefixEnd_219572 : Nat := 4983230072969 + 3 ^ 40 * 219572 * 2
def baseEnd_219572 : Nat := 22270809732171882911647

theorem tailTrace_219572 : CollatzResearch.WordTrace tailWord_219572 prefixEnd_219572 22270809732171882911647 := by
  unfold tailWord_219572
  simp only [CollatzResearch.WordTrace]
  refine ⟨4004224380267809378594485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5338965840357079171459313 4004224380267809378594485)
  ·
    refine ⟨375396035650107129243233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4004224380267809378594485 375396035650107129243233)
    ·
      refine ⟨281547026737580346932425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 375396035650107129243233 281547026737580346932425)
      ·
        refine ⟨211160270053185260199319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 281547026737580346932425 211160270053185260199319)
        ·
          refine ⟨316740405079777890298979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211160270053185260199319 316740405079777890298979)
          ·
            refine ⟨475110607619666835448469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316740405079777890298979 475110607619666835448469)
            ·
              refine ⟨22270809732171882911647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 475110607619666835448469 22270809732171882911647)
              ·
                rfl

theorem cell19_219572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 6].length) (baseStart_219572 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219572 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219572 prefixEnd_219572 := by exact prefixLift 219572
  have htrace : WordTrace (prefixWord ++ tailWord_219572) baseStart_219572 baseEnd_219572 := by
    simpa [prefixWord, tailWord_219572, baseEnd_219572] using wordTrace_append hprefix tailTrace_219572
  have hstable : (prefixWord ++ tailWord_219572).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219572).length < 2 ^ (prefixWord ++ tailWord_219572).sum := by decide
  have hdescent : baseEnd_219572 < baseStart_219572 := by decide
  rcases family_descends (prefixWord ++ tailWord_219572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219616 : List Nat := [2, 1, 1, 3, 1, 1, 5, 5]
def baseStart_219616 : Nat := 118140960795 + 219616 * 2 ^ 59
def prefixEnd_219616 : Nat := 4983230072969 + 3 ^ 40 * 219616 * 2
def baseEnd_219616 : Nat := 66825817729136583757043

theorem tailTrace_219616 : CollatzResearch.WordTrace tailWord_219616 prefixEnd_219616 66825817729136583757043 := by
  unfold tailWord_219616
  simp only [CollatzResearch.WordTrace]
  refine ⟨4005026786188107135895351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5340035714917476181193801 4005026786188107135895351)
  ·
    refine ⟨6007540179282160703843027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4005026786188107135895351 6007540179282160703843027)
    ·
      refine ⟨9011310268923241055764541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6007540179282160703843027 9011310268923241055764541)
      ·
        refine ⟨3379241350846215395911703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9011310268923241055764541 3379241350846215395911703)
        ·
          refine ⟨5068862026269323093867555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3379241350846215395911703 5068862026269323093867555)
          ·
            refine ⟨7603293039403984640801333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5068862026269323093867555 7603293039403984640801333)
            ·
              refine ⟨712808722444123560075125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7603293039403984640801333 712808722444123560075125)
              ·
                refine ⟨66825817729136583757043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 712808722444123560075125 66825817729136583757043)
                ·
                  rfl

theorem cell19_219616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 5].length) (baseStart_219616 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219616 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219616 prefixEnd_219616 := by exact prefixLift 219616
  have htrace : WordTrace (prefixWord ++ tailWord_219616) baseStart_219616 baseEnd_219616 := by
    simpa [prefixWord, tailWord_219616, baseEnd_219616] using wordTrace_append hprefix tailTrace_219616
  have hstable : (prefixWord ++ tailWord_219616).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219616).length < 2 ^ (prefixWord ++ tailWord_219616).sum := by decide
  have hdescent : baseEnd_219616 < baseStart_219616 := by decide
  rcases family_descends (prefixWord ++ tailWord_219616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219652 : List Nat := [2, 3, 2, 3, 1, 1, 1, 6]
def baseStart_219652 : Nat := 118140960795 + 219652 * 2 ^ 59
def prefixEnd_219652 : Nat := 4983230072969 + 3 ^ 40 * 219652 * 2
def baseEnd_219652 : Nat := 66836771983099166956945

theorem tailTrace_219652 : CollatzResearch.WordTrace tailWord_219652 prefixEnd_219652 66836771983099166956945 := by
  unfold tailWord_219652
  simp only [CollatzResearch.WordTrace]
  refine ⟨4005683300122896210050605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5340911066830528280067473 4005683300122896210050605)
  ·
    refine ⟨1502131237546086078768977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4005683300122896210050605 1502131237546086078768977)
    ·
      refine ⟨1126598428159564559076733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1502131237546086078768977 1126598428159564559076733)
      ·
        refine ⟨422474410559836709653775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1126598428159564559076733 422474410559836709653775)
        ·
          refine ⟨633711615839755064480663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 422474410559836709653775 633711615839755064480663)
          ·
            refine ⟨950567423759632596720995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633711615839755064480663 950567423759632596720995)
            ·
              refine ⟨1425851135639448895081493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 950567423759632596720995 1425851135639448895081493)
              ·
                refine ⟨66836771983099166956945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1425851135639448895081493 66836771983099166956945)
                ·
                  rfl

theorem cell19_219652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 6].length) (baseStart_219652 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219652 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219652 prefixEnd_219652 := by exact prefixLift 219652
  have htrace : WordTrace (prefixWord ++ tailWord_219652) baseStart_219652 baseEnd_219652 := by
    simpa [prefixWord, tailWord_219652, baseEnd_219652] using wordTrace_append hprefix tailTrace_219652
  have hstable : (prefixWord ++ tailWord_219652).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219652).length < 2 ^ (prefixWord ++ tailWord_219652).sum := by decide
  have hdescent : baseEnd_219652 < baseStart_219652 := by decide
  rcases family_descends (prefixWord ++ tailWord_219652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219709 : List Nat := [1, 4, 1, 3, 2, 1, 3, 4]
def baseStart_219709 : Nat := 118140960795 + 219709 * 2 ^ 59
def prefixEnd_219709 : Nat := 4983230072969 + 3 ^ 40 * 219709 * 2
def baseEnd_219709 : Nat := 66854116218539923690123

theorem tailTrace_219709 : CollatzResearch.WordTrace tailWord_219709 prefixEnd_219709 66854116218539923690123 := by
  unfold tailWord_219709
  simp only [CollatzResearch.WordTrace]
  refine ⟨8013445561039291154926181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5342297040692860769950787 8013445561039291154926181)
  ·
    refine ⟨1502521042694867091548659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8013445561039291154926181 1502521042694867091548659)
    ·
      refine ⟨2253781564042300637322989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1502521042694867091548659 2253781564042300637322989)
      ·
        refine ⟨845168086515862738996121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2253781564042300637322989 845168086515862738996121)
        ·
          refine ⟨633876064886897054247091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845168086515862738996121 633876064886897054247091)
          ·
            refine ⟨950814097330345581370637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 633876064886897054247091 950814097330345581370637)
            ·
              refine ⟨356555286498879593013989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 950814097330345581370637 356555286498879593013989)
              ·
                refine ⟨66854116218539923690123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 356555286498879593013989 66854116218539923690123)
                ·
                  rfl

theorem cell19_219709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_219709 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219709 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219709 prefixEnd_219709 := by exact prefixLift 219709
  have htrace : WordTrace (prefixWord ++ tailWord_219709) baseStart_219709 baseEnd_219709 := by
    simpa [prefixWord, tailWord_219709, baseEnd_219709] using wordTrace_append hprefix tailTrace_219709
  have hstable : (prefixWord ++ tailWord_219709).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219709).length < 2 ^ (prefixWord ++ tailWord_219709).sum := by decide
  have hdescent : baseEnd_219709 < baseStart_219709 := by decide
  rcases family_descends (prefixWord ++ tailWord_219709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219802 : List Nat := [3, 1, 1, 6, 1, 2, 5]
def baseStart_219802 : Nat := 118140960795 + 219802 * 2 ^ 59
def prefixEnd_219802 : Nat := 4983230072969 + 3 ^ 40 * 219802 * 2
def baseEnd_219802 : Nat := 22294138235981087874401

theorem tailTrace_219802 : CollatzResearch.WordTrace tailWord_219802 prefixEnd_219802 22294138235981087874401 := by
  unfold tailWord_219802
  simp only [CollatzResearch.WordTrace]
  refine ⟨2004209387425592009515415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5344558366468245358707773 2004209387425592009515415)
  ·
    refine ⟨3006314081138388014273123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2004209387425592009515415 3006314081138388014273123)
    ·
      refine ⟨4509471121707582021409685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3006314081138388014273123 4509471121707582021409685)
      ·
        refine ⟨211381458830042907253579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 4509471121707582021409685 211381458830042907253579)
        ·
          refine ⟨317072188245064360880369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211381458830042907253579 317072188245064360880369)
          ·
            refine ⟨237804141183798270660277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317072188245064360880369 237804141183798270660277)
            ·
              refine ⟨22294138235981087874401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237804141183798270660277 22294138235981087874401)
              ·
                rfl

theorem cell19_219802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 1, 2, 5].length) (baseStart_219802 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219802 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219802 prefixEnd_219802 := by exact prefixLift 219802
  have htrace : WordTrace (prefixWord ++ tailWord_219802) baseStart_219802 baseEnd_219802 := by
    simpa [prefixWord, tailWord_219802, baseEnd_219802] using wordTrace_append hprefix tailTrace_219802
  have hstable : (prefixWord ++ tailWord_219802).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219802).length < 2 ^ (prefixWord ++ tailWord_219802).sum := by decide
  have hdescent : baseEnd_219802 < baseStart_219802 := by decide
  rcases family_descends (prefixWord ++ tailWord_219802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219804 : List Nat := [2, 2, 3, 2, 2, 3, 5]
def baseStart_219804 : Nat := 118140960795 + 219804 * 2 ^ 59
def prefixEnd_219804 : Nat := 4983230072969 + 3 ^ 40 * 219804 * 2
def baseEnd_219804 : Nat := 22294341092535950526251

theorem tailTrace_219804 : CollatzResearch.WordTrace tailWord_219804 prefixEnd_219804 22294341092535950526251 := by
  unfold tailWord_219804
  simp only [CollatzResearch.WordTrace]
  refine ⟨4008455247847561189817233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5344606997130081586422977 4008455247847561189817233)
  ·
    refine ⟨3006341435885670892362925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4008455247847561189817233 3006341435885670892362925)
    ·
      refine ⟨1127378038457126584636097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3006341435885670892362925 1127378038457126584636097)
      ·
        refine ⟨845533528842844938477073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1127378038457126584636097 845533528842844938477073)
        ·
          refine ⟨634150146632133703857805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 845533528842844938477073 634150146632133703857805)
          ·
            refine ⟨237806304987050138946677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 634150146632133703857805 237806304987050138946677)
            ·
              refine ⟨22294341092535950526251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237806304987050138946677 22294341092535950526251)
              ·
                rfl

theorem cell19_219804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_219804 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219804 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219804 prefixEnd_219804 := by exact prefixLift 219804
  have htrace : WordTrace (prefixWord ++ tailWord_219804) baseStart_219804 baseEnd_219804 := by
    simpa [prefixWord, tailWord_219804, baseEnd_219804] using wordTrace_append hprefix tailTrace_219804
  have hstable : (prefixWord ++ tailWord_219804).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219804).length < 2 ^ (prefixWord ++ tailWord_219804).sum := by decide
  have hdescent : baseEnd_219804 < baseStart_219804 := by decide
  rcases family_descends (prefixWord ++ tailWord_219804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219861 : List Nat := [1, 3, 2, 5, 1, 7]
def baseStart_219861 : Nat := 118140960795 + 219861 * 2 ^ 59
def prefixEnd_219861 : Nat := 4983230072969 + 3 ^ 40 * 219861 * 2
def baseEnd_219861 : Nat := 7433374168116512034659

theorem tailTrace_219861 : CollatzResearch.WordTrace tailWord_219861 prefixEnd_219861 7433374168116512034659 := by
  unfold tailWord_219861
  simp only [CollatzResearch.WordTrace]
  refine ⟨8018989456488621114459437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5345992970992414076306291 8018989456488621114459437)
  ·
    refine ⟨3007121046183232917922289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8018989456488621114459437 3007121046183232917922289)
    ·
      refine ⟨2255340784637424688441717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3007121046183232917922289 2255340784637424688441717)
      ·
        refine ⟨211438198559758564541411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2255340784637424688441717 211438198559758564541411)
        ·
          refine ⟨317157297839637846812117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211438198559758564541411 317157297839637846812117)
          ·
            refine ⟨7433374168116512034659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 317157297839637846812117 7433374168116512034659)
            ·
              rfl

theorem cell19_219861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 7].length) (baseStart_219861 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219861 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219861 prefixEnd_219861 := by exact prefixLift 219861
  have htrace : WordTrace (prefixWord ++ tailWord_219861) baseStart_219861 baseEnd_219861 := by
    simpa [prefixWord, tailWord_219861, baseEnd_219861] using wordTrace_append hprefix tailTrace_219861
  have hstable : (prefixWord ++ tailWord_219861).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219861).length < 2 ^ (prefixWord ++ tailWord_219861).sum := by decide
  have hdescent : baseEnd_219861 < baseStart_219861 := by decide
  rcases family_descends (prefixWord ++ tailWord_219861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219893 : List Nat := [1, 3, 6, 1, 1, 1, 3, 3]
def baseStart_219893 : Nat := 118140960795 + 219893 * 2 ^ 59
def prefixEnd_219893 : Nat := 4983230072969 + 3 ^ 40 * 219893 * 2
def baseEnd_219893 : Nat := 66910104627682015600733

theorem tailTrace_219893 : CollatzResearch.WordTrace tailWord_219893 prefixEnd_219893 66910104627682015600733 := by
  unfold tailWord_219893
  simp only [CollatzResearch.WordTrace]
  refine ⟨8020156592372690579624333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5346771061581793719749555 8020156592372690579624333)
  ·
    refine ⟨3007558722139758967359125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8020156592372690579624333 3007558722139758967359125)
    ·
      refine ⟨140979315100301201594959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3007558722139758967359125 140979315100301201594959)
      ·
        refine ⟨211468972650451802392439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140979315100301201594959 211468972650451802392439)
        ·
          refine ⟨317203458975677703588659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211468972650451802392439 317203458975677703588659)
          ·
            refine ⟨475805188463516555382989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317203458975677703588659 475805188463516555382989)
            ·
              refine ⟨178426945673818708268621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 475805188463516555382989 178426945673818708268621)
              ·
                refine ⟨66910104627682015600733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178426945673818708268621 66910104627682015600733)
                ·
                  rfl

theorem cell19_219893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 3, 3].length) (baseStart_219893 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219893 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219893 prefixEnd_219893 := by exact prefixLift 219893
  have htrace : WordTrace (prefixWord ++ tailWord_219893) baseStart_219893 baseEnd_219893 := by
    simpa [prefixWord, tailWord_219893, baseEnd_219893] using wordTrace_append hprefix tailTrace_219893
  have hstable : (prefixWord ++ tailWord_219893).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219893).length < 2 ^ (prefixWord ++ tailWord_219893).sum := by decide
  have hdescent : baseEnd_219893 < baseStart_219893 := by decide
  rcases family_descends (prefixWord ++ tailWord_219893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_219977 : List Nat := [1, 2, 1, 1, 2, 7, 5]
def baseStart_219977 : Nat := 118140960795 + 219977 * 2 ^ 59
def prefixEnd_219977 : Nat := 4983230072969 + 3 ^ 40 * 219977 * 2
def baseEnd_219977 : Nat := 22311888184531569911279

theorem tailTrace_219977 : CollatzResearch.WordTrace tailWord_219977 prefixEnd_219977 22311888184531569911279 := by
  unfold tailWord_219977
  simp only [CollatzResearch.WordTrace]
  refine ⟨8023220324068372925682185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5348813549378915283788123 8023220324068372925682185)
  ·
    refine ⟨6017415243051279694261639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8023220324068372925682185 6017415243051279694261639)
    ·
      refine ⟨9026122864576919541392459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6017415243051279694261639 9026122864576919541392459)
      ·
        refine ⟨13539184296865379312088689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9026122864576919541392459 13539184296865379312088689)
        ·
          refine ⟨10154388222649034484066517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13539184296865379312088689 10154388222649034484066517)
          ·
            refine ⟨237993473968336745720309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 10154388222649034484066517 237993473968336745720309)
            ·
              refine ⟨22311888184531569911279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237993473968336745720309 22311888184531569911279)
              ·
                rfl

theorem cell19_219977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 5].length) (baseStart_219977 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_219977 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_219977 prefixEnd_219977 := by exact prefixLift 219977
  have htrace : WordTrace (prefixWord ++ tailWord_219977) baseStart_219977 baseEnd_219977 := by
    simpa [prefixWord, tailWord_219977, baseEnd_219977] using wordTrace_append hprefix tailTrace_219977
  have hstable : (prefixWord ++ tailWord_219977).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_219977).length < 2 ^ (prefixWord ++ tailWord_219977).sum := by decide
  have hdescent : baseEnd_219977 < baseStart_219977 := by decide
  rcases family_descends (prefixWord ++ tailWord_219977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220030 : List Nat := [4, 2, 3, 1, 3, 6]
def baseStart_220030 : Nat := 118140960795 + 220030 * 2 ^ 59
def prefixEnd_220030 : Nat := 4983230072969 + 3 ^ 40 * 220030 * 2
def baseEnd_220030 : Nat := 7439087961078476728435

theorem tailTrace_220030 : CollatzResearch.WordTrace tailWord_220030 prefixEnd_220030 7439087961078476728435 := by
  unfold tailWord_220030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1003144174109545372170193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5350102261917575318241029 1003144174109545372170193)
  ·
    refine ⟨752358130582159029127645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1003144174109545372170193 752358130582159029127645)
    ·
      refine ⟨282134298968309635922867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 752358130582159029127645 282134298968309635922867)
      ·
        refine ⟨423201448452464453884301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282134298968309635922867 423201448452464453884301)
        ·
          refine ⟨158700543169674170206613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423201448452464453884301 158700543169674170206613)
          ·
            refine ⟨7439087961078476728435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 158700543169674170206613 7439087961078476728435)
            ·
              rfl

theorem cell19_220030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 6].length) (baseStart_220030 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220030 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220030 prefixEnd_220030 := by exact prefixLift 220030
  have htrace : WordTrace (prefixWord ++ tailWord_220030) baseStart_220030 baseEnd_220030 := by
    simpa [prefixWord, tailWord_220030, baseEnd_220030] using wordTrace_append hprefix tailTrace_220030
  have hstable : (prefixWord ++ tailWord_220030).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220030).length < 2 ^ (prefixWord ++ tailWord_220030).sum := by decide
  have hdescent : baseEnd_220030 < baseStart_220030 := by decide
  rcases family_descends (prefixWord ++ tailWord_220030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220053 : List Nat := [1, 3, 2, 1, 1, 4, 3, 4]
def baseStart_220053 : Nat := 118140960795 + 220053 * 2 ^ 59
def prefixEnd_220053 : Nat := 4983230072969 + 3 ^ 40 * 220053 * 2
def baseEnd_220053 : Nat := 66958790200849052044741

theorem tailTrace_220053 : CollatzResearch.WordTrace tailWord_220053 prefixEnd_220053 66958790200849052044741 := by
  unfold tailWord_220053
  simp only [CollatzResearch.WordTrace]
  refine ⟨8025992271793037905448813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5350661514528691936965875 8025992271793037905448813)
  ·
    refine ⟨3009747101922389214543305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8025992271793037905448813 3009747101922389214543305)
    ·
      refine ⟨2257310326441791910907479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3009747101922389214543305 2257310326441791910907479)
      ·
        refine ⟨3385965489662687866361219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2257310326441791910907479 3385965489662687866361219)
        ·
          refine ⟨5078948234494031799541829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3385965489662687866361219 5078948234494031799541829)
          ·
            refine ⟨952302793967630962414093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5078948234494031799541829 952302793967630962414093)
            ·
              refine ⟨357113547737861610905285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 952302793967630962414093 357113547737861610905285)
              ·
                refine ⟨66958790200849052044741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357113547737861610905285 66958790200849052044741)
                ·
                  rfl

theorem cell19_220053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 4].length) (baseStart_220053 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220053 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220053 prefixEnd_220053 := by exact prefixLift 220053
  have htrace : WordTrace (prefixWord ++ tailWord_220053) baseStart_220053 baseEnd_220053 := by
    simpa [prefixWord, tailWord_220053, baseEnd_220053] using wordTrace_append hprefix tailTrace_220053
  have hstable : (prefixWord ++ tailWord_220053).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220053).length < 2 ^ (prefixWord ++ tailWord_220053).sum := by decide
  have hdescent : baseEnd_220053 < baseStart_220053 := by decide
  rcases family_descends (prefixWord ++ tailWord_220053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220112 : List Nat := [2, 1, 1, 1, 1, 2, 3, 8]
def baseStart_220112 : Nat := 118140960795 + 220112 * 2 ^ 59
def prefixEnd_220112 : Nat := 4983230072969 + 3 ^ 40 * 220112 * 2
def baseEnd_220112 : Nat := 66976743005954396733469

theorem tailTrace_220112 : CollatzResearch.WordTrace tailWord_220112 prefixEnd_220112 66976743005954396733469 := by
  unfold tailWord_220112
  simp only [CollatzResearch.WordTrace]
  refine ⟨4014072089289645490923295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5352096119052860654564393 4014072089289645490923295)
  ·
    refine ⟨6021108133934468236384943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4014072089289645490923295 6021108133934468236384943)
    ·
      refine ⟨9031662200901702354577415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6021108133934468236384943 9031662200901702354577415)
      ·
        refine ⟨13547493301352553531866123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9031662200901702354577415 13547493301352553531866123)
        ·
          refine ⟨20321239952028830297799185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13547493301352553531866123 20321239952028830297799185)
          ·
            refine ⟨15240929964021622723349389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20321239952028830297799185 15240929964021622723349389)
            ·
              refine ⟨5715348736508108521256021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15240929964021622723349389 5715348736508108521256021)
              ·
                refine ⟨66976743005954396733469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5715348736508108521256021 66976743005954396733469)
                ·
                  rfl

theorem cell19_220112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 8].length) (baseStart_220112 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220112 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220112 prefixEnd_220112 := by exact prefixLift 220112
  have htrace : WordTrace (prefixWord ++ tailWord_220112) baseStart_220112 baseEnd_220112 := by
    simpa [prefixWord, tailWord_220112, baseEnd_220112] using wordTrace_append hprefix tailTrace_220112
  have hstable : (prefixWord ++ tailWord_220112).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220112).length < 2 ^ (prefixWord ++ tailWord_220112).sum := by decide
  have hdescent : baseEnd_220112 < baseStart_220112 := by decide
  rcases family_descends (prefixWord ++ tailWord_220112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220125 : List Nat := [1, 4, 3, 1, 2, 3, 2, 3]
def baseStart_220125 : Nat := 118140960795 + 220125 * 2 ^ 59
def prefixEnd_220125 : Nat := 4983230072969 + 3 ^ 40 * 220125 * 2
def baseEnd_220125 : Nat := 66980698708774218444545

theorem tailTrace_220125 : CollatzResearch.WordTrace tailWord_220125 prefixEnd_220125 66980698708774218444545 := by
  unfold tailWord_220125
  simp only [CollatzResearch.WordTrace]
  refine ⟨8028618327532194202069829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5352412218354796134713219 8028618327532194202069829)
  ·
    refine ⟨1505365936412286412888093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8028618327532194202069829 1505365936412286412888093)
    ·
      refine ⟨564512226154607404833035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1505365936412286412888093 564512226154607404833035)
      ·
        refine ⟨846768339231911107249553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 564512226154607404833035 846768339231911107249553)
        ·
          refine ⟨635076254423933330437165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 846768339231911107249553 635076254423933330437165)
          ·
            refine ⟨238153595408974998913937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 635076254423933330437165 238153595408974998913937)
            ·
              refine ⟨178615196556731249185453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238153595408974998913937 178615196556731249185453)
              ·
                refine ⟨66980698708774218444545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178615196556731249185453 66980698708774218444545)
                ·
                  rfl

theorem cell19_220125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 3, 2, 3].length) (baseStart_220125 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220125 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220125 prefixEnd_220125 := by exact prefixLift 220125
  have htrace : WordTrace (prefixWord ++ tailWord_220125) baseStart_220125 baseEnd_220125 := by
    simpa [prefixWord, tailWord_220125, baseEnd_220125] using wordTrace_append hprefix tailTrace_220125
  have hstable : (prefixWord ++ tailWord_220125).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220125).length < 2 ^ (prefixWord ++ tailWord_220125).sum := by decide
  have hdescent : baseEnd_220125 < baseStart_220125 := by decide
  rcases family_descends (prefixWord ++ tailWord_220125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220167 : List Nat := [1, 1, 4, 3, 1, 1, 4, 4]
def baseStart_220167 : Nat := 118140960795 + 220167 * 2 ^ 59
def prefixEnd_220167 : Nat := 4983230072969 + 3 ^ 40 * 220167 * 2
def baseEnd_220167 : Nat := 66993478671730565511097

theorem tailTrace_220167 : CollatzResearch.WordTrace tailWord_220167 prefixEnd_220167 66993478671730565511097 := by
  unfold tailWord_220167
  simp only [CollatzResearch.WordTrace]
  refine ⟨8030150193380035375098755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5353433462253356916732503 8030150193380035375098755)
  ·
    refine ⟨12045225290070053062648133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8030150193380035375098755 12045225290070053062648133)
    ·
      refine ⟨2258479741888134949246525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12045225290070053062648133 2258479741888134949246525)
      ·
        refine ⟨846929903208050605967447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2258479741888134949246525 846929903208050605967447)
        ·
          refine ⟨1270394854812075908951171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 846929903208050605967447 1270394854812075908951171)
          ·
            refine ⟨1905592282218113863426757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1270394854812075908951171 1905592282218113863426757)
            ·
              refine ⟨357298552915896349392517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1905592282218113863426757 357298552915896349392517)
              ·
                refine ⟨66993478671730565511097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357298552915896349392517 66993478671730565511097)
                ·
                  rfl

theorem cell19_220167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 4, 4].length) (baseStart_220167 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220167 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220167 prefixEnd_220167 := by exact prefixLift 220167
  have htrace : WordTrace (prefixWord ++ tailWord_220167) baseStart_220167 baseEnd_220167 := by
    simpa [prefixWord, tailWord_220167, baseEnd_220167] using wordTrace_append hprefix tailTrace_220167
  have hstable : (prefixWord ++ tailWord_220167).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220167).length < 2 ^ (prefixWord ++ tailWord_220167).sum := by decide
  have hdescent : baseEnd_220167 < baseStart_220167 := by decide
  rcases family_descends (prefixWord ++ tailWord_220167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220222 : List Nat := [4, 2, 1, 3, 1, 1, 3, 4]
def baseStart_220222 : Nat := 118140960795 + 220222 * 2 ^ 59
def prefixEnd_220222 : Nat := 4983230072969 + 3 ^ 40 * 220222 * 2
def baseEnd_220222 : Nat := 67010214337506734288725

theorem tailTrace_220222 : CollatzResearch.WordTrace tailWord_220222 prefixEnd_220222 67010214337506734288725 := by
  unfold tailWord_220222
  simp only [CollatzResearch.WordTrace]
  refine ⟨1004019526022597471043865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 5354770805453853178900613 1004019526022597471043865)
  ·
    refine ⟨753014644516948103282899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1004019526022597471043865 753014644516948103282899)
    ·
      refine ⟨1129521966775422154924349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 753014644516948103282899 1129521966775422154924349)
      ·
        refine ⟨423570737540783308096631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1129521966775422154924349 423570737540783308096631)
        ·
          refine ⟨635356106311174962144947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 423570737540783308096631 635356106311174962144947)
          ·
            refine ⟨953034159466762443217421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 635356106311174962144947 953034159466762443217421)
            ·
              refine ⟨357387809800035916206533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 953034159466762443217421 357387809800035916206533)
              ·
                refine ⟨67010214337506734288725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357387809800035916206533 67010214337506734288725)
                ·
                  rfl

theorem cell19_220222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_220222 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220222 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220222 prefixEnd_220222 := by exact prefixLift 220222
  have htrace : WordTrace (prefixWord ++ tailWord_220222) baseStart_220222 baseEnd_220222 := by
    simpa [prefixWord, tailWord_220222, baseEnd_220222] using wordTrace_append hprefix tailTrace_220222
  have hstable : (prefixWord ++ tailWord_220222).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220222).length < 2 ^ (prefixWord ++ tailWord_220222).sum := by decide
  have hdescent : baseEnd_220222 < baseStart_220222 := by decide
  rcases family_descends (prefixWord ++ tailWord_220222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220296 : List Nat := [2, 1, 3, 4, 2, 2, 2, 3]
def baseStart_220296 : Nat := 118140960795 + 220296 * 2 ^ 59
def prefixEnd_220296 : Nat := 4983230072969 + 3 ^ 40 * 220296 * 2
def baseEnd_220296 : Nat := 67032731415096488644079

theorem tailTrace_220296 : CollatzResearch.WordTrace tailWord_220296 prefixEnd_220296 67032731415096488644079 := by
  unfold tailWord_220296
  simp only [CollatzResearch.WordTrace]
  refine ⟨4017427604956345203272371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5356570139941793604363161 4017427604956345203272371)
  ·
    refine ⟨6026141407434517804908557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4017427604956345203272371 6026141407434517804908557)
    ·
      refine ⟨2259803027787944176840709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6026141407434517804908557 2259803027787944176840709)
      ·
        refine ⟨423713067710239533157633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2259803027787944176840709 423713067710239533157633)
        ·
          refine ⟨317784800782679649868225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423713067710239533157633 317784800782679649868225)
          ·
            refine ⟨238338600587009737401169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 317784800782679649868225 238338600587009737401169)
            ·
              refine ⟨178753950440257303050877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238338600587009737401169 178753950440257303050877)
              ·
                refine ⟨67032731415096488644079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178753950440257303050877 67032731415096488644079)
                ·
                  rfl

theorem cell19_220296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_220296 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220296 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220296 prefixEnd_220296 := by exact prefixLift 220296
  have htrace : WordTrace (prefixWord ++ tailWord_220296) baseStart_220296 baseEnd_220296 := by
    simpa [prefixWord, tailWord_220296, baseEnd_220296] using wordTrace_append hprefix tailTrace_220296
  have hstable : (prefixWord ++ tailWord_220296).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220296).length < 2 ^ (prefixWord ++ tailWord_220296).sum := by decide
  have hdescent : baseEnd_220296 < baseStart_220296 := by decide
  rcases family_descends (prefixWord ++ tailWord_220296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220338 : List Nat := [3, 2, 1, 1, 1, 5, 2, 4]
def baseStart_220338 : Nat := 118140960795 + 220338 * 2 ^ 59
def prefixEnd_220338 : Nat := 4983230072969 + 3 ^ 40 * 220338 * 2
def baseEnd_220338 : Nat := 67045511378052835710631

theorem tailTrace_220338 : CollatzResearch.WordTrace tailWord_220338 prefixEnd_220338 67045511378052835710631 := by
  unfold tailWord_220338
  simp only [CollatzResearch.WordTrace]
  refine ⟨2009096768940132894893417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5357591383840354386382445 2009096768940132894893417)
  ·
    refine ⟨1506822576705099671170063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2009096768940132894893417 1506822576705099671170063)
    ·
      refine ⟨2260233865057649506755095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1506822576705099671170063 2260233865057649506755095)
      ·
        refine ⟨3390350797586474260132643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2260233865057649506755095 3390350797586474260132643)
        ·
          refine ⟨5085526196379711390198965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3390350797586474260132643 5085526196379711390198965)
          ·
            refine ⟨476768080910597942831153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5085526196379711390198965 476768080910597942831153)
            ·
              refine ⟨357576060682948457123365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 476768080910597942831153 357576060682948457123365)
              ·
                refine ⟨67045511378052835710631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357576060682948457123365 67045511378052835710631)
                ·
                  rfl

theorem cell19_220338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_220338 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220338 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220338 prefixEnd_220338 := by exact prefixLift 220338
  have htrace : WordTrace (prefixWord ++ tailWord_220338) baseStart_220338 baseEnd_220338 := by
    simpa [prefixWord, tailWord_220338, baseEnd_220338] using wordTrace_append hprefix tailTrace_220338
  have hstable : (prefixWord ++ tailWord_220338).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220338).length < 2 ^ (prefixWord ++ tailWord_220338).sum := by decide
  have hdescent : baseEnd_220338 < baseStart_220338 := by decide
  rcases family_descends (prefixWord ++ tailWord_220338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220374 : List Nat := [5, 2, 1, 2, 2, 7]
def baseStart_220374 : Nat := 118140960795 + 220374 * 2 ^ 59
def prefixEnd_220374 : Nat := 4983230072969 + 3 ^ 40 * 220374 * 2
def baseEnd_220374 : Nat := 7450718403557268767837

theorem tailTrace_220374 : CollatzResearch.WordTrace tailWord_220374 prefixEnd_220374 7450718403557268767837 := by
  unfold tailWord_220374
  simp only [CollatzResearch.WordTrace]
  refine ⟨502356256476881857992761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5358466735753406485256117 502356256476881857992761)
  ·
    refine ⟨376767192357661393494571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 502356256476881857992761 376767192357661393494571)
    ·
      refine ⟨565150788536492090241857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 376767192357661393494571 565150788536492090241857)
      ·
        refine ⟨423863091402369067681393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 565150788536492090241857 423863091402369067681393)
        ·
          refine ⟨317897318551776800761045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 423863091402369067681393 317897318551776800761045)
          ·
            refine ⟨7450718403557268767837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 317897318551776800761045 7450718403557268767837)
            ·
              rfl

theorem cell19_220374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 7].length) (baseStart_220374 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220374 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220374 prefixEnd_220374 := by exact prefixLift 220374
  have htrace : WordTrace (prefixWord ++ tailWord_220374) baseStart_220374 baseEnd_220374 := by
    simpa [prefixWord, tailWord_220374, baseEnd_220374] using wordTrace_append hprefix tailTrace_220374
  have hstable : (prefixWord ++ tailWord_220374).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220374).length < 2 ^ (prefixWord ++ tailWord_220374).sum := by decide
  have hdescent : baseEnd_220374 < baseStart_220374 := by decide
  rcases family_descends (prefixWord ++ tailWord_220374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220376 : List Nat := [2, 1, 2, 2, 6, 6]
def baseStart_220376 : Nat := 118140960795 + 220376 * 2 ^ 59
def prefixEnd_220376 : Nat := 4983230072969 + 3 ^ 40 * 220376 * 2
def baseEnd_220376 : Nat := 7450786022408889651787

theorem tailTrace_220376 : CollatzResearch.WordTrace tailWord_220376 prefixEnd_220376 7450786022408889651787 := by
  unfold tailWord_220376
  simp only [CollatzResearch.WordTrace]
  refine ⟨4018886524811432034728491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5358515366415242712971321 4018886524811432034728491)
  ·
    refine ⟨6028329787217148052092737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4018886524811432034728491 6028329787217148052092737)
    ·
      refine ⟨4521247340412861039069553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6028329787217148052092737 4521247340412861039069553)
      ·
        refine ⟨3390935505309645779302165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4521247340412861039069553 3390935505309645779302165)
        ·
          refine ⟨158950101811389645904789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 3390935505309645779302165 158950101811389645904789)
          ·
            refine ⟨7450786022408889651787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 158950101811389645904789 7450786022408889651787)
            ·
              rfl

theorem cell19_220376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 6].length) (baseStart_220376 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220376 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220376 prefixEnd_220376 := by exact prefixLift 220376
  have htrace : WordTrace (prefixWord ++ tailWord_220376) baseStart_220376 baseEnd_220376 := by
    simpa [prefixWord, tailWord_220376, baseEnd_220376] using wordTrace_append hprefix tailTrace_220376
  have hstable : (prefixWord ++ tailWord_220376).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220376).length < 2 ^ (prefixWord ++ tailWord_220376).sum := by decide
  have hdescent : baseEnd_220376 < baseStart_220376 := by decide
  rcases family_descends (prefixWord ++ tailWord_220376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220391 : List Nat := [1, 1, 5, 3, 3, 1, 1, 4]
def baseStart_220391 : Nat := 118140960795 + 220391 * 2 ^ 59
def prefixEnd_220391 : Nat := 4983230072969 + 3 ^ 40 * 220391 * 2
def baseEnd_220391 : Nat := 67061638474164416532709

theorem tailTrace_220391 : CollatzResearch.WordTrace tailWord_220391 prefixEnd_220391 67061638474164416532709 := by
  unfold tailWord_220391
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038320144568521631253027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5358880096379014420835351 8038320144568521631253027)
  ·
    refine ⟨12057480216852782446879541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8038320144568521631253027 12057480216852782446879541)
    ·
      refine ⟨1130388770329948354394957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 12057480216852782446879541 1130388770329948354394957)
      ·
        refine ⟨423895788873730632898109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1130388770329948354394957 423895788873730632898109)
        ·
          refine ⟨158960920827648987336791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 423895788873730632898109 158960920827648987336791)
          ·
            refine ⟨238441381241473481005187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158960920827648987336791 238441381241473481005187)
            ·
              refine ⟨357662071862210221507781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238441381241473481005187 357662071862210221507781)
              ·
                refine ⟨67061638474164416532709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357662071862210221507781 67061638474164416532709)
                ·
                  rfl

theorem cell19_220391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 4].length) (baseStart_220391 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220391 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220391 prefixEnd_220391 := by exact prefixLift 220391
  have htrace : WordTrace (prefixWord ++ tailWord_220391) baseStart_220391 baseEnd_220391 := by
    simpa [prefixWord, tailWord_220391, baseEnd_220391] using wordTrace_append hprefix tailTrace_220391
  have hstable : (prefixWord ++ tailWord_220391).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220391).length < 2 ^ (prefixWord ++ tailWord_220391).sum := by decide
  have hdescent : baseEnd_220391 < baseStart_220391 := by decide
  rcases family_descends (prefixWord ++ tailWord_220391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220395 : List Nat := [1, 1, 1, 1, 2, 8, 1, 4]
def baseStart_220395 : Nat := 118140960795 + 220395 * 2 ^ 59
def prefixEnd_220395 : Nat := 4983230072969 + 3 ^ 40 * 220395 * 2
def baseEnd_220395 : Nat := 67062855613493592443809

theorem tailTrace_220395 : CollatzResearch.WordTrace tailWord_220395 prefixEnd_220395 67062855613493592443809 := by
  unfold tailWord_220395
  simp only [CollatzResearch.WordTrace]
  refine ⟨8038466036554030314398639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5358977357702686876265759 8038466036554030314398639)
  ·
    refine ⟨12057699054831045471597959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8038466036554030314398639 12057699054831045471597959)
    ·
      refine ⟨18086548582246568207396939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12057699054831045471597959 18086548582246568207396939)
      ·
        refine ⟨27129822873369852311095409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18086548582246568207396939 27129822873369852311095409)
        ·
          refine ⟨20347367155027389233321557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27129822873369852311095409 20347367155027389233321557)
          ·
            refine ⟨238445708847977217577987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 20347367155027389233321557 238445708847977217577987)
            ·
              refine ⟨357668563271965826366981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238445708847977217577987 357668563271965826366981)
              ·
                refine ⟨67062855613493592443809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357668563271965826366981 67062855613493592443809)
                ·
                  rfl

theorem cell19_220395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 4].length) (baseStart_220395 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220395 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220395 prefixEnd_220395 := by exact prefixLift 220395
  have htrace : WordTrace (prefixWord ++ tailWord_220395) baseStart_220395 baseEnd_220395 := by
    simpa [prefixWord, tailWord_220395, baseEnd_220395] using wordTrace_append hprefix tailTrace_220395
  have hstable : (prefixWord ++ tailWord_220395).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220395).length < 2 ^ (prefixWord ++ tailWord_220395).sum := by decide
  have hdescent : baseEnd_220395 < baseStart_220395 := by decide
  rcases family_descends (prefixWord ++ tailWord_220395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220412 : List Nat := [2, 2, 2, 1, 5, 1, 3, 3]
def baseStart_220412 : Nat := 118140960795 + 220412 * 2 ^ 59
def prefixEnd_220412 : Nat := 4983230072969 + 3 ^ 40 * 220412 * 2
def baseEnd_220412 : Nat := 67068028455642590065985

theorem tailTrace_220412 : CollatzResearch.WordTrace tailWord_220412 prefixEnd_220412 67068028455642590065985 := by
  unfold tailWord_220412
  simp only [CollatzResearch.WordTrace]
  refine ⟨4019543038746221108883745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5359390718328294811844993 4019543038746221108883745)
  ·
    refine ⟨3014657279059665831662809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4019543038746221108883745 3014657279059665831662809)
    ·
      refine ⟨2260992959294749373747107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3014657279059665831662809 2260992959294749373747107)
      ·
        refine ⟨3391489438942124060620661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2260992959294749373747107 3391489438942124060620661)
        ·
          refine ⟨317952134900824130683187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3391489438942124060620661 317952134900824130683187)
          ·
            refine ⟨476928202351236196024781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 317952134900824130683187 476928202351236196024781)
            ·
              refine ⟨178848075881713573509293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 476928202351236196024781 178848075881713573509293)
              ·
                refine ⟨67068028455642590065985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178848075881713573509293 67068028455642590065985)
                ·
                  rfl

theorem cell19_220412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 1, 3, 3].length) (baseStart_220412 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220412 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220412 prefixEnd_220412 := by exact prefixLift 220412
  have htrace : WordTrace (prefixWord ++ tailWord_220412) baseStart_220412 baseEnd_220412 := by
    simpa [prefixWord, tailWord_220412, baseEnd_220412] using wordTrace_append hprefix tailTrace_220412
  have hstable : (prefixWord ++ tailWord_220412).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220412).length < 2 ^ (prefixWord ++ tailWord_220412).sum := by decide
  have hdescent : baseEnd_220412 < baseStart_220412 := by decide
  rcases family_descends (prefixWord ++ tailWord_220412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220469 : List Nat := [1, 3, 3, 1, 2, 4, 2, 3]
def baseStart_220469 : Nat := 118140960795 + 220469 * 2 ^ 59
def prefixEnd_220469 : Nat := 4983230072969 + 3 ^ 40 * 220469 * 2
def baseEnd_220469 : Nat := 67085372691083346799163

theorem tailTrace_220469 : CollatzResearch.WordTrace tailWord_220469 prefixEnd_220469 67085372691083346799163 := by
  unfold tailWord_220469
  simp only [CollatzResearch.WordTrace]
  refine ⟨8041165038285940952592461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5360776692190627301728307 8041165038285940952592461)
  ·
    refine ⟨3015436889357227857222173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8041165038285940952592461 3015436889357227857222173)
    ·
      refine ⟨1130788833508960446458315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3015436889357227857222173 1130788833508960446458315)
      ·
        refine ⟨1696183250263440669687473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1130788833508960446458315 1696183250263440669687473)
        ·
          refine ⟨1272137437697580502265605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1696183250263440669687473 1272137437697580502265605)
          ·
            refine ⟨238525769568296344174801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1272137437697580502265605 238525769568296344174801)
            ·
              refine ⟨178894327176222258131101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 238525769568296344174801 178894327176222258131101)
              ·
                refine ⟨67085372691083346799163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 178894327176222258131101 67085372691083346799163)
                ·
                  rfl

theorem cell19_220469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 2, 3].length) (baseStart_220469 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220469 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220469 prefixEnd_220469 := by exact prefixLift 220469
  have htrace : WordTrace (prefixWord ++ tailWord_220469) baseStart_220469 baseEnd_220469 := by
    simpa [prefixWord, tailWord_220469, baseEnd_220469] using wordTrace_append hprefix tailTrace_220469
  have hstable : (prefixWord ++ tailWord_220469).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220469).length < 2 ^ (prefixWord ++ tailWord_220469).sum := by decide
  have hdescent : baseEnd_220469 < baseStart_220469 := by decide
  rcases family_descends (prefixWord ++ tailWord_220469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220492 : List Nat := [2, 2, 1, 3, 2, 2, 7]
def baseStart_220492 : Nat := 118140960795 + 220492 * 2 ^ 59
def prefixEnd_220492 : Nat := 4983230072969 + 3 ^ 40 * 220492 * 2
def baseEnd_220492 : Nat := 22364123747408702762663

theorem tailTrace_220492 : CollatzResearch.WordTrace tailWord_220492 prefixEnd_220492 22364123747408702762663 := by
  unfold tailWord_220492
  simp only [CollatzResearch.WordTrace]
  refine ⟨4021001958601307940339865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5361335944801743920453153 4021001958601307940339865)
  ·
    refine ⟨3015751468950980955254899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4021001958601307940339865 3015751468950980955254899)
    ·
      refine ⟨4523627203426471432882349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3015751468950980955254899 4523627203426471432882349)
      ·
        refine ⟨1696360201284926787330881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4523627203426471432882349 1696360201284926787330881)
        ·
          refine ⟨1272270150963695090498161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1696360201284926787330881 1272270150963695090498161)
          ·
            refine ⟨954202613222771317873621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1272270150963695090498161 954202613222771317873621)
            ·
              refine ⟨22364123747408702762663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 954202613222771317873621 22364123747408702762663)
              ·
                rfl

theorem cell19_220492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_220492 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220492 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220492 prefixEnd_220492 := by exact prefixLift 220492
  have htrace : WordTrace (prefixWord ++ tailWord_220492) baseStart_220492 baseEnd_220492 := by
    simpa [prefixWord, tailWord_220492, baseEnd_220492] using wordTrace_append hprefix tailTrace_220492
  have hstable : (prefixWord ++ tailWord_220492).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220492).length < 2 ^ (prefixWord ++ tailWord_220492).sum := by decide
  have hdescent : baseEnd_220492 < baseStart_220492 := by decide
  rcases family_descends (prefixWord ++ tailWord_220492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220530 : List Nat := [3, 2, 1, 2, 1, 2, 1, 7]
def baseStart_220530 : Nat := 118140960795 + 220530 * 2 ^ 59
def prefixEnd_220530 : Nat := 4983230072969 + 3 ^ 40 * 220530 * 2
def baseEnd_220530 : Nat := 67103934065853279443441

theorem tailTrace_220530 : CollatzResearch.WordTrace tailWord_220530 prefixEnd_220530 67103934065853279443441 := by
  unfold tailWord_220530
  simp only [CollatzResearch.WordTrace]
  refine ⟨2010847472766237092640761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5362259927376632247042029 2010847472766237092640761)
  ·
    refine ⟨1508135604574677819480571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2010847472766237092640761 1508135604574677819480571)
    ·
      refine ⟨2262203406862016729220857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1508135604574677819480571 2262203406862016729220857)
      ·
        refine ⟨1696652555146512546915643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2262203406862016729220857 1696652555146512546915643)
        ·
          refine ⟨2544978832719768820373465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1696652555146512546915643 2544978832719768820373465)
          ·
            refine ⟨1908734124539826615280099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2544978832719768820373465 1908734124539826615280099)
            ·
              refine ⟨2863101186809739922920149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1908734124539826615280099 2863101186809739922920149)
              ·
                refine ⟨67103934065853279443441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2863101186809739922920149 67103934065853279443441)
                ·
                  rfl

theorem cell19_220530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 7].length) (baseStart_220530 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220530 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220530 prefixEnd_220530 := by exact prefixLift 220530
  have htrace : WordTrace (prefixWord ++ tailWord_220530) baseStart_220530 baseEnd_220530 := by
    simpa [prefixWord, tailWord_220530, baseEnd_220530] using wordTrace_append hprefix tailTrace_220530
  have hstable : (prefixWord ++ tailWord_220530).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220530).length < 2 ^ (prefixWord ++ tailWord_220530).sum := by decide
  have hdescent : baseEnd_220530 < baseStart_220530 := by decide
  rcases family_descends (prefixWord ++ tailWord_220530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220562 : List Nat := [3, 2, 3, 3, 1, 2, 1, 4]
def baseStart_220562 : Nat := 118140960795 + 220562 * 2 ^ 59
def prefixEnd_220562 : Nat := 4983230072969 + 3 ^ 40 * 220562 * 2
def baseEnd_220562 : Nat := 67113671180486686732243

theorem tailTrace_220562 : CollatzResearch.WordTrace tailWord_220562 prefixEnd_220562 67113671180486686732243 := by
  unfold tailWord_220562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2011139256737254458931985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5363038017966011890485293 2011139256737254458931985)
  ·
    refine ⟨1508354442552940844198989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2011139256737254458931985 1508354442552940844198989)
    ·
      refine ⟨565632915957352816574621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1508354442552940844198989 565632915957352816574621)
      ·
        refine ⟨212112343484007306215483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 565632915957352816574621 212112343484007306215483)
        ·
          refine ⟨318168515226010959323225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 212112343484007306215483 318168515226010959323225)
          ·
            refine ⟨238626386419508219492419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 318168515226010959323225 238626386419508219492419)
            ·
              refine ⟨357939579629262329238629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238626386419508219492419 357939579629262329238629)
              ·
                refine ⟨67113671180486686732243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357939579629262329238629 67113671180486686732243)
                ·
                  rfl

theorem cell19_220562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 2, 1, 4].length) (baseStart_220562 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220562 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220562 prefixEnd_220562 := by exact prefixLift 220562
  have htrace : WordTrace (prefixWord ++ tailWord_220562) baseStart_220562 baseEnd_220562 := by
    simpa [prefixWord, tailWord_220562, baseEnd_220562] using wordTrace_append hprefix tailTrace_220562
  have hstable : (prefixWord ++ tailWord_220562).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220562).length < 2 ^ (prefixWord ++ tailWord_220562).sum := by decide
  have hdescent : baseEnd_220562 < baseStart_220562 := by decide
  rcases family_descends (prefixWord ++ tailWord_220562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220564 : List Nat := [2, 4, 2, 1, 2, 3, 1, 4]
def baseStart_220564 : Nat := 118140960795 + 220564 * 2 ^ 59
def prefixEnd_220564 : Nat := 4983230072969 + 3 ^ 40 * 220564 * 2
def baseEnd_220564 : Nat := 67114279750151274687793

theorem tailTrace_220564 : CollatzResearch.WordTrace tailWord_220564 prefixEnd_220564 67114279750151274687793 := by
  unfold tailWord_220564
  simp only [CollatzResearch.WordTrace]
  refine ⟨4022314986470886088650373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5363086648627848118200497 4022314986470886088650373)
  ·
    refine ⟨754184059963291141621945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4022314986470886088650373 754184059963291141621945)
    ·
      refine ⟨565638044972468356216459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 754184059963291141621945 565638044972468356216459)
      ·
        refine ⟨848457067458702534324689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 565638044972468356216459 848457067458702534324689)
        ·
          refine ⟨636342800594026900743517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 848457067458702534324689 636342800594026900743517)
          ·
            refine ⟨238628550222760087778819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 636342800594026900743517 238628550222760087778819)
            ·
              refine ⟨357942825334140131668229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 238628550222760087778819 357942825334140131668229)
              ·
                refine ⟨67114279750151274687793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 357942825334140131668229 67114279750151274687793)
                ·
                  rfl

theorem cell19_220564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 4].length) (baseStart_220564 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220564 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220564 prefixEnd_220564 := by exact prefixLift 220564
  have htrace : WordTrace (prefixWord ++ tailWord_220564) baseStart_220564 baseEnd_220564 := by
    simpa [prefixWord, tailWord_220564, baseEnd_220564] using wordTrace_append hprefix tailTrace_220564
  have hstable : (prefixWord ++ tailWord_220564).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220564).length < 2 ^ (prefixWord ++ tailWord_220564).sum := by decide
  have hdescent : baseEnd_220564 < baseStart_220564 := by decide
  rcases family_descends (prefixWord ++ tailWord_220564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220604 : List Nat := [2, 2, 2, 4, 2, 1, 6]
def baseStart_220604 : Nat := 118140960795 + 220604 * 2 ^ 59
def prefixEnd_220604 : Nat := 4983230072969 + 3 ^ 40 * 220604 * 2
def baseEnd_220604 : Nat := 22375483714481011266265

theorem tailTrace_220604 : CollatzResearch.WordTrace tailWord_220604 prefixEnd_220604 22375483714481011266265 := by
  unfold tailWord_220604
  simp only [CollatzResearch.WordTrace]
  refine ⟨4023044446398429504378433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5364059261864572672504577 4023044446398429504378433)
  ·
    refine ⟨3017283334798822128283825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4023044446398429504378433 3017283334798822128283825)
    ·
      refine ⟨2262962501099116596212869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3017283334798822128283825 2262962501099116596212869)
      ·
        refine ⟨424305468956084361789913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2262962501099116596212869 424305468956084361789913)
        ·
          refine ⟨318229101717063271342435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 424305468956084361789913 318229101717063271342435)
          ·
            refine ⟨477343652575594907013653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 318229101717063271342435 477343652575594907013653)
            ·
              refine ⟨22375483714481011266265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 477343652575594907013653 22375483714481011266265)
              ·
                rfl

theorem cell19_220604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 6].length) (baseStart_220604 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220604 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220604 prefixEnd_220604 := by exact prefixLift 220604
  have htrace : WordTrace (prefixWord ++ tailWord_220604) baseStart_220604 baseEnd_220604 := by
    simpa [prefixWord, tailWord_220604, baseEnd_220604] using wordTrace_append hprefix tailTrace_220604
  have hstable : (prefixWord ++ tailWord_220604).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220604).length < 2 ^ (prefixWord ++ tailWord_220604).sum := by decide
  have hdescent : baseEnd_220604 < baseStart_220604 := by decide
  rcases family_descends (prefixWord ++ tailWord_220604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220661 : List Nat := [1, 3, 5, 1, 1, 1, 7]
def baseStart_220661 : Nat := 118140960795 + 220661 * 2 ^ 59
def prefixEnd_220661 : Nat := 4983230072969 + 3 ^ 40 * 220661 * 2
def baseEnd_220661 : Nat := 22381265126294596843991

theorem tailTrace_220661 : CollatzResearch.WordTrace tailWord_220661 prefixEnd_220661 22381265126294596843991 := by
  unfold tailWord_220661
  simp only [CollatzResearch.WordTrace]
  refine ⟨8048167853590357743581837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5365445235726905162387891 8048167853590357743581837)
  ·
    refine ⟨3018062945096384153843189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8048167853590357743581837 3018062945096384153843189)
    ·
      refine ⟨282943401102786014422799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3018062945096384153843189 282943401102786014422799)
      ·
        refine ⟨424415101654179021634199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 282943401102786014422799 424415101654179021634199)
        ·
          refine ⟨636622652481268532451299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424415101654179021634199 636622652481268532451299)
          ·
            refine ⟨954933978721902798676949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 636622652481268532451299 954933978721902798676949)
            ·
              refine ⟨22381265126294596843991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 954933978721902798676949 22381265126294596843991)
              ·
                rfl

theorem cell19_220661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_220661 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220661 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220661 prefixEnd_220661 := by exact prefixLift 220661
  have htrace : WordTrace (prefixWord ++ tailWord_220661) baseStart_220661 baseEnd_220661 := by
    simpa [prefixWord, tailWord_220661, baseEnd_220661] using wordTrace_append hprefix tailTrace_220661
  have hstable : (prefixWord ++ tailWord_220661).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220661).length < 2 ^ (prefixWord ++ tailWord_220661).sum := by decide
  have hdescent : baseEnd_220661 < baseStart_220661 := by decide
  rcases family_descends (prefixWord ++ tailWord_220661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220682 : List Nat := [3, 1, 2, 2, 2, 2, 1, 6]
def baseStart_220682 : Nat := 118140960795 + 220682 * 2 ^ 59
def prefixEnd_220682 : Nat := 4983230072969 + 3 ^ 40 * 220682 * 2
def baseEnd_220682 : Nat := 67150185360361964065249

theorem tailTrace_220682 : CollatzResearch.WordTrace tailWord_220682 prefixEnd_220682 67150185360361964065249 := by
  unfold tailWord_220682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2012233446628569582524075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5365955857676185553397533 2012233446628569582524075)
  ·
    refine ⟨3018350169942854373786113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2012233446628569582524075 3018350169942854373786113)
    ·
      refine ⟨2263762627457140780339585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3018350169942854373786113 2263762627457140780339585)
      ·
        refine ⟨1697821970592855585254689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2263762627457140780339585 1697821970592855585254689)
        ·
          refine ⟨1273366477944641688941017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1697821970592855585254689 1273366477944641688941017)
          ·
            refine ⟨955024858458481266705763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1273366477944641688941017 955024858458481266705763)
            ·
              refine ⟨1432537287687721900058645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 955024858458481266705763 1432537287687721900058645)
              ·
                refine ⟨67150185360361964065249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1432537287687721900058645 67150185360361964065249)
                ·
                  rfl

theorem cell19_220682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_220682 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220682 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220682 prefixEnd_220682 := by exact prefixLift 220682
  have htrace : WordTrace (prefixWord ++ tailWord_220682) baseStart_220682 baseEnd_220682 := by
    simpa [prefixWord, tailWord_220682, baseEnd_220682] using wordTrace_append hprefix tailTrace_220682
  have hstable : (prefixWord ++ tailWord_220682).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220682).length < 2 ^ (prefixWord ++ tailWord_220682).sum := by decide
  have hdescent : baseEnd_220682 < baseStart_220682 := by decide
  rcases family_descends (prefixWord ++ tailWord_220682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220701 : List Nat := [1, 4, 2, 2, 1, 1, 1, 7]
def baseStart_220701 : Nat := 118140960795 + 220701 * 2 ^ 59
def prefixEnd_220701 : Nat := 4983230072969 + 3 ^ 40 * 220701 * 2
def baseEnd_220701 : Nat := 67155966772175549642975

theorem tailTrace_220701 : CollatzResearch.WordTrace tailWord_220701 prefixEnd_220701 67155966772175549642975 := by
  unfold tailWord_220701
  simp only [CollatzResearch.WordTrace]
  refine ⟨8049626773445444575037957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5366417848963629716691971 8049626773445444575037957)
  ·
    refine ⟨1509305020021020857819617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 8049626773445444575037957 1509305020021020857819617)
    ·
      refine ⟨1131978765015765643364713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1509305020021020857819617 1131978765015765643364713)
      ·
        refine ⟨848984073761824232523535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1131978765015765643364713 848984073761824232523535)
        ·
          refine ⟨1273476110642736348785303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 848984073761824232523535 1273476110642736348785303)
          ·
            refine ⟨1910214165964104523177955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1273476110642736348785303 1910214165964104523177955)
            ·
              refine ⟨2865321248946156784766933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1910214165964104523177955 2865321248946156784766933)
              ·
                refine ⟨67155966772175549642975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2865321248946156784766933 67155966772175549642975)
                ·
                  rfl

theorem cell19_220701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 7].length) (baseStart_220701 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220701 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220701 prefixEnd_220701 := by exact prefixLift 220701
  have htrace : WordTrace (prefixWord ++ tailWord_220701) baseStart_220701 baseEnd_220701 := by
    simpa [prefixWord, tailWord_220701, baseEnd_220701] using wordTrace_append hprefix tailTrace_220701
  have hstable : (prefixWord ++ tailWord_220701).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220701).length < 2 ^ (prefixWord ++ tailWord_220701).sum := by decide
  have hdescent : baseEnd_220701 < baseStart_220701 := by decide
  rcases family_descends (prefixWord ++ tailWord_220701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220756 : List Nat := [2, 4, 1, 1, 1, 2, 5, 3]
def baseStart_220756 : Nat := 118140960795 + 220756 * 2 ^ 59
def prefixEnd_220756 : Nat := 4983230072969 + 3 ^ 40 * 220756 * 2
def baseEnd_220756 : Nat := 67172702437951718420603

theorem tailTrace_220756 : CollatzResearch.WordTrace tailWord_220756 prefixEnd_220756 67172702437951718420603 := by
  unfold tailWord_220756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4025816394123094484145061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5367755192164125978860081 4025816394123094484145061)
  ·
    refine ⟨754840573898080215777199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4025816394123094484145061 754840573898080215777199)
    ·
      refine ⟨1132260860847120323665799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 754840573898080215777199 1132260860847120323665799)
      ·
        refine ⟨1698391291270680485498699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1132260860847120323665799 1698391291270680485498699)
        ·
          refine ⟨2547586936906020728248049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1698391291270680485498699 2547586936906020728248049)
          ·
            refine ⟨1910690202679515546186037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2547586936906020728248049 1910690202679515546186037)
            ·
              refine ⟨179127206501204582454941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1910690202679515546186037 179127206501204582454941)
              ·
                refine ⟨67172702437951718420603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179127206501204582454941 67172702437951718420603)
                ·
                  rfl

theorem cell19_220756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 5, 3].length) (baseStart_220756 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220756 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220756 prefixEnd_220756 := by exact prefixLift 220756
  have htrace : WordTrace (prefixWord ++ tailWord_220756) baseStart_220756 baseEnd_220756 := by
    simpa [prefixWord, tailWord_220756, baseEnd_220756] using wordTrace_append hprefix tailTrace_220756
  have hstable : (prefixWord ++ tailWord_220756).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220756).length < 2 ^ (prefixWord ++ tailWord_220756).sum := by decide
  have hdescent : baseEnd_220756 < baseStart_220756 := by decide
  rcases family_descends (prefixWord ++ tailWord_220756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220912 : List Nat := [2, 1, 1, 1, 3, 1, 2, 8]
def baseStart_220912 : Nat := 118140960795 + 220912 * 2 ^ 59
def prefixEnd_220912 : Nat := 4983230072969 + 3 ^ 40 * 220912 * 2
def baseEnd_220912 : Nat := 67220170871789578953511

theorem tailTrace_220912 : CollatzResearch.WordTrace tailWord_220912 prefixEnd_220912 67220170871789578953511 := by
  unfold tailWord_220912
  simp only [CollatzResearch.WordTrace]
  refine ⟨4028661287840513805484495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5371548383787351740645993 4028661287840513805484495)
  ·
    refine ⟨6042991931760770708226743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4028661287840513805484495 6042991931760770708226743)
    ·
      refine ⟨9064487897641156062340115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6042991931760770708226743 9064487897641156062340115)
      ·
        refine ⟨13596731846461734093510173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9064487897641156062340115 13596731846461734093510173)
        ·
          refine ⟨5098774442423150285066315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13596731846461734093510173 5098774442423150285066315)
          ·
            refine ⟨7648161663634725427599473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5098774442423150285066315 7648161663634725427599473)
            ·
              refine ⟨5736121247726044070699605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7648161663634725427599473 5736121247726044070699605)
              ·
                refine ⟨67220170871789578953511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5736121247726044070699605 67220170871789578953511)
                ·
                  rfl

theorem cell19_220912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 8].length) (baseStart_220912 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220912 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220912 prefixEnd_220912 := by exact prefixLift 220912
  have htrace : WordTrace (prefixWord ++ tailWord_220912) baseStart_220912 baseEnd_220912 := by
    simpa [prefixWord, tailWord_220912, baseEnd_220912] using wordTrace_append hprefix tailTrace_220912
  have hstable : (prefixWord ++ tailWord_220912).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220912).length < 2 ^ (prefixWord ++ tailWord_220912).sum := by decide
  have hdescent : baseEnd_220912 < baseStart_220912 := by decide
  rcases family_descends (prefixWord ++ tailWord_220912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220931 : List Nat := [1, 1, 1, 3, 2, 2, 2, 7]
def baseStart_220931 : Nat := 118140960795 + 220931 * 2 ^ 59
def prefixEnd_220931 : Nat := 4983230072969 + 3 ^ 40 * 220931 * 2
def baseEnd_220931 : Nat := 67225952283603164531237

theorem tailTrace_220931 : CollatzResearch.WordTrace tailWord_220931 prefixEnd_220931 67225952283603164531237 := by
  unfold tailWord_220931
  simp only [CollatzResearch.WordTrace]
  refine ⟨8058015562612193855910647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5372010375074795903940431 8058015562612193855910647)
  ·
    refine ⟨12087023343918290783865971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8058015562612193855910647 12087023343918290783865971)
    ·
      refine ⟨18130535015877436175798957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12087023343918290783865971 18130535015877436175798957)
      ·
        refine ⟨6798950630954038565924609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18130535015877436175798957 6798950630954038565924609)
        ·
          refine ⟨5099212973215528924443457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6798950630954038565924609 5099212973215528924443457)
          ·
            refine ⟨3824409729911646693332593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5099212973215528924443457 3824409729911646693332593)
            ·
              refine ⟨2868307297433735019999445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3824409729911646693332593 2868307297433735019999445)
              ·
                refine ⟨67225952283603164531237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2868307297433735019999445 67225952283603164531237)
                ·
                  rfl

theorem cell19_220931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_220931 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220931 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220931 prefixEnd_220931 := by exact prefixLift 220931
  have htrace : WordTrace (prefixWord ++ tailWord_220931) baseStart_220931 baseEnd_220931 := by
    simpa [prefixWord, tailWord_220931, baseEnd_220931] using wordTrace_append hprefix tailTrace_220931
  have hstable : (prefixWord ++ tailWord_220931).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220931).length < 2 ^ (prefixWord ++ tailWord_220931).sum := by decide
  have hdescent : baseEnd_220931 < baseStart_220931 := by decide
  rcases family_descends (prefixWord ++ tailWord_220931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220946 : List Nat := [3, 2, 4, 1, 1, 2, 6]
def baseStart_220946 : Nat := 118140960795 + 220946 * 2 ^ 59
def prefixEnd_220946 : Nat := 4983230072969 + 3 ^ 40 * 220946 * 2
def baseEnd_220946 : Nat := 22410172185362524732621

theorem tailTrace_220946 : CollatzResearch.WordTrace tailWord_220946 prefixEnd_220946 22410172185362524732621 := by
  unfold tailWord_220946
  simp only [CollatzResearch.WordTrace]
  refine ⟨2014640664389462854426673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5372375105038567611804461 2014640664389462854426673)
  ·
    refine ⟨1510980498292097140820005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2014640664389462854426673 1510980498292097140820005)
    ·
      refine ⟨283308843429768213903751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1510980498292097140820005 283308843429768213903751)
      ·
        refine ⟨424963265144652320855627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 283308843429768213903751 424963265144652320855627)
        ·
          refine ⟨637444897716978481283441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 424963265144652320855627 637444897716978481283441)
          ·
            refine ⟨478083673287733860962581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637444897716978481283441 478083673287733860962581)
            ·
              refine ⟨22410172185362524732621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 478083673287733860962581 22410172185362524732621)
              ·
                rfl

theorem cell19_220946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 6].length) (baseStart_220946 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220946 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220946 prefixEnd_220946 := by exact prefixLift 220946
  have htrace : WordTrace (prefixWord ++ tailWord_220946) baseStart_220946 baseEnd_220946 := by
    simpa [prefixWord, tailWord_220946, baseEnd_220946] using wordTrace_append hprefix tailTrace_220946
  have hstable : (prefixWord ++ tailWord_220946).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220946).length < 2 ^ (prefixWord ++ tailWord_220946).sum := by decide
  have hdescent : baseEnd_220946 < baseStart_220946 := by decide
  rcases family_descends (prefixWord ++ tailWord_220946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220982 : List Nat := [5, 1, 2, 2, 1, 1, 4, 3]
def baseStart_220982 : Nat := 118140960795 + 220982 * 2 ^ 59
def prefixEnd_220982 : Nat := 4983230072969 + 3 ^ 40 * 220982 * 2
def baseEnd_220982 : Nat := 67241470810050157397765

theorem tailTrace_220982 : CollatzResearch.WordTrace tailWord_220982 prefixEnd_220982 67241470810050157397765 := by
  unfold tailWord_220982
  simp only [CollatzResearch.WordTrace]
  refine ⟨503742230339214347876075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 5373250456951619710678133 503742230339214347876075)
  ·
    refine ⟨755613345508821521814113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 503742230339214347876075 755613345508821521814113)
    ·
      refine ⟨566710009131616141360585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 755613345508821521814113 566710009131616141360585)
      ·
        refine ⟨425032506848712106020439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 566710009131616141360585 425032506848712106020439)
        ·
          refine ⟨637548760273068159030659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 425032506848712106020439 637548760273068159030659)
          ·
            refine ⟨956323140409602238545989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 637548760273068159030659 956323140409602238545989)
            ·
              refine ⟨179310588826800419727373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 956323140409602238545989 179310588826800419727373)
              ·
                refine ⟨67241470810050157397765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179310588826800419727373 67241470810050157397765)
                ·
                  rfl

theorem cell19_220982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_220982 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220982 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220982 prefixEnd_220982 := by exact prefixLift 220982
  have htrace : WordTrace (prefixWord ++ tailWord_220982) baseStart_220982 baseEnd_220982 := by
    simpa [prefixWord, tailWord_220982, baseEnd_220982] using wordTrace_append hprefix tailTrace_220982
  have hstable : (prefixWord ++ tailWord_220982).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220982).length < 2 ^ (prefixWord ++ tailWord_220982).sum := by decide
  have hdescent : baseEnd_220982 < baseStart_220982 := by decide
  rcases family_descends (prefixWord ++ tailWord_220982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220984 : List Nat := [2, 1, 2, 1, 3, 5, 2, 3]
def baseStart_220984 : Nat := 118140960795 + 220984 * 2 ^ 59
def prefixEnd_220984 : Nat := 4983230072969 + 3 ^ 40 * 220984 * 2
def baseEnd_220984 : Nat := 67242079379714745353315

theorem tailTrace_220984 : CollatzResearch.WordTrace tailWord_220984 prefixEnd_220984 67242079379714745353315 := by
  unfold tailWord_220984
  simp only [CollatzResearch.WordTrace]
  refine ⟨4029974315710091953795003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5373299087613455938393337 4029974315710091953795003)
  ·
    refine ⟨6044961473565137930692505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4029974315710091953795003 6044961473565137930692505)
    ·
      refine ⟨4533721105173853448019379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6044961473565137930692505 4533721105173853448019379)
      ·
        refine ⟨6800581657760780172029069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4533721105173853448019379 6800581657760780172029069)
        ·
          refine ⟨2550218121660292564510901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6800581657760780172029069 2550218121660292564510901)
          ·
            refine ⟨239082948905652427922897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2550218121660292564510901 239082948905652427922897)
            ·
              refine ⟨179312211679239320942173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239082948905652427922897 179312211679239320942173)
              ·
                refine ⟨67242079379714745353315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179312211679239320942173 67242079379714745353315)
                ·
                  rfl

theorem cell19_220984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 3].length) (baseStart_220984 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220984 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220984 prefixEnd_220984 := by exact prefixLift 220984
  have htrace : WordTrace (prefixWord ++ tailWord_220984) baseStart_220984 baseEnd_220984 := by
    simpa [prefixWord, tailWord_220984, baseEnd_220984] using wordTrace_append hprefix tailTrace_220984
  have hstable : (prefixWord ++ tailWord_220984).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220984).length < 2 ^ (prefixWord ++ tailWord_220984).sum := by decide
  have hdescent : baseEnd_220984 < baseStart_220984 := by decide
  rcases family_descends (prefixWord ++ tailWord_220984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_220986 : List Nat := [3, 1, 1, 1, 5, 2, 1, 5]
def baseStart_220986 : Nat := 118140960795 + 220986 * 2 ^ 59
def prefixEnd_220986 : Nat := 4983230072969 + 3 ^ 40 * 220986 * 2
def baseEnd_220986 : Nat := 67242687949379333308865

theorem tailTrace_220986 : CollatzResearch.WordTrace tailWord_220986 prefixEnd_220986 67242687949379333308865 := by
  unfold tailWord_220986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2015005394353234562290703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 5373347718275292166108541 2015005394353234562290703)
  ·
    refine ⟨3022508091529851843436055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2015005394353234562290703 3022508091529851843436055)
    ·
      refine ⟨4533762137294777765154083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3022508091529851843436055 4533762137294777765154083)
      ·
        refine ⟨6800643205942166647731125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4533762137294777765154083 6800643205942166647731125)
        ·
          refine ⟨637560300557078123224793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6800643205942166647731125 637560300557078123224793)
          ·
            refine ⟨478170225417808592418595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 637560300557078123224793 478170225417808592418595)
            ·
              refine ⟨717255338126712888627893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 478170225417808592418595 717255338126712888627893)
              ·
                refine ⟨67242687949379333308865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 717255338126712888627893 67242687949379333308865)
                ·
                  rfl

theorem cell19_220986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_220986 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_220986 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_220986 prefixEnd_220986 := by exact prefixLift 220986
  have htrace : WordTrace (prefixWord ++ tailWord_220986) baseStart_220986 baseEnd_220986 := by
    simpa [prefixWord, tailWord_220986, baseEnd_220986] using wordTrace_append hprefix tailTrace_220986
  have hstable : (prefixWord ++ tailWord_220986).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_220986).length < 2 ^ (prefixWord ++ tailWord_220986).sum := by decide
  have hdescent : baseEnd_220986 < baseStart_220986 := by decide
  rcases family_descends (prefixWord ++ tailWord_220986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221024 : List Nat := [2, 1, 1, 3, 3, 3, 2, 4]
def baseStart_221024 : Nat := 118140960795 + 221024 * 2 ^ 59
def prefixEnd_221024 : Nat := 4983230072969 + 3 ^ 40 * 221024 * 2
def baseEnd_221024 : Nat := 67254250773006504464317

theorem tailTrace_221024 : CollatzResearch.WordTrace tailWord_221024 prefixEnd_221024 67254250773006504464317 := by
  unfold tailWord_221024
  simp only [CollatzResearch.WordTrace]
  refine ⟨4030703775637635369523063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5374271700850180492697417 4030703775637635369523063)
  ·
    refine ⟨6046055663456453054284595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4030703775637635369523063 6046055663456453054284595)
    ·
      refine ⟨9069083495184679581426893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6046055663456453054284595 9069083495184679581426893)
      ·
        refine ⟨3400906310694254843035085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9069083495184679581426893 3400906310694254843035085)
        ·
          refine ⟨1275339866510345566138157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3400906310694254843035085 1275339866510345566138157)
          ·
            refine ⟨478252449941379587301809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1275339866510345566138157 478252449941379587301809)
            ·
              refine ⟨358689337456034690476357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 478252449941379587301809 358689337456034690476357)
              ·
                refine ⟨67254250773006504464317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 358689337456034690476357 67254250773006504464317)
                ·
                  rfl

theorem cell19_221024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_221024 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221024 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221024 prefixEnd_221024 := by exact prefixLift 221024
  have htrace : WordTrace (prefixWord ++ tailWord_221024) baseStart_221024 baseEnd_221024 := by
    simpa [prefixWord, tailWord_221024, baseEnd_221024] using wordTrace_append hprefix tailTrace_221024
  have hstable : (prefixWord ++ tailWord_221024).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221024).length < 2 ^ (prefixWord ++ tailWord_221024).sum := by decide
  have hdescent : baseEnd_221024 < baseStart_221024 := by decide
  rcases family_descends (prefixWord ++ tailWord_221024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221064 : List Nat := [2, 1, 3, 3, 10]
def baseStart_221064 : Nat := 118140960795 + 221064 * 2 ^ 59
def prefixEnd_221064 : Nat := 4983230072969 + 3 ^ 40 * 221064 * 2
def baseEnd_221064 : Nat := 2491348969122157910197

theorem tailTrace_221064 : CollatzResearch.WordTrace tailWord_221064 prefixEnd_221064 2491348969122157910197 := by
  unfold tailWord_221064
  simp only [CollatzResearch.WordTrace]
  refine ⟨4031433235565178785251123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 5375244314086905047001497 4031433235565178785251123)
  ·
    refine ⟨6047149853347768177876685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4031433235565178785251123 6047149853347768177876685)
    ·
      refine ⟨2267681195005413066703757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6047149853347768177876685 2267681195005413066703757)
      ·
        refine ⟨850380448127029900013909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2267681195005413066703757 850380448127029900013909)
        ·
          refine ⟨2491348969122157910197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 850380448127029900013909 2491348969122157910197)
          ·
            rfl

theorem cell19_221064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 10].length) (baseStart_221064 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221064 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221064 prefixEnd_221064 := by exact prefixLift 221064
  have htrace : WordTrace (prefixWord ++ tailWord_221064) baseStart_221064 baseEnd_221064 := by
    simpa [prefixWord, tailWord_221064, baseEnd_221064] using wordTrace_append hprefix tailTrace_221064
  have hstable : (prefixWord ++ tailWord_221064).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221064).length < 2 ^ (prefixWord ++ tailWord_221064).sum := by decide
  have hdescent : baseEnd_221064 < baseStart_221064 := by decide
  rcases family_descends (prefixWord ++ tailWord_221064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_221155 : List Nat := [1, 1, 1, 6, 1, 4, 2, 3]
def baseStart_221155 : Nat := 118140960795 + 221155 * 2 ^ 59
def prefixEnd_221155 : Nat := 4983230072969 + 3 ^ 40 * 221155 * 2
def baseEnd_221155 : Nat := 67294112086037015552849

theorem tailTrace_221155 : CollatzResearch.WordTrace tailWord_221155 prefixEnd_221155 67294112086037015552849 := by
  unfold tailWord_221155
  simp only [CollatzResearch.WordTrace]
  refine ⟨8066185513800680112064919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 5377457009200453408043279 8066185513800680112064919)
  ·
    refine ⟨12099278270701020168097379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8066185513800680112064919 12099278270701020168097379)
    ·
      refine ⟨18148917406051530252146069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12099278270701020168097379 18148917406051530252146069)
      ·
        refine ⟨850730503408665480569347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 18148917406051530252146069 850730503408665480569347)
        ·
          refine ⟨1276095755112998220854021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 850730503408665480569347 1276095755112998220854021)
          ·
            refine ⟨239267954083687166410129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1276095755112998220854021 239267954083687166410129)
            ·
              refine ⟨179450965562765374807597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 239267954083687166410129 179450965562765374807597)
              ·
                refine ⟨67294112086037015552849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 179450965562765374807597 67294112086037015552849)
                ·
                  rfl

theorem cell19_221155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 3].length) (baseStart_221155 + u * 2 ^ 78) = endpoint ∧
      endpoint < baseStart_221155 + u * 2 ^ 78 := by
  have hprefix : WordTrace prefixWord baseStart_221155 prefixEnd_221155 := by exact prefixLift 221155
  have htrace : WordTrace (prefixWord ++ tailWord_221155) baseStart_221155 baseEnd_221155 := by
    simpa [prefixWord, tailWord_221155, baseEnd_221155] using wordTrace_append hprefix tailTrace_221155
  have hstable : (prefixWord ++ tailWord_221155).sum < 78 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_221155).length < 2 ^ (prefixWord ++ tailWord_221155).sum := by decide
  have hdescent : baseEnd_221155 < baseStart_221155 := by decide
  rcases family_descends (prefixWord ++ tailWord_221155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan19Incremental
