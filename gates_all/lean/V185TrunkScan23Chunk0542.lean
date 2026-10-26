import V185TrunkScan23Chunk0541

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3204807 : List Nat := [1, 1, 4, 1, 1, 1, 4, 4, 1, 3, 2]
def baseStart_3204807 : Nat := 118140960795 + 3204807 * 2 ^ 59
def prefixEnd_3204807 : Nat := 4983230072969 + 3 ^ 40 * 3204807 * 2
def baseEnd_3204807 : Nat := 1645606395893747911573867

theorem tailTrace_3204807 : CollatzResearch.WordTrace tailWord_3204807 prefixEnd_3204807 1645606395893747911573867 := by
  unfold tailWord_3204807
  simp only [CollatzResearch.WordTrace]
  refine ⟨116888914100539051304948675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77925942733692700869965783 116888914100539051304948675)
  ·
    refine ⟨175333371150808576957423013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116888914100539051304948675 175333371150808576957423013)
    ·
      refine ⟨32875007090776608179516815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175333371150808576957423013 32875007090776608179516815)
      ·
        refine ⟨49312510636164912269275223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32875007090776608179516815 49312510636164912269275223)
        ·
          refine ⟨73968765954247368403912835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49312510636164912269275223 73968765954247368403912835)
          ·
            refine ⟨110953148931371052605869253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73968765954247368403912835 110953148931371052605869253)
            ·
              refine ⟨20803715424632072363600485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 110953148931371052605869253 20803715424632072363600485)
              ·
                refine ⟨3900696642118513568175091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20803715424632072363600485 3900696642118513568175091)
                ·
                  refine ⟨5851044963177770352262637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900696642118513568175091 5851044963177770352262637)
                  ·
                    refine ⟨2194141861191663882098489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5851044963177770352262637 2194141861191663882098489)
                    ·
                      refine ⟨1645606395893747911573867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2194141861191663882098489 1645606395893747911573867)
                      ·
                        rfl

theorem cell23_3204807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_3204807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204807 prefixEnd_3204807 := by exact prefixLift 3204807
  have htrace : WordTrace (prefixWord ++ tailWord_3204807) baseStart_3204807 baseEnd_3204807 := by
    simpa [prefixWord, tailWord_3204807, baseEnd_3204807] using wordTrace_append hprefix tailTrace_3204807
  have hstable : (prefixWord ++ tailWord_3204807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204807).length < 2 ^ (prefixWord ++ tailWord_3204807).sum := by decide
  have hdescent : baseEnd_3204807 < baseStart_3204807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204823 : List Nat := [1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 5]
def baseStart_3204823 : Nat := 118140960795 + 3204823 * 2 ^ 59
def prefixEnd_3204823 : Nat := 4983230072969 + 3 ^ 40 * 3204823 * 2
def baseEnd_3204823 : Nat := 1645614611584219848973793

theorem tailTrace_3204823 : CollatzResearch.WordTrace tailWord_3204823 prefixEnd_3204823 1645614611584219848973793 := by
  unfold tailWord_3204823
  simp only [CollatzResearch.WordTrace]
  refine ⟨116889497668481086037531123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77926331778987390691687415 116889497668481086037531123)
  ·
    refine ⟨175334246502721629056296685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116889497668481086037531123 175334246502721629056296685)
    ·
      refine ⟨65750342438520610896111257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175334246502721629056296685 65750342438520610896111257)
      ·
        refine ⟨49312756828890458172083443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65750342438520610896111257 49312756828890458172083443)
        ·
          refine ⟨73969135243335687258125165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49312756828890458172083443 73969135243335687258125165)
          ·
            refine ⟨27738425716250882721796937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73969135243335687258125165 27738425716250882721796937)
            ·
              refine ⟨20803819287188162041347703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27738425716250882721796937 20803819287188162041347703)
              ·
                refine ⟨31205728930782243062021555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20803819287188162041347703 31205728930782243062021555)
                ·
                  refine ⟨46808593396173364593032333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31205728930782243062021555 46808593396173364593032333)
                  ·
                    refine ⟨17553222523565011722387125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46808593396173364593032333 17553222523565011722387125)
                    ·
                      refine ⟨1645614611584219848973793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17553222523565011722387125 1645614611584219848973793)
                      ·
                        rfl

theorem cell23_3204823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_3204823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204823 prefixEnd_3204823 := by exact prefixLift 3204823
  have htrace : WordTrace (prefixWord ++ tailWord_3204823) baseStart_3204823 baseEnd_3204823 := by
    simpa [prefixWord, tailWord_3204823, baseEnd_3204823] using wordTrace_append hprefix tailTrace_3204823
  have hstable : (prefixWord ++ tailWord_3204823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204823).length < 2 ^ (prefixWord ++ tailWord_3204823).sum := by decide
  have hdescent : baseEnd_3204823 < baseStart_3204823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204843 : List Nat := [1, 1, 1, 1, 2, 4, 3, 3, 7]
def baseStart_3204843 : Nat := 118140960795 + 3204843 * 2 ^ 59
def prefixEnd_3204843 : Nat := 4983230072969 + 3 ^ 40 * 3204843 * 2
def baseEnd_3204843 : Nat := 182847209021923307858189

theorem tailTrace_3204843 : CollatzResearch.WordTrace tailWord_3204843 prefixEnd_3204843 182847209021923307858189 := by
  unfold tailWord_3204843
  simp only [CollatzResearch.WordTrace]
  refine ⟨116890227128408629453259183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77926818085605752968839455 116890227128408629453259183)
  ·
    refine ⟨175335340692612944179888775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116890227128408629453259183 175335340692612944179888775)
    ·
      refine ⟨263003011038919416269833163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175335340692612944179888775 263003011038919416269833163)
      ·
        refine ⟨394504516558379124404749745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263003011038919416269833163 394504516558379124404749745)
        ·
          refine ⟨295878387418784343303562309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394504516558379124404749745 295878387418784343303562309)
          ·
            refine ⟨55477197641022064369417933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 295878387418784343303562309 55477197641022064369417933)
            ·
              refine ⟨20803949115383274138531725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55477197641022064369417933 20803949115383274138531725)
              ·
                refine ⟨7801480918268727801949397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20803949115383274138531725 7801480918268727801949397)
                ·
                  refine ⟨182847209021923307858189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7801480918268727801949397 182847209021923307858189)
                  ·
                    rfl

theorem cell23_3204843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 3, 7].length) (baseStart_3204843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204843 prefixEnd_3204843 := by exact prefixLift 3204843
  have htrace : WordTrace (prefixWord ++ tailWord_3204843) baseStart_3204843 baseEnd_3204843 := by
    simpa [prefixWord, tailWord_3204843, baseEnd_3204843] using wordTrace_append hprefix tailTrace_3204843
  have hstable : (prefixWord ++ tailWord_3204843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204843).length < 2 ^ (prefixWord ++ tailWord_3204843).sum := by decide
  have hdescent : baseEnd_3204843 < baseStart_3204843 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204850 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 2, 2, 4]
def baseStart_3204850 : Nat := 118140960795 + 3204850 * 2 ^ 59
def prefixEnd_3204850 : Nat := 4983230072969 + 3 ^ 40 * 3204850 * 2
def baseEnd_3204850 : Nat := 1645628475561891243336169

theorem tailTrace_3204850 : CollatzResearch.WordTrace tailWord_3204850 prefixEnd_3204850 1645628475561891243336169 := by
  unfold tailWord_3204850
  simp only [CollatzResearch.WordTrace]
  refine ⟨29222620609845817412191001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77926988292922179765842669 29222620609845817412191001)
  ·
    refine ⟨21916965457384363059143251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29222620609845817412191001 21916965457384363059143251)
    ·
      refine ⟨32875448186076544588714877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21916965457384363059143251 32875448186076544588714877)
      ·
        refine ⟨12328293069778704220768079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32875448186076544588714877 12328293069778704220768079)
        ·
          refine ⟨18492439604668056331152119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12328293069778704220768079 18492439604668056331152119)
          ·
            refine ⟨27738659407002084496728179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18492439604668056331152119 27738659407002084496728179)
            ·
              refine ⟨41607989110503126745092269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27738659407002084496728179 41607989110503126745092269)
              ·
                refine ⟨15602995916438672529409601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41607989110503126745092269 15602995916438672529409601)
                ·
                  refine ⟨11702246937329004397057201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15602995916438672529409601 11702246937329004397057201)
                  ·
                    refine ⟨8776685202996753297792901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11702246937329004397057201 8776685202996753297792901)
                    ·
                      refine ⟨1645628475561891243336169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8776685202996753297792901 1645628475561891243336169)
                      ·
                        rfl

theorem cell23_3204850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 2, 2, 4].length) (baseStart_3204850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204850 prefixEnd_3204850 := by exact prefixLift 3204850
  have htrace : WordTrace (prefixWord ++ tailWord_3204850) baseStart_3204850 baseEnd_3204850 := by
    simpa [prefixWord, tailWord_3204850, baseEnd_3204850] using wordTrace_append hprefix tailTrace_3204850
  have hstable : (prefixWord ++ tailWord_3204850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204850).length < 2 ^ (prefixWord ++ tailWord_3204850).sum := by decide
  have hdescent : baseEnd_3204850 < baseStart_3204850 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204854 : List Nat := [5, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_3204854 : Nat := 118140960795 + 3204854 * 2 ^ 59
def prefixEnd_3204854 : Nat := 4983230072969 + 3 ^ 40 * 3204854 * 2
def baseEnd_3204854 : Nat := 1645630529484509227686151

theorem tailTrace_3204854 : CollatzResearch.WordTrace tailWord_3204854 prefixEnd_3204854 1645630529484509227686151 := by
  unfold tailWord_3204854
  simp only [CollatzResearch.WordTrace]
  refine ⟨7305664270710548645744351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77927085554245852221273077 7305664270710548645744351)
  ·
    refine ⟨10958496406065822968616527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7305664270710548645744351 10958496406065822968616527)
    ·
      refine ⟨16437744609098734452924791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10958496406065822968616527 16437744609098734452924791)
      ·
        refine ⟨24656616913648101679387187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16437744609098734452924791 24656616913648101679387187)
        ·
          refine ⟨36984925370472152519080781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24656616913648101679387187 36984925370472152519080781)
          ·
            refine ⟨13869347013927057194655293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36984925370472152519080781 13869347013927057194655293)
            ·
              refine ⟨5201005130222646447995735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13869347013927057194655293 5201005130222646447995735)
              ·
                refine ⟨7801507695333969671993603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5201005130222646447995735 7801507695333969671993603)
                ·
                  refine ⟨11702261543000954507990405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7801507695333969671993603 11702261543000954507990405)
                  ·
                    refine ⟨2194174039312678970248201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11702261543000954507990405 2194174039312678970248201)
                    ·
                      refine ⟨1645630529484509227686151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2194174039312678970248201 1645630529484509227686151)
                      ·
                        rfl

theorem cell23_3204854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_3204854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204854 prefixEnd_3204854 := by exact prefixLift 3204854
  have htrace : WordTrace (prefixWord ++ tailWord_3204854) baseStart_3204854 baseEnd_3204854 := by
    simpa [prefixWord, tailWord_3204854, baseEnd_3204854] using wordTrace_append hprefix tailTrace_3204854
  have hstable : (prefixWord ++ tailWord_3204854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204854).length < 2 ^ (prefixWord ++ tailWord_3204854).sum := by decide
  have hdescent : baseEnd_3204854 < baseStart_3204854 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204890 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 4, 5]
def baseStart_3204890 : Nat := 118140960795 + 3204890 * 2 ^ 59
def prefixEnd_3204890 : Nat := 4983230072969 + 3 ^ 40 * 3204890 * 2
def baseEnd_3204890 : Nat := 548549671596023695611995

theorem tailTrace_3204890 : CollatzResearch.WordTrace tailWord_3204890 prefixEnd_3204890 548549671596023695611995 := by
  unfold tailWord_3204890
  simp only [CollatzResearch.WordTrace]
  refine ⟨29222985339809589120055031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77927960906158904320146749 29222985339809589120055031)
  ·
    refine ⟨43834478009714383680082547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29222985339809589120055031 43834478009714383680082547)
    ·
      refine ⟨65751717014571575520123821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43834478009714383680082547 65751717014571575520123821)
      ·
        refine ⟨24656893880464340820046433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65751717014571575520123821 24656893880464340820046433)
        ·
          refine ⟨18492670410348255615034825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24656893880464340820046433 18492670410348255615034825)
          ·
            refine ⟨13869502807761191711276119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18492670410348255615034825 13869502807761191711276119)
            ·
              refine ⟨20804254211641787566914179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13869502807761191711276119 20804254211641787566914179)
              ·
                refine ⟨31206381317462681350371269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20804254211641787566914179 31206381317462681350371269)
                ·
                  refine ⟨5851196497024252753194613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31206381317462681350371269 5851196497024252753194613)
                  ·
                    refine ⟨548549671596023695611995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5851196497024252753194613 548549671596023695611995)
                    ·
                      rfl

theorem cell23_3204890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_3204890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204890 prefixEnd_3204890 := by exact prefixLift 3204890
  have htrace : WordTrace (prefixWord ++ tailWord_3204890) baseStart_3204890 baseEnd_3204890 := by
    simpa [prefixWord, tailWord_3204890, baseEnd_3204890] using wordTrace_append hprefix tailTrace_3204890
  have hstable : (prefixWord ++ tailWord_3204890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204890).length < 2 ^ (prefixWord ++ tailWord_3204890).sum := by decide
  have hdescent : baseEnd_3204890 < baseStart_3204890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204900 : List Nat := [2, 3, 1, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_3204900 : Nat := 118140960795 + 3204900 * 2 ^ 59
def prefixEnd_3204900 : Nat := 4983230072969 + 3 ^ 40 * 3204900 * 2
def baseEnd_3204900 : Nat := 1645654149594616047710939

theorem tailTrace_3204900 : CollatzResearch.WordTrace tailWord_3204900 prefixEnd_3204900 1645654149594616047710939 := by
  unfold tailWord_3204900
  simp only [CollatzResearch.WordTrace]
  refine ⟨58446153044601064094042077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77928204059468085458722769 58446153044601064094042077)
  ·
    refine ⟨21917307391725399035265779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58446153044601064094042077 21917307391725399035265779)
    ·
      refine ⟨32875961087588098552898669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21917307391725399035265779 32875961087588098552898669)
      ·
        refine ⟨12328485407845536957337001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32875961087588098552898669 12328485407845536957337001)
        ·
          refine ⟨9246364055884152718002751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12328485407845536957337001 9246364055884152718002751)
          ·
            refine ⟨13869546083826229077004127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9246364055884152718002751 13869546083826229077004127)
            ·
              refine ⟨20804319125739343615506191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13869546083826229077004127 20804319125739343615506191)
              ·
                refine ⟨31206478688609015423259287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20804319125739343615506191 31206478688609015423259287)
                ·
                  refine ⟨46809718032913523134888931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31206478688609015423259287 46809718032913523134888931)
                  ·
                    refine ⟨70214577049370284702333397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46809718032913523134888931 70214577049370284702333397)
                    ·
                      refine ⟨1645654149594616047710939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70214577049370284702333397 1645654149594616047710939)
                      ·
                        rfl

theorem cell23_3204900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_3204900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204900 prefixEnd_3204900 := by exact prefixLift 3204900
  have htrace : WordTrace (prefixWord ++ tailWord_3204900) baseStart_3204900 baseEnd_3204900 := by
    simpa [prefixWord, tailWord_3204900, baseEnd_3204900] using wordTrace_append hprefix tailTrace_3204900
  have hstable : (prefixWord ++ tailWord_3204900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204900).length < 2 ^ (prefixWord ++ tailWord_3204900).sum := by decide
  have hdescent : baseEnd_3204900 < baseStart_3204900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204934 : List Nat := [6, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3204934 : Nat := 118140960795 + 3204934 * 2 ^ 59
def prefixEnd_3204934 : Nat := 4983230072969 + 3 ^ 40 * 3204934 * 2
def baseEnd_3204934 : Nat := 1645671607936868914685783

theorem tailTrace_3204934 : CollatzResearch.WordTrace tailWord_3204934 prefixEnd_3204934 1645671607936868914685783 := by
  unfold tailWord_3204934
  simp only [CollatzResearch.WordTrace]
  refine ⟨3652923317846217249838183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77929030780719301329881237 3652923317846217249838183)
  ·
    refine ⟨5479384976769325874757275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3652923317846217249838183 5479384976769325874757275)
    ·
      refine ⟨8219077465153988812135913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5479384976769325874757275 8219077465153988812135913)
      ·
        refine ⟨6164308098865491609101935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8219077465153988812135913 6164308098865491609101935)
        ·
          refine ⟨9246462148298237413652903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6164308098865491609101935 9246462148298237413652903)
          ·
            refine ⟨13869693222447356120479355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9246462148298237413652903 13869693222447356120479355)
            ·
              refine ⟨20804539833671034180719033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13869693222447356120479355 20804539833671034180719033)
              ·
                refine ⟨15603404875253275635539275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20804539833671034180719033 15603404875253275635539275)
                ·
                  refine ⟨23405107312879913453308913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15603404875253275635539275 23405107312879913453308913)
                  ·
                    refine ⟨17553830484659935089981685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23405107312879913453308913 17553830484659935089981685)
                    ·
                      refine ⟨1645671607936868914685783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17553830484659935089981685 1645671607936868914685783)
                      ·
                        rfl

theorem cell23_3204934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3204934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204934 prefixEnd_3204934 := by exact prefixLift 3204934
  have htrace : WordTrace (prefixWord ++ tailWord_3204934) baseStart_3204934 baseEnd_3204934 := by
    simpa [prefixWord, tailWord_3204934, baseEnd_3204934] using wordTrace_append hprefix tailTrace_3204934
  have hstable : (prefixWord ++ tailWord_3204934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204934).length < 2 ^ (prefixWord ++ tailWord_3204934).sum := by decide
  have hdescent : baseEnd_3204934 < baseStart_3204934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204954 : List Nat := [3, 1, 1, 2, 1, 3, 3, 4, 1, 4]
def baseStart_3204954 : Nat := 118140960795 + 3204954 * 2 ^ 59
def prefixEnd_3204954 : Nat := 4983230072969 + 3 ^ 40 * 3204954 * 2
def baseEnd_3204954 : Nat := 548560625849986278811897

theorem tailTrace_3204954 : CollatzResearch.WordTrace tailWord_3204954 prefixEnd_3204954 548560625849986278811897 := by
  unfold tailWord_3204954
  simp only [CollatzResearch.WordTrace]
  refine ⟨29223568907751623852637479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77929517087337663607033277 29223568907751623852637479)
  ·
    refine ⟨43835353361627435778956219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29223568907751623852637479 43835353361627435778956219)
    ·
      refine ⟨65753030042441153668434329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43835353361627435778956219 65753030042441153668434329)
      ·
        refine ⟨49314772531830865251325747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65753030042441153668434329 49314772531830865251325747)
        ·
          refine ⟨73972158797746297876988621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49314772531830865251325747 73972158797746297876988621)
          ·
            refine ⟨27739559549154861703870733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73972158797746297876988621 27739559549154861703870733)
            ·
              refine ⟨10402334830933073138951525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27739559549154861703870733 10402334830933073138951525)
              ·
                refine ⟨1950437780799951213553411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10402334830933073138951525 1950437780799951213553411)
                ·
                  refine ⟨2925656671199926820330117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950437780799951213553411 2925656671199926820330117)
                  ·
                    refine ⟨548560625849986278811897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2925656671199926820330117 548560625849986278811897)
                    ·
                      rfl

theorem cell23_3204954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 3, 4, 1, 4].length) (baseStart_3204954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204954 prefixEnd_3204954 := by exact prefixLift 3204954
  have htrace : WordTrace (prefixWord ++ tailWord_3204954) baseStart_3204954 baseEnd_3204954 := by
    simpa [prefixWord, tailWord_3204954, baseEnd_3204954] using wordTrace_append hprefix tailTrace_3204954
  have hstable : (prefixWord ++ tailWord_3204954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204954).length < 2 ^ (prefixWord ++ tailWord_3204954).sum := by decide
  have hdescent : baseEnd_3204954 < baseStart_3204954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3204997 : List Nat := [1, 3, 1, 1, 3, 2, 3, 3, 1, 5]
def baseStart_3204997 : Nat := 118140960795 + 3204997 * 2 ^ 59
def prefixEnd_3204997 : Nat := 4983230072969 + 3 ^ 40 * 3204997 * 2
def baseEnd_3204997 : Nat := 548567985739367389399331

theorem tailTrace_3204997 : CollatzResearch.WordTrace tailWord_3204997 prefixEnd_3204997 548567985739367389399331 := by
  unfold tailWord_3204997
  simp only [CollatzResearch.WordTrace]
  refine ⟨116895843969850713754365245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77930562646567142502910163 116895843969850713754365245)
  ·
    refine ⟨43835941488694017657886967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116895843969850713754365245 43835941488694017657886967)
    ·
      refine ⟨65753912233041026486830451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43835941488694017657886967 65753912233041026486830451)
      ·
        refine ⟨98630868349561539730245677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65753912233041026486830451 98630868349561539730245677)
        ·
          refine ⟨36986575631085577398842129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98630868349561539730245677 36986575631085577398842129)
          ·
            refine ⟨27739931723314183049131597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36986575631085577398842129 27739931723314183049131597)
            ·
              refine ⟨10402474396242818643424349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27739931723314183049131597 10402474396242818643424349)
              ·
                refine ⟨3900927898591056991284131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10402474396242818643424349 3900927898591056991284131)
                ·
                  refine ⟨5851391847886585486926197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3900927898591056991284131 5851391847886585486926197)
                  ·
                    refine ⟨548567985739367389399331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5851391847886585486926197 548567985739367389399331)
                    ·
                      rfl

theorem cell23_3204997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 3, 1, 5].length) (baseStart_3204997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3204997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3204997 prefixEnd_3204997 := by exact prefixLift 3204997
  have htrace : WordTrace (prefixWord ++ tailWord_3204997) baseStart_3204997 baseEnd_3204997 := by
    simpa [prefixWord, tailWord_3204997, baseEnd_3204997] using wordTrace_append hprefix tailTrace_3204997
  have hstable : (prefixWord ++ tailWord_3204997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3204997).length < 2 ^ (prefixWord ++ tailWord_3204997).sum := by decide
  have hdescent : baseEnd_3204997 < baseStart_3204997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3204997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205054 : List Nat := [4, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_3205054 : Nat := 118140960795 + 3205054 * 2 ^ 59
def prefixEnd_3205054 : Nat := 4983230072969 + 3 ^ 40 * 3205054 * 2
def baseEnd_3205054 : Nat := 1645733225615408445185231

theorem tailTrace_3205054 : CollatzResearch.WordTrace tailWord_3205054 prefixEnd_3205054 1645733225615408445185231 := by
  unfold tailWord_3205054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14612240366330526561148777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77931948620429474992793477 14612240366330526561148777)
  ·
    refine ⟨10959180274747894920861583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14612240366330526561148777 10959180274747894920861583)
    ·
      refine ⟨16438770412121842381292375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10959180274747894920861583 16438770412121842381292375)
      ·
        refine ⟨24658155618182763571938563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16438770412121842381292375 24658155618182763571938563)
        ·
          refine ⟨36987233427274145357907845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24658155618182763571938563 36987233427274145357907845)
          ·
            refine ⟨6935106267613902254607721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36987233427274145357907845 6935106267613902254607721)
            ·
              refine ⟨5201329700710426690955791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6935106267613902254607721 5201329700710426690955791)
              ·
                refine ⟨7801994551065640036433687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5201329700710426690955791 7801994551065640036433687)
                ·
                  refine ⟨11702991826598460054650531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7801994551065640036433687 11702991826598460054650531)
                  ·
                    refine ⟨17554487739897690081975797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11702991826598460054650531 17554487739897690081975797)
                    ·
                      refine ⟨1645733225615408445185231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17554487739897690081975797 1645733225615408445185231)
                      ·
                        rfl

theorem cell23_3205054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_3205054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205054 prefixEnd_3205054 := by exact prefixLift 3205054
  have htrace : WordTrace (prefixWord ++ tailWord_3205054) baseStart_3205054 baseEnd_3205054 := by
    simpa [prefixWord, tailWord_3205054, baseEnd_3205054] using wordTrace_append hprefix tailTrace_3205054
  have hstable : (prefixWord ++ tailWord_3205054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205054).length < 2 ^ (prefixWord ++ tailWord_3205054).sum := by decide
  have hdescent : baseEnd_3205054 < baseStart_3205054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205068 : List Nat := [2, 2, 1, 4, 1, 4, 1, 1, 3, 2, 2]
def baseStart_3205068 : Nat := 118140960795 + 3205068 * 2 ^ 59
def prefixEnd_3205068 : Nat := 4983230072969 + 3 ^ 40 * 3205068 * 2
def baseEnd_3205068 : Nat := 1645740414344571390410167

theorem tailTrace_3205068 : CollatzResearch.WordTrace tailWord_3205068 prefixEnd_3205068 1645740414344571390410167 := by
  unfold tailWord_3205068
  simp only [CollatzResearch.WordTrace]
  refine ⟨58449216776296746440099929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77932289035062328586799905 58449216776296746440099929)
  ·
    refine ⟨43836912582222559830074947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58449216776296746440099929 43836912582222559830074947)
    ·
      refine ⟨65755368873333839745112421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43836912582222559830074947 65755368873333839745112421)
      ·
        refine ⟨12329131663750094952208579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65755368873333839745112421 12329131663750094952208579)
        ·
          refine ⟨18493697495625142428312869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12329131663750094952208579 18493697495625142428312869)
          ·
            refine ⟨3467568280429714205308663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18493697495625142428312869 3467568280429714205308663)
            ·
              refine ⟨5201352420644571307962995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3467568280429714205308663 5201352420644571307962995)
              ·
                refine ⟨7802028630966856961944493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5201352420644571307962995 7802028630966856961944493)
                ·
                  refine ⟨2925760736612571360729185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7802028630966856961944493 2925760736612571360729185)
                  ·
                    refine ⟨2194320552459428520546889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2925760736612571360729185 2194320552459428520546889)
                    ·
                      refine ⟨1645740414344571390410167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2194320552459428520546889 1645740414344571390410167)
                      ·
                        rfl

theorem cell23_3205068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_3205068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205068 prefixEnd_3205068 := by exact prefixLift 3205068
  have htrace : WordTrace (prefixWord ++ tailWord_3205068) baseStart_3205068 baseEnd_3205068 := by
    simpa [prefixWord, tailWord_3205068, baseEnd_3205068] using wordTrace_append hprefix tailTrace_3205068
  have hstable : (prefixWord ++ tailWord_3205068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205068).length < 2 ^ (prefixWord ++ tailWord_3205068).sum := by decide
  have hdescent : baseEnd_3205068 < baseStart_3205068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205074 : List Nat := [3, 2, 2, 3, 2, 1, 2, 8]
def baseStart_3205074 : Nat := 118140960795 + 3205074 * 2 ^ 59
def prefixEnd_3205074 : Nat := 4983230072969 + 3 ^ 40 * 3205074 * 2
def baseEnd_3205074 : Nat := 60953462786240680256857

theorem tailTrace_3205074 : CollatzResearch.WordTrace tailWord_3205074 prefixEnd_3205074 60953462786240680256857 := by
  unfold tailWord_3205074
  simp only [CollatzResearch.WordTrace]
  refine ⟨29224663097642938976229569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77932434927047837269945517 29224663097642938976229569)
  ·
    refine ⟨21918497323232204232172177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29224663097642938976229569 21918497323232204232172177)
    ·
      refine ⟨16438872992424153174129133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21918497323232204232172177 16438872992424153174129133)
      ·
        refine ⟨6164577372159057440298425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16438872992424153174129133 6164577372159057440298425)
        ·
          refine ⟨4623433029119293080223819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6164577372159057440298425 4623433029119293080223819)
          ·
            refine ⟨6935149543678939620335729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4623433029119293080223819 6935149543678939620335729)
            ·
              refine ⟨5201362157759204715251797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6935149543678939620335729 5201362157759204715251797)
              ·
                refine ⟨60953462786240680256857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5201362157759204715251797 60953462786240680256857)
                ·
                  rfl

theorem cell23_3205074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 2, 8].length) (baseStart_3205074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205074 prefixEnd_3205074 := by exact prefixLift 3205074
  have htrace : WordTrace (prefixWord ++ tailWord_3205074) baseStart_3205074 baseEnd_3205074 := by
    simpa [prefixWord, tailWord_3205074, baseEnd_3205074] using wordTrace_append hprefix tailTrace_3205074
  have hstable : (prefixWord ++ tailWord_3205074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205074).length < 2 ^ (prefixWord ++ tailWord_3205074).sum := by decide
  have hdescent : baseEnd_3205074 < baseStart_3205074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205078 : List Nat := [5, 2, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_3205078 : Nat := 118140960795 + 3205078 * 2 ^ 59
def prefixEnd_3205078 : Nat := 4983230072969 + 3 ^ 40 * 3205078 * 2
def baseEnd_3205078 : Nat := 548581849717038783761707

theorem tailTrace_3205078 : CollatzResearch.WordTrace tailWord_3205078 prefixEnd_3205078 548581849717038783761707 := by
  unfold tailWord_3205078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7306174892659829036753993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77932532188371509725375925 7306174892659829036753993)
  ·
    refine ⟨5479631169494871777565495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7306174892659829036753993 5479631169494871777565495)
    ·
      refine ⟨8219446754242307666348243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5479631169494871777565495 8219446754242307666348243)
      ·
        refine ⟨12329170131363461499522365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8219446754242307666348243 12329170131363461499522365)
        ·
          refine ⟨4623438799261298062320887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12329170131363461499522365 4623438799261298062320887)
          ·
            refine ⟨6935158198891947093481331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4623438799261298062320887 6935158198891947093481331)
            ·
              refine ⟨10402737298337920640221997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6935158198891947093481331 10402737298337920640221997)
              ·
                refine ⟨3901026486876720240083249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10402737298337920640221997 3901026486876720240083249)
                ·
                  refine ⟨2925769865157540180062437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3901026486876720240083249 2925769865157540180062437)
                  ·
                    refine ⟨548581849717038783761707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2925769865157540180062437 548581849717038783761707)
                    ·
                      rfl

theorem cell23_3205078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_3205078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205078 prefixEnd_3205078 := by exact prefixLift 3205078
  have htrace : WordTrace (prefixWord ++ tailWord_3205078) baseStart_3205078 baseEnd_3205078 := by
    simpa [prefixWord, tailWord_3205078, baseEnd_3205078] using wordTrace_append hprefix tailTrace_3205078
  have hstable : (prefixWord ++ tailWord_3205078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205078).length < 2 ^ (prefixWord ++ tailWord_3205078).sum := by decide
  have hdescent : baseEnd_3205078 < baseStart_3205078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205118 : List Nat := [4, 2, 2, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_3205118 : Nat := 118140960795 + 3205118 * 2 ^ 59
def prefixEnd_3205118 : Nat := 4983230072969 + 3 ^ 40 * 3205118 * 2
def baseEnd_3205118 : Nat := 1645766088377296194784937

theorem tailTrace_3205118 : CollatzResearch.WordTrace tailWord_3205118 prefixEnd_3205118 1645766088377296194784937 := by
  unfold tailWord_3205118
  simp only [CollatzResearch.WordTrace]
  refine ⟨14612532150301543927440001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77933504801608234279680005 14612532150301543927440001)
  ·
    refine ⟨10959399112726157945580001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14612532150301543927440001 10959399112726157945580001)
    ·
      refine ⟨8219549334544618459185001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10959399112726157945580001 8219549334544618459185001)
      ·
        refine ⟨6164662000908463844388751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8219549334544618459185001 6164662000908463844388751)
        ·
          refine ⟨9246993001362695766583127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6164662000908463844388751 9246993001362695766583127)
          ·
            refine ⟨13870489502044043649874691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9246993001362695766583127 13870489502044043649874691)
            ·
              refine ⟨20805734253066065474812037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13870489502044043649874691 20805734253066065474812037)
              ·
                refine ⟨3901075172449887276527257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20805734253066065474812037 3901075172449887276527257)
                ·
                  refine ⟨2925806379337415457395443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3901075172449887276527257 2925806379337415457395443)
                  ·
                    refine ⟨4388709569006123186093165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2925806379337415457395443 4388709569006123186093165)
                    ·
                      refine ⟨1645766088377296194784937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4388709569006123186093165 1645766088377296194784937)
                      ·
                        rfl

theorem cell23_3205118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_3205118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205118 prefixEnd_3205118 := by exact prefixLift 3205118
  have htrace : WordTrace (prefixWord ++ tailWord_3205118) baseStart_3205118 baseEnd_3205118 := by
    simpa [prefixWord, tailWord_3205118, baseEnd_3205118] using wordTrace_append hprefix tailTrace_3205118
  have hstable : (prefixWord ++ tailWord_3205118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205118).length < 2 ^ (prefixWord ++ tailWord_3205118).sum := by decide
  have hdescent : baseEnd_3205118 < baseStart_3205118 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205217 : List Nat := [1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 5]
def baseStart_3205217 : Nat := 118140960795 + 3205217 * 2 ^ 59
def prefixEnd_3205217 : Nat := 4983230072969 + 3 ^ 40 * 3205217 * 2
def baseEnd_3205217 : Nat := 1645816922962091307446981

theorem tailTrace_3205217 : CollatzResearch.WordTrace tailWord_3205217 prefixEnd_3205217 1645816922962091307446981 := by
  unfold tailWord_3205217
  simp only [CollatzResearch.WordTrace]
  refine ⟨116903868029053691327373905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77935912019369127551582603 116903868029053691327373905)
  ·
    refine ⟨87677901021790268495530429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116903868029053691327373905 87677901021790268495530429)
    ·
      refine ⟨32879212883171350685823911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87677901021790268495530429 32879212883171350685823911)
      ·
        refine ⟨49318819324757026028735867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32879212883171350685823911 49318819324757026028735867)
        ·
          refine ⟨73978228987135539043103801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49318819324757026028735867 73978228987135539043103801)
          ·
            refine ⟨55483671740351654282327851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73978228987135539043103801 55483671740351654282327851)
            ·
              refine ⟨83225507610527481423491777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55483671740351654282327851 83225507610527481423491777)
              ·
                refine ⟨62419130707895611067618833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83225507610527481423491777 62419130707895611067618833)
                ·
                  refine ⟨46814348030921708300714125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62419130707895611067618833 46814348030921708300714125)
                  ·
                    refine ⟨17555380511595640612767797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46814348030921708300714125 17555380511595640612767797)
                    ·
                      refine ⟨1645816922962091307446981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17555380511595640612767797 1645816922962091307446981)
                      ·
                        rfl

theorem cell23_3205217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 2, 2, 3, 5].length) (baseStart_3205217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205217 prefixEnd_3205217 := by exact prefixLift 3205217
  have htrace : WordTrace (prefixWord ++ tailWord_3205217) baseStart_3205217 baseEnd_3205217 := by
    simpa [prefixWord, tailWord_3205217, baseEnd_3205217] using wordTrace_append hprefix tailTrace_3205217
  have hstable : (prefixWord ++ tailWord_3205217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205217).length < 2 ^ (prefixWord ++ tailWord_3205217).sum := by decide
  have hdescent : baseEnd_3205217 < baseStart_3205217 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205241 : List Nat := [1, 2, 1, 3, 4, 1, 3, 1, 3, 4]
def baseStart_3205241 : Nat := 118140960795 + 3205241 * 2 ^ 59
def prefixEnd_3205241 : Nat := 4983230072969 + 3 ^ 40 * 3205241 * 2
def baseEnd_3205241 : Nat := 548609748832599737848957

theorem tailTrace_3205241 : CollatzResearch.WordTrace tailWord_3205241 prefixEnd_3205241 548609748832599737848957 := by
  unfold tailWord_3205241
  simp only [CollatzResearch.WordTrace]
  refine ⟨116904743380966743426247577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77936495587311162284165051 116904743380966743426247577)
  ·
    refine ⟨87678557535725057569685683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116904743380966743426247577 87678557535725057569685683)
    ·
      refine ⟨131517836303587586354528525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87678557535725057569685683 131517836303587586354528525)
      ·
        refine ⟨49319188613845344882948197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131517836303587586354528525 49319188613845344882948197)
        ·
          refine ⟨9247347865096002165552787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49319188613845344882948197 9247347865096002165552787)
          ·
            refine ⟨13871021797644003248329181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9247347865096002165552787 13871021797644003248329181)
            ·
              refine ⟨5201633174116501218123443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13871021797644003248329181 5201633174116501218123443)
              ·
                refine ⟨7802449761174751827185165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5201633174116501218123443 7802449761174751827185165)
                ·
                  refine ⟨2925918660440531935194437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7802449761174751827185165 2925918660440531935194437)
                  ·
                    refine ⟨548609748832599737848957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2925918660440531935194437 548609748832599737848957)
                    ·
                      rfl

theorem cell23_3205241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 1, 3, 4].length) (baseStart_3205241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205241 prefixEnd_3205241 := by exact prefixLift 3205241
  have htrace : WordTrace (prefixWord ++ tailWord_3205241) baseStart_3205241 baseEnd_3205241 := by
    simpa [prefixWord, tailWord_3205241, baseEnd_3205241] using wordTrace_append hprefix tailTrace_3205241
  have hstable : (prefixWord ++ tailWord_3205241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205241).length < 2 ^ (prefixWord ++ tailWord_3205241).sum := by decide
  have hdescent : baseEnd_3205241 < baseStart_3205241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205304 : List Nat := [2, 1, 2, 1, 2, 1, 3, 1, 5, 1, 4]
def baseStart_3205304 : Nat := 118140960795 + 3205304 * 2 ^ 59
def prefixEnd_3205304 : Nat := 4983230072969 + 3 ^ 40 * 3205304 * 2
def baseEnd_3205304 : Nat := 1645861595779032467059081

theorem tailTrace_3205304 : CollatzResearch.WordTrace tailWord_3205304 prefixEnd_3205304 1645861595779032467059081 := by
  unfold tailWord_3205304
  simp only [CollatzResearch.WordTrace]
  refine ⟨58453520589869252592895483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77938027453159003457193977 58453520589869252592895483)
  ·
    refine ⟨87680280884803878889343225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58453520589869252592895483 87680280884803878889343225)
    ·
      refine ⟨65760210663602909167007419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87680280884803878889343225 65760210663602909167007419)
      ·
        refine ⟨98640315995404363750511129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65760210663602909167007419 98640315995404363750511129)
        ·
          refine ⟨73980236996553272812883347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98640315995404363750511129 73980236996553272812883347)
          ·
            refine ⟨110970355494829909219325021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73980236996553272812883347 110970355494829909219325021)
            ·
              refine ⟨41613883310561215957246883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 110970355494829909219325021 41613883310561215957246883)
              ·
                refine ⟨62420824965841823935870325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41613883310561215957246883 62420824965841823935870325)
                ·
                  refine ⟨5851952340547670993987843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62420824965841823935870325 5851952340547670993987843)
                  ·
                    refine ⟨8777928510821506490981765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5851952340547670993987843 8777928510821506490981765)
                    ·
                      refine ⟨1645861595779032467059081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8777928510821506490981765 1645861595779032467059081)
                      ·
                        rfl

theorem cell23_3205304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 1, 5, 1, 4].length) (baseStart_3205304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205304 prefixEnd_3205304 := by exact prefixLift 3205304
  have htrace : WordTrace (prefixWord ++ tailWord_3205304) baseStart_3205304 baseEnd_3205304 := by
    simpa [prefixWord, tailWord_3205304, baseEnd_3205304] using wordTrace_append hprefix tailTrace_3205304
  have hstable : (prefixWord ++ tailWord_3205304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205304).length < 2 ^ (prefixWord ++ tailWord_3205304).sum := by decide
  have hdescent : baseEnd_3205304 < baseStart_3205304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205338 : List Nat := [3, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4]
def baseStart_3205338 : Nat := 118140960795 + 3205338 * 2 ^ 59
def prefixEnd_3205338 : Nat := 4983230072969 + 3 ^ 40 * 3205338 * 2
def baseEnd_3205338 : Nat := 1645879054121285334033925

theorem tailTrace_3205338 : CollatzResearch.WordTrace tailWord_3205338 prefixEnd_3205338 1645879054121285334033925 := by
  unfold tailWord_3205338
  simp only [CollatzResearch.WordTrace]
  refine ⟨29227070315403832248132167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77938854174410219328352445 29227070315403832248132167)
  ·
    refine ⟨43840605473105748372198251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29227070315403832248132167 43840605473105748372198251)
    ·
      refine ⟨65760908209658622558297377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43840605473105748372198251 65760908209658622558297377)
      ·
        refine ⟨49320681157243966918723033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65760908209658622558297377 49320681157243966918723033)
        ·
          refine ⟨36990510867932975189042275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49320681157243966918723033 36990510867932975189042275)
          ·
            refine ⟨55485766301899462783563413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36990510867932975189042275 55485766301899462783563413)
            ·
              refine ⟨2600895295401537317979535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55485766301899462783563413 2600895295401537317979535)
              ·
                refine ⟨3901342943102305976969303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2600895295401537317979535 3901342943102305976969303)
                ·
                  refine ⟨5852014414653458965453955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3901342943102305976969303 5852014414653458965453955)
                  ·
                    refine ⟨8778021621980188448180933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5852014414653458965453955 8778021621980188448180933)
                    ·
                      refine ⟨1645879054121285334033925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8778021621980188448180933 1645879054121285334033925)
                      ·
                        rfl

theorem cell23_3205338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 6, 1, 1, 1, 4].length) (baseStart_3205338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205338 prefixEnd_3205338 := by exact prefixLift 3205338
  have htrace : WordTrace (prefixWord ++ tailWord_3205338) baseStart_3205338 baseEnd_3205338 := by
    simpa [prefixWord, tailWord_3205338, baseEnd_3205338] using wordTrace_append hprefix tailTrace_3205338
  have hstable : (prefixWord ++ tailWord_3205338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205338).length < 2 ^ (prefixWord ++ tailWord_3205338).sum := by decide
  have hdescent : baseEnd_3205338 < baseStart_3205338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205355 : List Nat := [1, 1, 1, 1, 2, 5, 1, 6, 1, 2, 2]
def baseStart_3205355 : Nat := 118140960795 + 3205355 * 2 ^ 59
def prefixEnd_3205355 : Nat := 4983230072969 + 3 ^ 40 * 3205355 * 2
def baseEnd_3205355 : Nat := 1645887783292411767521347

theorem tailTrace_3205355 : CollatzResearch.WordTrace tailWord_3205355 prefixEnd_3205355 1645887783292411767521347 := by
  unfold tailWord_3205355
  simp only [CollatzResearch.WordTrace]
  refine ⟨116908901302553740895897519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77939267535035827263931679 116908901302553740895897519)
  ·
    refine ⟨175363351953830611343846279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116908901302553740895897519 175363351953830611343846279)
    ·
      refine ⟨263045027930745917015769419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175363351953830611343846279 263045027930745917015769419)
      ·
        refine ⟨394567541896118875523654129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263045027930745917015769419 394567541896118875523654129)
        ·
          refine ⟨295925656422089156642740597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394567541896118875523654129 295925656422089156642740597)
          ·
            refine ⟨27743030289570858435256931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 295925656422089156642740597 27743030289570858435256931)
            ·
              refine ⟨41614545434356287652885397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27743030289570858435256931 41614545434356287652885397)
              ·
                refine ⟨1950681817235450983729003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41614545434356287652885397 1950681817235450983729003)
                ·
                  refine ⟨2926022725853176475593505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950681817235450983729003 2926022725853176475593505)
                  ·
                    refine ⟨2194517044389882356695129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2926022725853176475593505 2194517044389882356695129)
                    ·
                      refine ⟨1645887783292411767521347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2194517044389882356695129 1645887783292411767521347)
                      ·
                        rfl

theorem cell23_3205355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 6, 1, 2, 2].length) (baseStart_3205355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205355 prefixEnd_3205355 := by exact prefixLift 3205355
  have htrace : WordTrace (prefixWord ++ tailWord_3205355) baseStart_3205355 baseEnd_3205355 := by
    simpa [prefixWord, tailWord_3205355, baseEnd_3205355] using wordTrace_append hprefix tailTrace_3205355
  have hstable : (prefixWord ++ tailWord_3205355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205355).length < 2 ^ (prefixWord ++ tailWord_3205355).sum := by decide
  have hdescent : baseEnd_3205355 < baseStart_3205355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205378 : List Nat := [3, 4, 1, 1, 2, 1, 4, 7]
def baseStart_3205378 : Nat := 118140960795 + 3205378 * 2 ^ 59
def prefixEnd_3205378 : Nat := 4983230072969 + 3 ^ 40 * 3205378 * 2
def baseEnd_3205378 : Nat := 60959244198054265834583

theorem tailTrace_3205378 : CollatzResearch.WordTrace tailWord_3205378 prefixEnd_3205378 60959244198054265834583 := by
  unfold tailWord_3205378
  simp only [CollatzResearch.WordTrace]
  refine ⟨29227435045367603955996197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77939826787646943882656525 29227435045367603955996197)
  ·
    refine ⟨5480144071006425741749287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29227435045367603955996197 5480144071006425741749287)
    ·
      refine ⟨8220216106509638612623931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5480144071006425741749287 8220216106509638612623931)
      ·
        refine ⟨12330324159764457918935897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8220216106509638612623931 12330324159764457918935897)
        ·
          refine ⟨9247743119823343439201923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12330324159764457918935897 9247743119823343439201923)
          ·
            refine ⟨13871614679735015158802885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9247743119823343439201923 13871614679735015158802885)
            ·
              refine ⟨2600927752450315342275541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13871614679735015158802885 2600927752450315342275541)
              ·
                refine ⟨60959244198054265834583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2600927752450315342275541 60959244198054265834583)
                ·
                  rfl

theorem cell23_3205378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 4, 7].length) (baseStart_3205378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205378 prefixEnd_3205378 := by exact prefixLift 3205378
  have htrace : WordTrace (prefixWord ++ tailWord_3205378) baseStart_3205378 baseEnd_3205378 := by
    simpa [prefixWord, tailWord_3205378, baseEnd_3205378] using wordTrace_append hprefix tailTrace_3205378
  have hstable : (prefixWord ++ tailWord_3205378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205378).length < 2 ^ (prefixWord ++ tailWord_3205378).sum := by decide
  have hdescent : baseEnd_3205378 < baseStart_3205378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205521 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 3]
def baseStart_3205521 : Nat := 118140960795 + 3205521 * 2 ^ 59
def prefixEnd_3205521 : Nat := 4983230072969 + 3 ^ 40 * 3205521 * 2
def baseEnd_3205521 : Nat := 1645973021081058118045583

theorem tailTrace_3205521 : CollatzResearch.WordTrace tailWord_3205521 prefixEnd_3205521 1645973021081058118045583 := by
  unfold tailWord_3205521
  simp only [CollatzResearch.WordTrace]
  refine ⟨116914955819952351246440417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77943303879968234164293611 116914955819952351246440417)
  ·
    refine ⟨87686216864964263434830313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116914955819952351246440417 87686216864964263434830313)
    ·
      refine ⟨65764662648723197576122735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87686216864964263434830313 65764662648723197576122735)
      ·
        refine ⟨98646993973084796364184103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65764662648723197576122735 98646993973084796364184103)
        ·
          refine ⟨147970490959627194546276155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98646993973084796364184103 147970490959627194546276155)
          ·
            refine ⟨221955736439440791819414233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147970490959627194546276155 221955736439440791819414233)
            ·
              refine ⟨166466802329580593864560675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 221955736439440791819414233 166466802329580593864560675)
              ·
                refine ⟨249700203494370890796841013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166466802329580593864560675 249700203494370890796841013)
                ·
                  refine ⟨23409394077597271012203845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 249700203494370890796841013 23409394077597271012203845)
                  ·
                    refine ⟨4389261389549488314788221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23409394077597271012203845 4389261389549488314788221)
                    ·
                      refine ⟨1645973021081058118045583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4389261389549488314788221 1645973021081058118045583)
                      ·
                        rfl

theorem cell23_3205521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 4, 3].length) (baseStart_3205521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205521 prefixEnd_3205521 := by exact prefixLift 3205521
  have htrace : WordTrace (prefixWord ++ tailWord_3205521) baseStart_3205521 baseEnd_3205521 := by
    simpa [prefixWord, tailWord_3205521, baseEnd_3205521] using wordTrace_append hprefix tailTrace_3205521
  have hstable : (prefixWord ++ tailWord_3205521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205521).length < 2 ^ (prefixWord ++ tailWord_3205521).sum := by decide
  have hdescent : baseEnd_3205521 < baseStart_3205521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205538 : List Nat := [3, 3, 1, 2, 1, 1, 1, 1, 3, 4, 3]
def baseStart_3205538 : Nat := 118140960795 + 3205538 * 2 ^ 59
def prefixEnd_3205538 : Nat := 4983230072969 + 3 ^ 40 * 3205538 * 2
def baseEnd_3205538 : Nat := 1645981750252184551533005

theorem tailTrace_3205538 : CollatzResearch.WordTrace tailWord_3205538 prefixEnd_3205538 1645981750252184551533005 := by
  unfold tailWord_3205538
  simp only [CollatzResearch.WordTrace]
  refine ⟨29228893965222690787452317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77943717240593842099872845 29228893965222690787452317)
  ·
    refine ⟨10960835236958509045294619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29228893965222690787452317 10960835236958509045294619)
    ·
      refine ⟨16441252855437763567941929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10960835236958509045294619 16441252855437763567941929)
      ·
        refine ⟨12330939641578322675956447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16441252855437763567941929 12330939641578322675956447)
        ·
          refine ⟨18496409462367484013934671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12330939641578322675956447 18496409462367484013934671)
          ·
            refine ⟨27744614193551226020902007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18496409462367484013934671 27744614193551226020902007)
            ·
              refine ⟨41616921290326839031353011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27744614193551226020902007 41616921290326839031353011)
              ·
                refine ⟨62425381935490258547029517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41616921290326839031353011 62425381935490258547029517)
                ·
                  refine ⟨23409518225808846955136069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62425381935490258547029517 23409518225808846955136069)
                  ·
                    refine ⟨4389284667339158804088013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23409518225808846955136069 4389284667339158804088013)
                    ·
                      refine ⟨1645981750252184551533005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4389284667339158804088013 1645981750252184551533005)
                      ·
                        rfl

theorem cell23_3205538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_3205538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205538 prefixEnd_3205538 := by exact prefixLift 3205538
  have htrace : WordTrace (prefixWord ++ tailWord_3205538) baseStart_3205538 baseEnd_3205538 := by
    simpa [prefixWord, tailWord_3205538, baseEnd_3205538] using wordTrace_append hprefix tailTrace_3205538
  have hstable : (prefixWord ++ tailWord_3205538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205538).length < 2 ^ (prefixWord ++ tailWord_3205538).sum := by decide
  have hdescent : baseEnd_3205538 < baseStart_3205538 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205569 : List Nat := [1, 2, 7, 1, 1, 1, 1, 2, 2, 1, 4]
def baseStart_3205569 : Nat := 118140960795 + 3205569 * 2 ^ 59
def prefixEnd_3205569 : Nat := 4983230072969 + 3 ^ 40 * 3205569 * 2
def baseEnd_3205569 : Nat := 1645997668152473930245363

theorem tailTrace_3205569 : CollatzResearch.WordTrace tailWord_3205569 prefixEnd_3205569 1645997668152473930245363 := by
  unfold tailWord_3205569
  simp only [CollatzResearch.WordTrace]
  refine ⟨116916706523778455444187761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77944471015852303629458507 116916706523778455444187761)
  ·
    refine ⟨87687529892833841583140821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116916706523778455444187761 87687529892833841583140821)
    ·
      refine ⟨2055176481863293162104863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 87687529892833841583140821 2055176481863293162104863)
      ·
        refine ⟨3082764722794939743157295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2055176481863293162104863 3082764722794939743157295)
        ·
          refine ⟨4624147084192409614735943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3082764722794939743157295 4624147084192409614735943)
          ·
            refine ⟨6936220626288614422103915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4624147084192409614735943 6936220626288614422103915)
            ·
              refine ⟨10404330939432921633155873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6936220626288614422103915 10404330939432921633155873)
              ·
                refine ⟨7803248204574691224866905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10404330939432921633155873 7803248204574691224866905)
                ·
                  refine ⟨5852436153431018418650179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7803248204574691224866905 5852436153431018418650179)
                  ·
                    refine ⟨8778654230146527627975269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5852436153431018418650179 8778654230146527627975269)
                    ·
                      refine ⟨1645997668152473930245363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8778654230146527627975269 1645997668152473930245363)
                      ·
                        rfl

theorem cell23_3205569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_3205569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205569 prefixEnd_3205569 := by exact prefixLift 3205569
  have htrace : WordTrace (prefixWord ++ tailWord_3205569) baseStart_3205569 baseEnd_3205569 := by
    simpa [prefixWord, tailWord_3205569, baseEnd_3205569] using wordTrace_append hprefix tailTrace_3205569
  have hstable : (prefixWord ++ tailWord_3205569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205569).length < 2 ^ (prefixWord ++ tailWord_3205569).sum := by decide
  have hdescent : baseEnd_3205569 < baseStart_3205569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205571 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 5, 5]
def baseStart_3205571 : Nat := 118140960795 + 3205571 * 2 ^ 59
def prefixEnd_3205571 : Nat := 4983230072969 + 3 ^ 40 * 3205571 * 2
def baseEnd_3205571 : Nat := 548666231704594307473451

theorem tailTrace_3205571 : CollatzResearch.WordTrace tailWord_3205571 prefixEnd_3205571 548666231704594307473451 := by
  unfold tailWord_3205571
  simp only [CollatzResearch.WordTrace]
  refine ⟨116916779469771209785760567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77944519646514139857173711 116916779469771209785760567)
  ·
    refine ⟨175375169204656814678640851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116916779469771209785760567 175375169204656814678640851)
    ·
      refine ⟨263062753806985222017961277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175375169204656814678640851 263062753806985222017961277)
      ·
        refine ⟨98648532677619458256735479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263062753806985222017961277 98648532677619458256735479)
        ·
          refine ⟨147972799016429187385103219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98648532677619458256735479 147972799016429187385103219)
          ·
            refine ⟨221959198524643781077654829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147972799016429187385103219 221959198524643781077654829)
            ·
              refine ⟨83234699446741417904120561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221959198524643781077654829 83234699446741417904120561)
              ·
                refine ⟨62426024585056063428090421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83234699446741417904120561 62426024585056063428090421)
                ·
                  refine ⟨5852439804849005946383477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62426024585056063428090421 5852439804849005946383477)
                  ·
                    refine ⟨548666231704594307473451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5852439804849005946383477 548666231704594307473451)
                    ·
                      rfl

theorem cell23_3205571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 5, 5].length) (baseStart_3205571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205571 prefixEnd_3205571 := by exact prefixLift 3205571
  have htrace : WordTrace (prefixWord ++ tailWord_3205571) baseStart_3205571 baseEnd_3205571 := by
    simpa [prefixWord, tailWord_3205571, baseEnd_3205571] using wordTrace_append hprefix tailTrace_3205571
  have hstable : (prefixWord ++ tailWord_3205571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205571).length < 2 ^ (prefixWord ++ tailWord_3205571).sum := by decide
  have hdescent : baseEnd_3205571 < baseStart_3205571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205572 : List Nat := [2, 3, 3, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_3205572 : Nat := 118140960795 + 3205572 * 2 ^ 59
def prefixEnd_3205572 : Nat := 4983230072969 + 3 ^ 40 * 3205572 * 2
def baseEnd_3205572 : Nat := 1645999208594437418507849

theorem tailTrace_3205572 : CollatzResearch.WordTrace tailWord_3205572 prefixEnd_3205572 1645999208594437418507849 := by
  unfold tailWord_3205572
  simp only [CollatzResearch.WordTrace]
  refine ⟨58458407971383793478273485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77944543961845057971031313 58458407971383793478273485)
  ·
    refine ⟨21921902989268922554352557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58458407971383793478273485 21921902989268922554352557)
    ·
      refine ⟨8220713620975845957882209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21921902989268922554352557 8220713620975845957882209)
      ·
        refine ⟨6165535215731884468411657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8220713620975845957882209 6165535215731884468411657)
        ·
          refine ⟨4624151411798913351308743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6165535215731884468411657 4624151411798913351308743)
          ·
            refine ⟨6936227117698370026963115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4624151411798913351308743 6936227117698370026963115)
            ·
              refine ⟨10404340676547555040444673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6936227117698370026963115 10404340676547555040444673)
              ·
                refine ⟨7803255507410666280333505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10404340676547555040444673 7803255507410666280333505)
                ·
                  refine ⟨5852441630557999710250129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7803255507410666280333505 5852441630557999710250129)
                  ·
                    refine ⟨4389331222918499782687597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5852441630557999710250129 4389331222918499782687597)
                    ·
                      refine ⟨1645999208594437418507849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4389331222918499782687597 1645999208594437418507849)
                      ·
                        rfl

theorem cell23_3205572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_3205572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205572 prefixEnd_3205572 := by exact prefixLift 3205572
  have htrace : WordTrace (prefixWord ++ tailWord_3205572) baseStart_3205572 baseEnd_3205572 := by
    simpa [prefixWord, tailWord_3205572, baseEnd_3205572] using wordTrace_append hprefix tailTrace_3205572
  have hstable : (prefixWord ++ tailWord_3205572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205572).length < 2 ^ (prefixWord ++ tailWord_3205572).sum := by decide
  have hdescent : baseEnd_3205572 < baseStart_3205572 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205591 : List Nat := [1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 4]
def baseStart_3205591 : Nat := 118140960795 + 3205591 * 2 ^ 59
def prefixEnd_3205591 : Nat := 4983230072969 + 3 ^ 40 * 3205591 * 2
def baseEnd_3205591 : Nat := 1646008964726872844170261

theorem tailTrace_3205591 : CollatzResearch.WordTrace tailWord_3205591 prefixEnd_3205591 1646008964726872844170261 := by
  unfold tailWord_3205591
  simp only [CollatzResearch.WordTrace]
  refine ⟨116917508929698753201488627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77945005953132502134325751 116917508929698753201488627)
  ·
    refine ⟨175376263394548129802232941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116917508929698753201488627 175376263394548129802232941)
    ·
      refine ⟨65766098772955548675837353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175376263394548129802232941 65766098772955548675837353)
      ·
        refine ⟨49324574079716661506878015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65766098772955548675837353 49324574079716661506878015)
        ·
          refine ⟨73986861119574992260317023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49324574079716661506878015 73986861119574992260317023)
          ·
            refine ⟨110980291679362488390475535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73986861119574992260317023 110980291679362488390475535)
            ·
              refine ⟨166470437519043732585713303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 110980291679362488390475535 166470437519043732585713303)
              ·
                refine ⟨249705656278565598878569955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166470437519043732585713303 249705656278565598878569955)
                ·
                  refine ⟨374558484417848398317854933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249705656278565598878569955 374558484417848398317854933)
                  ·
                    refine ⟨8778714478543321835574725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 374558484417848398317854933 8778714478543321835574725)
                    ·
                      refine ⟨1646008964726872844170261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8778714478543321835574725 1646008964726872844170261)
                      ·
                        rfl

theorem cell23_3205591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_3205591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205591 prefixEnd_3205591 := by exact prefixLift 3205591
  have htrace : WordTrace (prefixWord ++ tailWord_3205591) baseStart_3205591 baseEnd_3205591 := by
    simpa [prefixWord, tailWord_3205591, baseEnd_3205591] using wordTrace_append hprefix tailTrace_3205591
  have hstable : (prefixWord ++ tailWord_3205591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205591).length < 2 ^ (prefixWord ++ tailWord_3205591).sum := by decide
  have hdescent : baseEnd_3205591 < baseStart_3205591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205605 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 3, 5]
def baseStart_3205605 : Nat := 118140960795 + 3205605 * 2 ^ 59
def prefixEnd_3205605 : Nat := 4983230072969 + 3 ^ 40 * 3205605 * 2
def baseEnd_3205605 : Nat := 548672051152011929798399

theorem tailTrace_3205605 : CollatzResearch.WordTrace tailWord_3205605 prefixEnd_3205605 548672051152011929798399 := by
  unfold tailWord_3205605
  simp only [CollatzResearch.WordTrace]
  refine ⟨116918019551648033592498269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77945346367765355728332179 116918019551648033592498269)
  ·
    refine ⟨43844257331868012597186851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116918019551648033592498269 43844257331868012597186851)
    ·
      refine ⟨65766385997802018895780277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43844257331868012597186851 65766385997802018895780277)
      ·
        refine ⟨6165598687293939271479401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65766385997802018895780277 6165598687293939271479401)
        ·
          refine ⟨4624199015470454453609551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6165598687293939271479401 4624199015470454453609551)
          ·
            refine ⟨6936298523205681680414327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4624199015470454453609551 6936298523205681680414327)
            ·
              refine ⟨10404447784808522520621491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6936298523205681680414327 10404447784808522520621491)
              ·
                refine ⟨15606671677212783780932237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10404447784808522520621491 15606671677212783780932237)
                ·
                  refine ⟨5852501878954793917849589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15606671677212783780932237 5852501878954793917849589)
                  ·
                    refine ⟨548672051152011929798399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5852501878954793917849589 548672051152011929798399)
                    ·
                      rfl

theorem cell23_3205605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 3, 5].length) (baseStart_3205605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205605 prefixEnd_3205605 := by exact prefixLift 3205605
  have htrace : WordTrace (prefixWord ++ tailWord_3205605) baseStart_3205605 baseEnd_3205605 := by
    simpa [prefixWord, tailWord_3205605, baseEnd_3205605] using wordTrace_append hprefix tailTrace_3205605
  have hstable : (prefixWord ++ tailWord_3205605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205605).length < 2 ^ (prefixWord ++ tailWord_3205605).sum := by decide
  have hdescent : baseEnd_3205605 < baseStart_3205605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205622 : List Nat := [5, 1, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_3205622 : Nat := 118140960795 + 3205622 * 2 ^ 59
def prefixEnd_3205622 : Nat := 4983230072969 + 3 ^ 40 * 3205622 * 2
def baseEnd_3205622 : Nat := 548674960875720740960873

theorem tailTrace_3205622 : CollatzResearch.WordTrace tailWord_3205622 prefixEnd_3205622 548674960875720740960873 := by
  unfold tailWord_3205622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7307414974536652843491695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77945759728390963663911413 7307414974536652843491695)
  ·
    refine ⟨10961122461804979265237543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7307414974536652843491695 10961122461804979265237543)
    ·
      refine ⟨16441683692707468897856315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10961122461804979265237543 16441683692707468897856315)
      ·
        refine ⟨24662525539061203346784473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16441683692707468897856315 24662525539061203346784473)
        ·
          refine ⟨18496894154295902510088355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24662525539061203346784473 18496894154295902510088355)
          ·
            refine ⟨27745341231443853765132533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18496894154295902510088355 27745341231443853765132533)
            ·
              refine ⟨2601125740447861290481175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27745341231443853765132533 2601125740447861290481175)
              ·
                refine ⟨3901688610671791935721763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601125740447861290481175 3901688610671791935721763)
                ·
                  refine ⟨5852532916007687903582645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3901688610671791935721763 5852532916007687903582645)
                  ·
                    refine ⟨548674960875720740960873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5852532916007687903582645 548674960875720740960873)
                    ·
                      rfl

theorem cell23_3205622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_3205622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205622 prefixEnd_3205622 := by exact prefixLift 3205622
  have htrace : WordTrace (prefixWord ++ tailWord_3205622) baseStart_3205622 baseEnd_3205622 := by
    simpa [prefixWord, tailWord_3205622, baseEnd_3205622] using wordTrace_append hprefix tailTrace_3205622
  have hstable : (prefixWord ++ tailWord_3205622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205622).length < 2 ^ (prefixWord ++ tailWord_3205622).sum := by decide
  have hdescent : baseEnd_3205622 < baseStart_3205622 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205635 : List Nat := [1, 1, 1, 3, 2, 1, 6, 2, 2, 4]
def baseStart_3205635 : Nat := 118140960795 + 3205635 * 2 ^ 59
def prefixEnd_3205635 : Nat := 4983230072969 + 3 ^ 40 * 3205635 * 2
def baseEnd_3205635 : Nat := 548677185958556890673353

theorem tailTrace_3205635 : CollatzResearch.WordTrace tailWord_3205635 prefixEnd_3205635 548677185958556890673353 := by
  unfold tailWord_3205635
  simp only [CollatzResearch.WordTrace]
  refine ⟨116919113741539348716090359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77946075827692899144060239 116919113741539348716090359)
  ·
    refine ⟨175378670612309023074135539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116919113741539348716090359 175378670612309023074135539)
    ·
      refine ⟨263068005918463534611203309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175378670612309023074135539 263068005918463534611203309)
      ·
        refine ⟨98650502219423825479201241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263068005918463534611203309 98650502219423825479201241)
        ·
          refine ⟨73987876664567869109400931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98650502219423825479201241 73987876664567869109400931)
          ·
            refine ⟨110981814996851803664101397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73987876664567869109400931 110981814996851803664101397)
            ·
              refine ⟨5202272577977428296754753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110981814996851803664101397 5202272577977428296754753)
              ·
                refine ⟨3901704433483071222566065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5202272577977428296754753 3901704433483071222566065)
                ·
                  refine ⟨2926278325112303416924549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3901704433483071222566065 2926278325112303416924549)
                  ·
                    refine ⟨548677185958556890673353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2926278325112303416924549 548677185958556890673353)
                    ·
                      rfl

theorem cell23_3205635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 2, 2, 4].length) (baseStart_3205635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205635 prefixEnd_3205635 := by exact prefixLift 3205635
  have htrace : WordTrace (prefixWord ++ tailWord_3205635) baseStart_3205635 baseEnd_3205635 := by
    simpa [prefixWord, tailWord_3205635, baseEnd_3205635] using wordTrace_append hprefix tailTrace_3205635
  have hstable : (prefixWord ++ tailWord_3205635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205635).length < 2 ^ (prefixWord ++ tailWord_3205635).sum := by decide
  have hdescent : baseEnd_3205635 < baseStart_3205635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205636 : List Nat := [2, 3, 2, 3, 1, 1, 4, 2, 1, 1, 3]
def baseStart_3205636 : Nat := 118140960795 + 3205636 * 2 ^ 59
def prefixEnd_3205636 : Nat := 4983230072969 + 3 ^ 40 * 3205636 * 2
def baseEnd_3205636 : Nat := 1646032071356325168107555

theorem tailTrace_3205636 : CollatzResearch.WordTrace tailWord_3205636 prefixEnd_3205636 1646032071356325168107555 := by
  unfold tailWord_3205636
  simp only [CollatzResearch.WordTrace]
  refine ⟨58459575107267862943438381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77946100143023817257917841 58459575107267862943438381)
  ·
    refine ⟨21922340665225448603789393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58459575107267862943438381 21922340665225448603789393)
    ·
      refine ⟨16441755498919086452842045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21922340665225448603789393 16441755498919086452842045)
      ·
        refine ⟨6165658312094657419815767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16441755498919086452842045 6165658312094657419815767)
        ·
          refine ⟨9248487468141986129723651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6165658312094657419815767 9248487468141986129723651)
          ·
            refine ⟨13872731202212979194585477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9248487468141986129723651 13872731202212979194585477)
            ·
              refine ⟨2601137100414933598984777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13872731202212979194585477 2601137100414933598984777)
              ·
                refine ⟨1950852825311200199238583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601137100414933598984777 1950852825311200199238583)
                ·
                  refine ⟨2926279237966800298857875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950852825311200199238583 2926279237966800298857875)
                  ·
                    refine ⟨4389418856950200448286813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2926279237966800298857875 4389418856950200448286813)
                    ·
                      refine ⟨1646032071356325168107555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4389418856950200448286813 1646032071356325168107555)
                      ·
                        rfl

theorem cell23_3205636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_3205636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205636 prefixEnd_3205636 := by exact prefixLift 3205636
  have htrace : WordTrace (prefixWord ++ tailWord_3205636) baseStart_3205636 baseEnd_3205636 := by
    simpa [prefixWord, tailWord_3205636, baseEnd_3205636] using wordTrace_append hprefix tailTrace_3205636
  have hstable : (prefixWord ++ tailWord_3205636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205636).length < 2 ^ (prefixWord ++ tailWord_3205636).sum := by decide
  have hdescent : baseEnd_3205636 < baseStart_3205636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205641 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 7]
def baseStart_3205641 : Nat := 118140960795 + 3205641 * 2 ^ 59
def prefixEnd_3205641 : Nat := 4983230072969 + 3 ^ 40 * 3205641 * 2
def baseEnd_3205641 : Nat := 1646034638759597648545031

theorem tailTrace_3205641 : CollatzResearch.WordTrace tailWord_3205641 prefixEnd_3205641 1646034638759597648545031 := by
  unfold tailWord_3205641
  simp only [CollatzResearch.WordTrace]
  refine ⟨116919332579517611740808777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77946221719678407827205851 116919332579517611740808777)
  ·
    refine ⟨87689499434638208805606583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116919332579517611740808777 87689499434638208805606583)
    ·
      refine ⟨131534249151957313208409875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87689499434638208805606583 131534249151957313208409875)
      ·
        refine ⟨197301373727935969812614813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131534249151957313208409875 197301373727935969812614813)
        ·
          refine ⟨73988015147975988679730555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197301373727935969812614813 73988015147975988679730555)
          ·
            refine ⟨110982022721963983019595833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73988015147975988679730555 110982022721963983019595833)
            ·
              refine ⟨83236517041472987264696875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 110982022721963983019595833 83236517041472987264696875)
              ·
                refine ⟨124854775562209480897045313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83236517041472987264696875 124854775562209480897045313)
                ·
                  refine ⟨93641081671657110672783985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124854775562209480897045313 93641081671657110672783985)
                  ·
                    refine ⟨70230811253742833004587989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 93641081671657110672783985 70230811253742833004587989)
                    ·
                      refine ⟨1646034638759597648545031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70230811253742833004587989 1646034638759597648545031)
                      ·
                        rfl

theorem cell23_3205641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 2, 7].length) (baseStart_3205641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205641 prefixEnd_3205641 := by exact prefixLift 3205641
  have htrace : WordTrace (prefixWord ++ tailWord_3205641) baseStart_3205641 baseEnd_3205641 := by
    simpa [prefixWord, tailWord_3205641, baseEnd_3205641] using wordTrace_append hprefix tailTrace_3205641
  have hstable : (prefixWord ++ tailWord_3205641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205641).length < 2 ^ (prefixWord ++ tailWord_3205641).sum := by decide
  have hdescent : baseEnd_3205641 < baseStart_3205641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205642 : List Nat := [3, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2]
def baseStart_3205642 : Nat := 118140960795 + 3205642 * 2 ^ 59
def prefixEnd_3205642 : Nat := 4983230072969 + 3 ^ 40 * 3205642 * 2
def baseEnd_3205642 : Nat := 1646035152240252144632527

theorem tailTrace_3205642 : CollatzResearch.WordTrace tailWord_3205642 prefixEnd_3205642 1646035152240252144632527 := by
  unfold tailWord_3205642
  simp only [CollatzResearch.WordTrace]
  refine ⟨29229842263128497227898795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77946246035009325941063453 29229842263128497227898795)
  ·
    refine ⟨43844763394692745841848193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29229842263128497227898795 43844763394692745841848193)
    ·
      refine ⟨32883572546019559381386145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43844763394692745841848193 32883572546019559381386145)
      ·
        refine ⟨24662679409514669536039609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32883572546019559381386145 24662679409514669536039609)
        ·
          refine ⟨18497009557136002152029707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24662679409514669536039609 18497009557136002152029707)
          ·
            refine ⟨27745514335704003228044561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18497009557136002152029707 27745514335704003228044561)
            ·
              refine ⟨20809135751778002421033421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27745514335704003228044561 20809135751778002421033421)
              ·
                refine ⟨7803425906916750907887533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20809135751778002421033421 7803425906916750907887533)
                ·
                  refine ⟨2926284715093781590457825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7803425906916750907887533 2926284715093781590457825)
                  ·
                    refine ⟨2194713536320336192843369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2926284715093781590457825 2194713536320336192843369)
                    ·
                      refine ⟨1646035152240252144632527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2194713536320336192843369 1646035152240252144632527)
                      ·
                        rfl

theorem cell23_3205642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2].length) (baseStart_3205642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205642 prefixEnd_3205642 := by exact prefixLift 3205642
  have htrace : WordTrace (prefixWord ++ tailWord_3205642) baseStart_3205642 baseEnd_3205642 := by
    simpa [prefixWord, tailWord_3205642, baseEnd_3205642] using wordTrace_append hprefix tailTrace_3205642
  have hstable : (prefixWord ++ tailWord_3205642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205642).length < 2 ^ (prefixWord ++ tailWord_3205642).sum := by decide
  have hdescent : baseEnd_3205642 < baseStart_3205642 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205652 : List Nat := [2, 4, 3, 1, 1, 2, 2, 1, 1, 6]
def baseStart_3205652 : Nat := 118140960795 + 3205652 * 2 ^ 59
def prefixEnd_3205652 : Nat := 4983230072969 + 3 ^ 40 * 3205652 * 2
def baseEnd_3205652 : Nat := 548680095682265701835827

theorem tailTrace_3205652 : CollatzResearch.WordTrace tailWord_3205652 prefixEnd_3205652 548680095682265701835827 := by
  unfold tailWord_3205652
  simp only [CollatzResearch.WordTrace]
  refine ⟨58459866891238880309729605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77946489188318507079639473 58459866891238880309729605)
  ·
    refine ⟨10961225042107290058074301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58459866891238880309729605 10961225042107290058074301)
    ·
      refine ⟨4110459390790233771777863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10961225042107290058074301 4110459390790233771777863)
      ·
        refine ⟨6165689086185350657666795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4110459390790233771777863 6165689086185350657666795)
        ·
          refine ⟨9248533629278025986500193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6165689086185350657666795 9248533629278025986500193)
          ·
            refine ⟨6936400221958519489875145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9248533629278025986500193 6936400221958519489875145)
            ·
              refine ⟨5202300166468889617406359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6936400221958519489875145 5202300166468889617406359)
              ·
                refine ⟨7803450249703334426109539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202300166468889617406359 7803450249703334426109539)
                ·
                  refine ⟨11705175374555001639164309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7803450249703334426109539 11705175374555001639164309)
                  ·
                    refine ⟨548680095682265701835827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11705175374555001639164309 548680095682265701835827)
                    ·
                      rfl

theorem cell23_3205652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_3205652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205652 prefixEnd_3205652 := by exact prefixLift 3205652
  have htrace : WordTrace (prefixWord ++ tailWord_3205652) baseStart_3205652 baseEnd_3205652 := by
    simpa [prefixWord, tailWord_3205652, baseEnd_3205652] using wordTrace_append hprefix tailTrace_3205652
  have hstable : (prefixWord ++ tailWord_3205652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205652).length < 2 ^ (prefixWord ++ tailWord_3205652).sum := by decide
  have hdescent : baseEnd_3205652 < baseStart_3205652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205692 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_3205692 : Nat := 118140960795 + 3205692 * 2 ^ 59
def prefixEnd_3205692 : Nat := 4983230072969 + 3 ^ 40 * 3205692 * 2
def baseEnd_3205692 : Nat := 1646060826272976949007297

theorem tailTrace_3205692 : CollatzResearch.WordTrace tailWord_3205692 prefixEnd_3205692 1646060826272976949007297 := by
  unfold tailWord_3205692
  simp only [CollatzResearch.WordTrace]
  refine ⟨58460596351166423725457665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77947461801555231633943553 58460596351166423725457665)
  ·
    refine ⟨43845447263374817794093249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58460596351166423725457665 43845447263374817794093249)
    ·
      refine ⟨32884085447531113345569937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43845447263374817794093249 32884085447531113345569937)
      ·
        refine ⟨24663064085648335009177453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32884085447531113345569937 24663064085648335009177453)
        ·
          refine ⟨9248649032118125628441545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24663064085648335009177453 9248649032118125628441545)
          ·
            refine ⟨6936486774088594221331159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9248649032118125628441545 6936486774088594221331159)
            ·
              refine ⟨10404730161132891331996739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6936486774088594221331159 10404730161132891331996739)
              ·
                refine ⟨15607095241699336997995109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10404730161132891331996739 15607095241699336997995109)
                ·
                  refine ⟨2926330357818625687124083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15607095241699336997995109 2926330357818625687124083)
                  ·
                    refine ⟨4389495536727938530686125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2926330357818625687124083 4389495536727938530686125)
                    ·
                      refine ⟨1646060826272976949007297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4389495536727938530686125 1646060826272976949007297)
                      ·
                        rfl

theorem cell23_3205692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_3205692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205692 prefixEnd_3205692 := by exact prefixLift 3205692
  have htrace : WordTrace (prefixWord ++ tailWord_3205692) baseStart_3205692 baseEnd_3205692 := by
    simpa [prefixWord, tailWord_3205692, baseEnd_3205692] using wordTrace_append hprefix tailTrace_3205692
  have hstable : (prefixWord ++ tailWord_3205692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205692).length < 2 ^ (prefixWord ++ tailWord_3205692).sum := by decide
  have hdescent : baseEnd_3205692 < baseStart_3205692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205708 : List Nat := [2, 2, 1, 3, 1, 2, 1, 3, 2, 6]
def baseStart_3205708 : Nat := 118140960795 + 3205708 * 2 ^ 59
def prefixEnd_3205708 : Nat := 4983230072969 + 3 ^ 40 * 3205708 * 2
def baseEnd_3205708 : Nat := 548689680654482962135741

theorem tailTrace_3205708 : CollatzResearch.WordTrace tailWord_3205708 prefixEnd_3205708 548689680654482962135741 := by
  unfold tailWord_3205708
  simp only [CollatzResearch.WordTrace]
  refine ⟨58460888135137441091748889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77947850846849921455665185 58460888135137441091748889)
  ·
    refine ⟨43845666101353080818811667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58460888135137441091748889 43845666101353080818811667)
    ·
      refine ⟨65768499152029621228217501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43845666101353080818811667 65768499152029621228217501)
      ·
        refine ⟨24663187182011107960581563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65768499152029621228217501 24663187182011107960581563)
        ·
          refine ⟨36994780773016661940872345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24663187182011107960581563 36994780773016661940872345)
          ·
            refine ⟨27746085579762496455654259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36994780773016661940872345 27746085579762496455654259)
            ·
              refine ⟨41619128369643744683481389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27746085579762496455654259 41619128369643744683481389)
              ·
                refine ⟨15607173138616404256305521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41619128369643744683481389 15607173138616404256305521)
                ·
                  refine ⟨11705379853962303192229141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15607173138616404256305521 11705379853962303192229141)
                  ·
                    refine ⟨548689680654482962135741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11705379853962303192229141 548689680654482962135741)
                    ·
                      rfl

theorem cell23_3205708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_3205708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205708 prefixEnd_3205708 := by exact prefixLift 3205708
  have htrace : WordTrace (prefixWord ++ tailWord_3205708) baseStart_3205708 baseEnd_3205708 := by
    simpa [prefixWord, tailWord_3205708, baseEnd_3205708] using wordTrace_append hprefix tailTrace_3205708
  have hstable : (prefixWord ++ tailWord_3205708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205708).length < 2 ^ (prefixWord ++ tailWord_3205708).sum := by decide
  have hdescent : baseEnd_3205708 < baseStart_3205708 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205709 : List Nat := [1, 6, 1, 1, 2, 3, 1, 1, 1, 3, 3]
def baseStart_3205709 : Nat := 118140960795 + 3205709 * 2 ^ 59
def prefixEnd_3205709 : Nat := 4983230072969 + 3 ^ 40 * 3205709 * 2
def baseEnd_3205709 : Nat := 1646069555444103382494719

theorem tailTrace_3205709 : CollatzResearch.WordTrace tailWord_3205709 prefixEnd_3205709 1646069555444103382494719 := by
  unfold tailWord_3205709
  simp only [CollatzResearch.WordTrace]
  refine ⟨116921812743271259354284181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77947875162180839569522787 116921812743271259354284181)
  ·
    refine ⟨5480709972340840282232071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116921812743271259354284181 5480709972340840282232071)
    ·
      refine ⟨8221064958511260423348107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5480709972340840282232071 8221064958511260423348107)
      ·
        refine ⟨12331597437766890635022161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8221064958511260423348107 12331597437766890635022161)
        ·
          refine ⟨9248698078325167976266621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12331597437766890635022161 9248698078325167976266621)
          ·
            refine ⟨3468261779371937991099983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9248698078325167976266621 3468261779371937991099983)
            ·
              refine ⟨5202392669057906986649975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3468261779371937991099983 5202392669057906986649975)
              ·
                refine ⟨7803589003586860479974963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202392669057906986649975 7803589003586860479974963)
                ·
                  refine ⟨11705383505380290719962445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7803589003586860479974963 11705383505380290719962445)
                  ·
                    refine ⟨4389518814517609019985917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11705383505380290719962445 4389518814517609019985917)
                    ·
                      refine ⟨1646069555444103382494719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4389518814517609019985917 1646069555444103382494719)
                      ·
                        rfl

theorem cell23_3205709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 3, 1, 1, 1, 3, 3].length) (baseStart_3205709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205709 prefixEnd_3205709 := by exact prefixLift 3205709
  have htrace : WordTrace (prefixWord ++ tailWord_3205709) baseStart_3205709 baseEnd_3205709 := by
    simpa [prefixWord, tailWord_3205709, baseEnd_3205709] using wordTrace_append hprefix tailTrace_3205709
  have hstable : (prefixWord ++ tailWord_3205709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205709).length < 2 ^ (prefixWord ++ tailWord_3205709).sum := by decide
  have hdescent : baseEnd_3205709 < baseStart_3205709 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205728 : List Nat := [2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 4]
def baseStart_3205728 : Nat := 118140960795 + 3205728 * 2 ^ 59
def prefixEnd_3205728 : Nat := 4983230072969 + 3 ^ 40 * 3205728 * 2
def baseEnd_3205728 : Nat := 1646079311576538808157131

theorem tailTrace_3205728 : CollatzResearch.WordTrace tailWord_3205728 prefixEnd_3205728 1646079311576538808157131 := by
  unfold tailWord_3205728
  simp only [CollatzResearch.WordTrace]
  refine ⟨58461252865101212799612919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77948337153468283732817225 58461252865101212799612919)
  ·
    refine ⟨87691879297651819199419379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58461252865101212799612919 87691879297651819199419379)
    ·
      refine ⟨131537818946477728799129069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87691879297651819199419379 131537818946477728799129069)
      ·
        refine ⟨49326682104929148299673401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131537818946477728799129069 49326682104929148299673401)
        ·
          refine ⟨36995011578696861224755051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49326682104929148299673401 36995011578696861224755051)
          ·
            refine ⟨55492517368045291837132577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36995011578696861224755051 55492517368045291837132577)
            ·
              refine ⟨41619388026033968877849433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55492517368045291837132577 41619388026033968877849433)
              ·
                refine ⟨31214541019525476658387075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41619388026033968877849433 31214541019525476658387075)
                ·
                  refine ⟨46821811529288214987580613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31214541019525476658387075 46821811529288214987580613)
                  ·
                    refine ⟨8779089661741540310171365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46821811529288214987580613 8779089661741540310171365)
                    ·
                      refine ⟨1646079311576538808157131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8779089661741540310171365 1646079311576538808157131)
                      ·
                        rfl

theorem cell23_3205728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_3205728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205728 prefixEnd_3205728 := by exact prefixLift 3205728
  have htrace : WordTrace (prefixWord ++ tailWord_3205728) baseStart_3205728 baseEnd_3205728 := by
    simpa [prefixWord, tailWord_3205728, baseEnd_3205728] using wordTrace_append hprefix tailTrace_3205728
  have hstable : (prefixWord ++ tailWord_3205728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205728).length < 2 ^ (prefixWord ++ tailWord_3205728).sum := by decide
  have hdescent : baseEnd_3205728 < baseStart_3205728 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205732 : List Nat := [2, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2]
def baseStart_3205732 : Nat := 118140960795 + 3205732 * 2 ^ 59
def prefixEnd_3205732 : Nat := 4983230072969 + 3 ^ 40 * 3205732 * 2
def baseEnd_3205732 : Nat := 1646081365499156792507113

theorem tailTrace_3205732 : CollatzResearch.WordTrace tailWord_3205732 prefixEnd_3205732 1646081365499156792507113 := by
  unfold tailWord_3205732
  simp only [CollatzResearch.WordTrace]
  refine ⟨58461325811093967141185725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77948434414791956188247633 58461325811093967141185725)
  ·
    refine ⟨21922997179160237677944647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58461325811093967141185725 21922997179160237677944647)
    ·
      refine ⟨32884495768740356516916971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21922997179160237677944647 32884495768740356516916971)
      ·
        refine ⟨49326743653110534775375457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32884495768740356516916971 49326743653110534775375457)
        ·
          refine ⟨36995057739832901081531593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49326743653110534775375457 36995057739832901081531593)
          ·
            refine ⟨27746293304874675811148695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36995057739832901081531593 27746293304874675811148695)
            ·
              refine ⟨41619439957312013716723043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27746293304874675811148695 41619439957312013716723043)
              ·
                refine ⟨62429159935968020575084565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41619439957312013716723043 62429159935968020575084565)
                ·
                  refine ⟨2926366871998500964457089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62429159935968020575084565 2926366871998500964457089)
                  ·
                    refine ⟨2194775153998875723342817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2926366871998500964457089 2194775153998875723342817)
                    ·
                      refine ⟨1646081365499156792507113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2194775153998875723342817 1646081365499156792507113)
                      ·
                        rfl

theorem cell23_3205732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2].length) (baseStart_3205732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205732 prefixEnd_3205732 := by exact prefixLift 3205732
  have htrace : WordTrace (prefixWord ++ tailWord_3205732) baseStart_3205732 baseEnd_3205732 := by
    simpa [prefixWord, tailWord_3205732, baseEnd_3205732] using wordTrace_append hprefix tailTrace_3205732
  have hstable : (prefixWord ++ tailWord_3205732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205732).length < 2 ^ (prefixWord ++ tailWord_3205732).sum := by decide
  have hdescent : baseEnd_3205732 < baseStart_3205732 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205775 : List Nat := [1, 1, 2, 1, 1, 1, 1, 6, 2, 5, 2]
def baseStart_3205775 : Nat := 118140960795 + 3205775 * 2 ^ 59
def prefixEnd_3205775 : Nat := 4983230072969 + 3 ^ 40 * 3205775 * 2
def baseEnd_3205775 : Nat := 1646103445167300124269415

theorem tailTrace_3205775 : CollatzResearch.WordTrace tailWord_3205775 prefixEnd_3205775 1646103445167300124269415 := by
  unfold tailWord_3205775
  simp only [CollatzResearch.WordTrace]
  refine ⟨116924219961032152626186779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77949479974021435084124519 116924219961032152626186779)
  ·
    refine ⟨175386329941548228939280169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116924219961032152626186779 175386329941548228939280169)
    ·
      refine ⟨131539747456161171704460127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175386329941548228939280169 131539747456161171704460127)
      ·
        refine ⟨197309621184241757556690191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131539747456161171704460127 197309621184241757556690191)
        ·
          refine ⟨295964431776362636335035287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197309621184241757556690191 295964431776362636335035287)
          ·
            refine ⟨443946647664543954502552931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 295964431776362636335035287 443946647664543954502552931)
            ·
              refine ⟨665919971496815931753829397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 443946647664543954502552931 665919971496815931753829397)
              ·
                refine ⟨31214998663913246800960753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 665919971496815931753829397 31214998663913246800960753)
                ·
                  refine ⟨23411248997934935100720565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31214998663913246800960753 23411248997934935100720565)
                  ·
                    refine ⟨2194804593556400165692553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23411248997934935100720565 2194804593556400165692553)
                    ·
                      refine ⟨1646103445167300124269415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2194804593556400165692553 1646103445167300124269415)
                      ·
                        rfl

theorem cell23_3205775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 6, 2, 5, 2].length) (baseStart_3205775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205775 prefixEnd_3205775 := by exact prefixLift 3205775
  have htrace : WordTrace (prefixWord ++ tailWord_3205775) baseStart_3205775 baseEnd_3205775 := by
    simpa [prefixWord, tailWord_3205775, baseEnd_3205775] using wordTrace_append hprefix tailTrace_3205775
  have hstable : (prefixWord ++ tailWord_3205775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205775).length < 2 ^ (prefixWord ++ tailWord_3205775).sum := by decide
  have hdescent : baseEnd_3205775 < baseStart_3205775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205785 : List Nat := [1, 2, 1, 2, 1, 2, 6, 1, 2, 5]
def baseStart_3205785 : Nat := 118140960795 + 3205785 * 2 ^ 59
def prefixEnd_3205785 : Nat := 4983230072969 + 3 ^ 40 * 3205785 * 2
def baseEnd_3205785 : Nat := 548702859991281695048123

theorem tailTrace_3205785 : CollatzResearch.WordTrace tailWord_3205785 prefixEnd_3205785 548702859991281695048123 := by
  unfold tailWord_3205785
  simp only [CollatzResearch.WordTrace]
  refine ⟨116924584690995924334050809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77949723127330616222700539 116924584690995924334050809)
  ·
    refine ⟨87693438518246943250538107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116924584690995924334050809 87693438518246943250538107)
    ·
      refine ⟨131540157777370414875807161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87693438518246943250538107 131540157777370414875807161)
      ·
        refine ⟨98655118333027811156855371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131540157777370414875807161 98655118333027811156855371)
        ·
          refine ⟨147982677499541716735283057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98655118333027811156855371 147982677499541716735283057)
          ·
            refine ⟨110987008124656287551462293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 147982677499541716735283057 110987008124656287551462293)
            ·
              refine ⟨5202516005843263478974795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 110987008124656287551462293 5202516005843263478974795)
              ·
                refine ⟨7803774008764895218462193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5202516005843263478974795 7803774008764895218462193)
                ·
                  refine ⟨5852830506573671413846645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7803774008764895218462193 5852830506573671413846645)
                  ·
                    refine ⟨548702859991281695048123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5852830506573671413846645 548702859991281695048123)
                    ·
                      rfl

theorem cell23_3205785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 6, 1, 2, 5].length) (baseStart_3205785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205785 prefixEnd_3205785 := by exact prefixLift 3205785
  have htrace : WordTrace (prefixWord ++ tailWord_3205785) baseStart_3205785 baseEnd_3205785 := by
    simpa [prefixWord, tailWord_3205785, baseEnd_3205785] using wordTrace_append hprefix tailTrace_3205785
  have hstable : (prefixWord ++ tailWord_3205785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205785).length < 2 ^ (prefixWord ++ tailWord_3205785).sum := by decide
  have hdescent : baseEnd_3205785 < baseStart_3205785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205806 : List Nat := [4, 1, 4, 1, 1, 1, 4, 2, 5]
def baseStart_3205806 : Nat := 118140960795 + 3205806 * 2 ^ 59
def prefixEnd_3205806 : Nat := 4983230072969 + 3 ^ 40 * 3205806 * 2
def baseEnd_3205806 : Nat := 182902151451954389220197

theorem tailTrace_3205806 : CollatzResearch.WordTrace tailWord_3205806 prefixEnd_3205806 182902151451954389220197 := by
  unfold tailWord_3205806
  simp only [CollatzResearch.WordTrace]
  refine ⟨14615668827989980615070659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77950233749279896613710181 14615668827989980615070659)
  ·
    refine ⟨21923503241984970922605989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14615668827989980615070659 21923503241984970922605989)
    ·
      refine ⟨4110656857872182047988623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21923503241984970922605989 4110656857872182047988623)
      ·
        refine ⟨6165985286808273071982935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4110656857872182047988623 6165985286808273071982935)
        ·
          refine ⟨9248977930212409607974403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6165985286808273071982935 9248977930212409607974403)
          ·
            refine ⟨13873466895318614411961605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9248977930212409607974403 13873466895318614411961605)
            ·
              refine ⟨2601275042872240202242801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13873466895318614411961605 2601275042872240202242801)
              ·
                refine ⟨1950956282154180151682101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2601275042872240202242801 1950956282154180151682101)
                ·
                  refine ⟨182902151451954389220197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1950956282154180151682101 182902151451954389220197)
                  ·
                    rfl

theorem cell23_3205806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 4, 2, 5].length) (baseStart_3205806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205806 prefixEnd_3205806 := by exact prefixLift 3205806
  have htrace : WordTrace (prefixWord ++ tailWord_3205806) baseStart_3205806 baseEnd_3205806 := by
    simpa [prefixWord, tailWord_3205806, baseEnd_3205806] using wordTrace_append hprefix tailTrace_3205806
  have hstable : (prefixWord ++ tailWord_3205806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205806).length < 2 ^ (prefixWord ++ tailWord_3205806).sum := by decide
  have hdescent : baseEnd_3205806 < baseStart_3205806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205808 : List Nat := [2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 5]
def baseStart_3205808 : Nat := 118140960795 + 3205808 * 2 ^ 59
def prefixEnd_3205808 : Nat := 4983230072969 + 3 ^ 40 * 3205808 * 2
def baseEnd_3205808 : Nat := 1646120390028898495156763

theorem tailTrace_3205808 : CollatzResearch.WordTrace tailWord_3205808 prefixEnd_3205808 1646120390028898495156763 := by
  unfold tailWord_3205808
  simp only [CollatzResearch.WordTrace]
  refine ⟨58462711784956299631069039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77950282379941732841425385 58462711784956299631069039)
  ·
    refine ⟨87694067677434449446603559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58462711784956299631069039 87694067677434449446603559)
    ·
      refine ⟨131541101516151674169905339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87694067677434449446603559 131541101516151674169905339)
      ·
        refine ⟨197311652274227511254858009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131541101516151674169905339 197311652274227511254858009)
        ·
          refine ⟨147983739205670633441143507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197311652274227511254858009 147983739205670633441143507)
          ·
            refine ⟨221975608808505950161715261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 147983739205670633441143507 221975608808505950161715261)
            ·
              refine ⟨83240853303189731310643223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 221975608808505950161715261 83240853303189731310643223)
              ·
                refine ⟨124861279954784596965964835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83240853303189731310643223 124861279954784596965964835)
                ·
                  refine ⟨187291919932176895448947253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124861279954784596965964835 187291919932176895448947253)
                  ·
                    refine ⟨17558617493641583948338805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 187291919932176895448947253 17558617493641583948338805)
                    ·
                      refine ⟨1646120390028898495156763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17558617493641583948338805 1646120390028898495156763)
                      ·
                        rfl

theorem cell23_3205808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 5].length) (baseStart_3205808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205808 prefixEnd_3205808 := by exact prefixLift 3205808
  have htrace : WordTrace (prefixWord ++ tailWord_3205808) baseStart_3205808 baseEnd_3205808 := by
    simpa [prefixWord, tailWord_3205808, baseEnd_3205808] using wordTrace_append hprefix tailTrace_3205808
  have hstable : (prefixWord ++ tailWord_3205808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205808).length < 2 ^ (prefixWord ++ tailWord_3205808).sum := by decide
  have hdescent : baseEnd_3205808 < baseStart_3205808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205832 : List Nat := [2, 1, 3, 1, 2, 4, 1, 2, 3, 4]
def baseStart_3205832 : Nat := 118140960795 + 3205832 * 2 ^ 59
def prefixEnd_3205832 : Nat := 4983230072969 + 3 ^ 40 * 3205832 * 2
def baseEnd_3205832 : Nat := 548710904521535467085551

theorem tailTrace_3205832 : CollatzResearch.WordTrace tailWord_3205832 prefixEnd_3205832 548710904521535467085551 := by
  unfold tailWord_3205832
  simp only [CollatzResearch.WordTrace]
  refine ⟨58463149460912825680505875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77950865947883767574007833 58463149460912825680505875)
  ·
    refine ⟨87694724191369238520758813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58463149460912825680505875 87694724191369238520758813)
    ·
      refine ⟨32885521571763464445284555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87694724191369238520758813 32885521571763464445284555)
      ·
        refine ⟨49328282357645196667926833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32885521571763464445284555 49328282357645196667926833)
        ·
          refine ⟨36996211768233897500945125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49328282357645196667926833 36996211768233897500945125)
          ·
            refine ⟨6936789706543855781427211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36996211768233897500945125 6936789706543855781427211)
            ·
              refine ⟨10405184559815783672140817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6936789706543855781427211 10405184559815783672140817)
              ·
                refine ⟨7803888419861837754105613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10405184559815783672140817 7803888419861837754105613)
                ·
                  refine ⟨2926458157448189157789605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7803888419861837754105613 2926458157448189157789605)
                  ·
                    refine ⟨548710904521535467085551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2926458157448189157789605 548710904521535467085551)
                    ·
                      rfl

theorem cell23_3205832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 2, 3, 4].length) (baseStart_3205832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205832 prefixEnd_3205832 := by exact prefixLift 3205832
  have htrace : WordTrace (prefixWord ++ tailWord_3205832) baseStart_3205832 baseEnd_3205832 := by
    simpa [prefixWord, tailWord_3205832, baseEnd_3205832] using wordTrace_append hprefix tailTrace_3205832
  have hstable : (prefixWord ++ tailWord_3205832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205832).length < 2 ^ (prefixWord ++ tailWord_3205832).sum := by decide
  have hdescent : baseEnd_3205832 < baseStart_3205832 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205849 : List Nat := [1, 2, 1, 2, 3, 2, 4, 3, 1, 4]
def baseStart_3205849 : Nat := 118140960795 + 3205849 * 2 ^ 59
def prefixEnd_3205849 : Nat := 4983230072969 + 3 ^ 40 * 3205849 * 2
def baseEnd_3205849 : Nat := 548713814245244278248025

theorem tailTrace_3205849 : CollatzResearch.WordTrace tailWord_3205849 prefixEnd_3205849 548713814245244278248025 := by
  unfold tailWord_3205849
  simp only [CollatzResearch.WordTrace]
  refine ⟨116926918962764063264380601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77951279308509375509587067 116926918962764063264380601)
  ·
    refine ⟨87695189222073047448285451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116926918962764063264380601 87695189222073047448285451)
    ·
      refine ⟨131542783833109571172428177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87695189222073047448285451 131542783833109571172428177)
      ·
        refine ⟨98657087874832178379321133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131542783833109571172428177 98657087874832178379321133)
        ·
          refine ⟨36996407953062066892245425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98657087874832178379321133 36996407953062066892245425)
          ·
            refine ⟨27747305964796550169184069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36996407953062066892245425 27747305964796550169184069)
            ·
              refine ⟨5202619868399353156722013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27747305964796550169184069 5202619868399353156722013)
              ·
                refine ⟨1950982450649757433770755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5202619868399353156722013 1950982450649757433770755)
                ·
                  refine ⟨2926473675974636150656133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1950982450649757433770755 2926473675974636150656133)
                  ·
                    refine ⟨548713814245244278248025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2926473675974636150656133 548713814245244278248025)
                    ·
                      rfl

theorem cell23_3205849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 4, 3, 1, 4].length) (baseStart_3205849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205849 prefixEnd_3205849 := by exact prefixLift 3205849
  have htrace : WordTrace (prefixWord ++ tailWord_3205849) baseStart_3205849 baseEnd_3205849 := by
    simpa [prefixWord, tailWord_3205849, baseEnd_3205849] using wordTrace_append hprefix tailTrace_3205849
  have hstable : (prefixWord ++ tailWord_3205849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205849).length < 2 ^ (prefixWord ++ tailWord_3205849).sum := by decide
  have hdescent : baseEnd_3205849 < baseStart_3205849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205852 : List Nat := [2, 2, 5, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_3205852 : Nat := 118140960795 + 3205852 * 2 ^ 59
def prefixEnd_3205852 : Nat := 4983230072969 + 3 ^ 40 * 3205852 * 2
def baseEnd_3205852 : Nat := 1646142983177696323006561

theorem tailTrace_3205852 : CollatzResearch.WordTrace tailWord_3205852 prefixEnd_3205852 1646142983177696323006561 := by
  unfold tailWord_3205852
  simp only [CollatzResearch.WordTrace]
  refine ⟨58463514190876597388369905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77951352254502129851159873 58463514190876597388369905)
  ·
    refine ⟨43847635643157448041277429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58463514190876597388369905 43847635643157448041277429)
    ·
      refine ⟨4110715841546010753869759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43847635643157448041277429 4110715841546010753869759)
      ·
        refine ⟨6166073762319016130804639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4110715841546010753869759 6166073762319016130804639)
        ·
          refine ⟨9249110643478524196206959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6166073762319016130804639 9249110643478524196206959)
          ·
            refine ⟨13873665965217786294310439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9249110643478524196206959 13873665965217786294310439)
            ·
              refine ⟨20810498947826679441465659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13873665965217786294310439 20810498947826679441465659)
              ·
                refine ⟨31215748421740019162198489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20810498947826679441465659 31215748421740019162198489)
                ·
                  refine ⟨23411811316305014371648867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31215748421740019162198489 23411811316305014371648867)
                  ·
                    refine ⟨35117716974457521557473301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23411811316305014371648867 35117716974457521557473301)
                    ·
                      refine ⟨1646142983177696323006561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35117716974457521557473301 1646142983177696323006561)
                      ·
                        rfl

theorem cell23_3205852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_3205852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205852 prefixEnd_3205852 := by exact prefixLift 3205852
  have htrace : WordTrace (prefixWord ++ tailWord_3205852) baseStart_3205852 baseEnd_3205852 := by
    simpa [prefixWord, tailWord_3205852, baseEnd_3205852] using wordTrace_append hprefix tailTrace_3205852
  have hstable : (prefixWord ++ tailWord_3205852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205852).length < 2 ^ (prefixWord ++ tailWord_3205852).sum := by decide
  have hdescent : baseEnd_3205852 < baseStart_3205852 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205882 : List Nat := [3, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2]
def baseStart_3205882 : Nat := 118140960795 + 3205882 * 2 ^ 59
def prefixEnd_3205882 : Nat := 4983230072969 + 3 ^ 40 * 3205882 * 2
def baseEnd_3205882 : Nat := 1646158387597331205631423

theorem tailTrace_3205882 : CollatzResearch.WordTrace tailWord_3205882 prefixEnd_3205882 1646158387597331205631423 := by
  unfold tailWord_3205882
  simp only [CollatzResearch.WordTrace]
  refine ⟨29232030642911127475082975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77952081714429673266887933 29232030642911127475082975)
  ·
    refine ⟨43848045964366691212624463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29232030642911127475082975 43848045964366691212624463)
    ·
      refine ⟨65772068946550036818936695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43848045964366691212624463 65772068946550036818936695)
      ·
        refine ⟨98658103419825055228405043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65772068946550036818936695 98658103419825055228405043)
        ·
          refine ⟨147987155129737582842607565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98658103419825055228405043 147987155129737582842607565)
          ·
            refine ⟨55495183173651593565977837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147987155129737582842607565 55495183173651593565977837)
            ·
              refine ⟨20810693690119347587241689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55495183173651593565977837 20810693690119347587241689)
              ·
                refine ⟨15608020267589510690431267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20810693690119347587241689 15608020267589510690431267)
                ·
                  refine ⟨23412030401384266035646901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15608020267589510690431267 23412030401384266035646901)
                  ·
                    refine ⟨2194877850129774940841897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23412030401384266035646901 2194877850129774940841897)
                    ·
                      refine ⟨1646158387597331205631423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2194877850129774940841897 1646158387597331205631423)
                      ·
                        rfl

theorem cell23_3205882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2].length) (baseStart_3205882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205882 prefixEnd_3205882 := by exact prefixLift 3205882
  have htrace : WordTrace (prefixWord ++ tailWord_3205882) baseStart_3205882 baseEnd_3205882 := by
    simpa [prefixWord, tailWord_3205882, baseEnd_3205882] using wordTrace_append hprefix tailTrace_3205882
  have hstable : (prefixWord ++ tailWord_3205882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205882).length < 2 ^ (prefixWord ++ tailWord_3205882).sum := by decide
  have hdescent : baseEnd_3205882 < baseStart_3205882 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205905 : List Nat := [1, 2, 2, 1, 1, 3, 2, 4, 1, 6]
def baseStart_3205905 : Nat := 118140960795 + 3205905 * 2 ^ 59
def prefixEnd_3205905 : Nat := 4983230072969 + 3 ^ 40 * 3205905 * 2
def baseEnd_3205905 : Nat := 548723399217461538547939

theorem tailTrace_3205905 : CollatzResearch.WordTrace tailWord_3205905 prefixEnd_3205905 548723399217461538547939 := by
  unfold tailWord_3205905
  simp only [CollatzResearch.WordTrace]
  refine ⟨116928961450561184828419169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77952640967040789885612779 116928961450561184828419169)
  ·
    refine ⟨87696721087920888621314377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116928961450561184828419169 87696721087920888621314377)
    ·
      refine ⟨65772540815940666465985783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87696721087920888621314377 65772540815940666465985783)
      ·
        refine ⟨98658811223910999698978675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65772540815940666465985783 98658811223910999698978675)
        ·
          refine ⟨147988216835866499548468013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98658811223910999698978675 147988216835866499548468013)
          ·
            refine ⟨55495581313449937330675505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147988216835866499548468013 55495581313449937330675505)
            ·
              refine ⟨41621685985087452998006629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55495581313449937330675505 41621685985087452998006629)
              ·
                refine ⟨7804066122203897437126243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41621685985087452998006629 7804066122203897437126243)
                ·
                  refine ⟨11706099183305846155689365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7804066122203897437126243 11706099183305846155689365)
                  ·
                    refine ⟨548723399217461538547939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11706099183305846155689365 548723399217461538547939)
                    ·
                      rfl

theorem cell23_3205905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 6].length) (baseStart_3205905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205905 prefixEnd_3205905 := by exact prefixLift 3205905
  have htrace : WordTrace (prefixWord ++ tailWord_3205905) baseStart_3205905 baseEnd_3205905 := by
    simpa [prefixWord, tailWord_3205905, baseEnd_3205905] using wordTrace_append hprefix tailTrace_3205905
  have hstable : (prefixWord ++ tailWord_3205905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205905).length < 2 ^ (prefixWord ++ tailWord_3205905).sum := by decide
  have hdescent : baseEnd_3205905 < baseStart_3205905 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205925 : List Nat := [1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 6]
def baseStart_3205925 : Nat := 118140960795 + 3205925 * 2 ^ 59
def prefixEnd_3205925 : Nat := 4983230072969 + 3 ^ 40 * 3205925 * 2
def baseEnd_3205925 : Nat := 1646180467265474537393725

theorem tailTrace_3205925 : CollatzResearch.WordTrace tailWord_3205925 prefixEnd_3205925 1646180467265474537393725 := by
  unfold tailWord_3205925
  simp only [CollatzResearch.WordTrace]
  refine ⟨116929690910488728244147229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77953127273659152162764819 116929690910488728244147229)
  ·
    refine ⟨43848634091433273091555211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116929690910488728244147229 43848634091433273091555211)
    ·
      refine ⟨65772951137149909637332817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43848634091433273091555211 65772951137149909637332817)
      ·
        refine ⟨49329713352862432227999613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65772951137149909637332817 49329713352862432227999613)
        ·
          refine ⟨18498642507323412085499855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49329713352862432227999613 18498642507323412085499855)
          ·
            refine ⟨27747963760985118128249783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18498642507323412085499855 27747963760985118128249783)
            ·
              refine ⟨41621945641477677192374675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27747963760985118128249783 41621945641477677192374675)
              ·
                refine ⟨62432918462216515788562013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41621945641477677192374675 62432918462216515788562013)
                ·
                  refine ⟨23412344423331193420710755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62432918462216515788562013 23412344423331193420710755)
                  ·
                    refine ⟨35118516634996790131066133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23412344423331193420710755 35118516634996790131066133)
                    ·
                      refine ⟨1646180467265474537393725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35118516634996790131066133 1646180467265474537393725)
                      ·
                        rfl

theorem cell23_3205925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_3205925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205925 prefixEnd_3205925 := by exact prefixLift 3205925
  have htrace : WordTrace (prefixWord ++ tailWord_3205925) baseStart_3205925 baseEnd_3205925 := by
    simpa [prefixWord, tailWord_3205925, baseEnd_3205925] using wordTrace_append hprefix tailTrace_3205925
  have hstable : (prefixWord ++ tailWord_3205925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205925).length < 2 ^ (prefixWord ++ tailWord_3205925).sum := by decide
  have hdescent : baseEnd_3205925 < baseStart_3205925 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205932 : List Nat := [2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 3]
def baseStart_3205932 : Nat := 118140960795 + 3205932 * 2 ^ 59
def prefixEnd_3205932 : Nat := 4983230072969 + 3 ^ 40 * 3205932 * 2
def baseEnd_3205932 : Nat := 1646184061630056010006193

theorem tailTrace_3205932 : CollatzResearch.WordTrace tailWord_3205932 prefixEnd_3205932 1646184061630056010006193 := by
  unfold tailWord_3205932
  simp only [CollatzResearch.WordTrace]
  refine ⟨58464973110731684219826025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77953297480975578959768033 58464973110731684219826025)
  ·
    refine ⟨43848729833048763164869519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58464973110731684219826025 43848729833048763164869519)
    ·
      refine ⟨65773094749573144747304279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43848729833048763164869519 65773094749573144747304279)
      ·
        refine ⟨98659642124359717120956419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65773094749573144747304279 98659642124359717120956419)
        ·
          refine ⟨147989463186539575681434629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98659642124359717120956419 147989463186539575681434629)
          ·
            refine ⟨27748024347476170440268993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 147989463186539575681434629 27748024347476170440268993)
            ·
              refine ⟨20811018260607127830201745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27748024347476170440268993 20811018260607127830201745)
              ·
                refine ⟨15608263695455345872651309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20811018260607127830201745 15608263695455345872651309)
                ·
                  refine ⟨5853098885795754702244241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15608263695455345872651309 5853098885795754702244241)
                  ·
                    refine ⟨4389824164346816026683181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5853098885795754702244241 4389824164346816026683181)
                    ·
                      refine ⟨1646184061630056010006193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4389824164346816026683181 1646184061630056010006193)
                      ·
                        rfl

theorem cell23_3205932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_3205932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205932 prefixEnd_3205932 := by exact prefixLift 3205932
  have htrace : WordTrace (prefixWord ++ tailWord_3205932) baseStart_3205932 baseEnd_3205932 := by
    simpa [prefixWord, tailWord_3205932, baseEnd_3205932] using wordTrace_append hprefix tailTrace_3205932
  have hstable : (prefixWord ++ tailWord_3205932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205932).length < 2 ^ (prefixWord ++ tailWord_3205932).sum := by decide
  have hdescent : baseEnd_3205932 < baseStart_3205932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205939 : List Nat := [1, 1, 1, 2, 6, 2, 1, 3, 2, 4]
def baseStart_3205939 : Nat := 118140960795 + 3205939 * 2 ^ 59
def prefixEnd_3205939 : Nat := 4983230072969 + 3 ^ 40 * 3205939 * 2
def baseEnd_3205939 : Nat := 548729218664879160872887

theorem tailTrace_3205939 : CollatzResearch.WordTrace tailWord_3205939 prefixEnd_3205939 548729218664879160872887 := by
  unfold tailWord_3205939
  simp only [CollatzResearch.WordTrace]
  refine ⟨116930201532438008635156871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77953467688292005756771247 116930201532438008635156871)
  ·
    refine ⟨175395302298657012952735307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116930201532438008635156871 175395302298657012952735307)
    ·
      refine ⟨263092953447985519429102961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175395302298657012952735307 263092953447985519429102961)
      ·
        refine ⟨197319715085989139571827221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263092953447985519429102961 197319715085989139571827221)
        ·
          refine ⟨9249361644655740917429401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 197319715085989139571827221 9249361644655740917429401)
          ·
            refine ⟨6937021233491805688072051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9249361644655740917429401 6937021233491805688072051)
            ·
              refine ⟨10405531850237708532108077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6937021233491805688072051 10405531850237708532108077)
              ·
                refine ⟨3902074443839140699540529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10405531850237708532108077 3902074443839140699540529)
                ·
                  refine ⟨2926555832879355524655397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3902074443839140699540529 2926555832879355524655397)
                  ·
                    refine ⟨548729218664879160872887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2926555832879355524655397 548729218664879160872887)
                    ·
                      rfl

theorem cell23_3205939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 3, 2, 4].length) (baseStart_3205939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205939 prefixEnd_3205939 := by exact prefixLift 3205939
  have htrace : WordTrace (prefixWord ++ tailWord_3205939) baseStart_3205939 baseEnd_3205939 := by
    simpa [prefixWord, tailWord_3205939, baseEnd_3205939] using wordTrace_append hprefix tailTrace_3205939
  have hstable : (prefixWord ++ tailWord_3205939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205939).length < 2 ^ (prefixWord ++ tailWord_3205939).sum := by decide
  have hdescent : baseEnd_3205939 < baseStart_3205939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205946 : List Nat := [3, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4]
def baseStart_3205946 : Nat := 118140960795 + 3205946 * 2 ^ 59
def prefixEnd_3205946 : Nat := 4983230072969 + 3 ^ 40 * 3205946 * 2
def baseEnd_3205946 : Nat := 1646191250359218955231129

theorem tailTrace_3205946 : CollatzResearch.WordTrace tailWord_3205946 prefixEnd_3205946 1646191250359218955231129 := by
  unfold tailWord_3205946
  simp only [CollatzResearch.WordTrace]
  refine ⟨29232614210853162207665423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77953637895608432553774461 29232614210853162207665423)
  ·
    refine ⟨43848921316279743311498135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29232614210853162207665423 43848921316279743311498135)
    ·
      refine ⟨65773381974419614967247203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43848921316279743311498135 65773381974419614967247203)
      ·
        refine ⟨98660072961629422450870805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65773381974419614967247203 98660072961629422450870805)
        ·
          refine ⟨4624690920076379177384569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 98660072961629422450870805 4624690920076379177384569)
          ·
            refine ⟨3468518190057284383038427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4624690920076379177384569 3468518190057284383038427)
            ·
              refine ⟨5202777285085926574557641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3468518190057284383038427 5202777285085926574557641)
              ·
                refine ⟨3902082963814444930918231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5202777285085926574557641 3902082963814444930918231)
                ·
                  refine ⟨5853124445721667396377347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902082963814444930918231 5853124445721667396377347)
                  ·
                    refine ⟨8779686668582501094566021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5853124445721667396377347 8779686668582501094566021)
                    ·
                      refine ⟨1646191250359218955231129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8779686668582501094566021 1646191250359218955231129)
                      ·
                        rfl

theorem cell23_3205946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_3205946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205946 prefixEnd_3205946 := by exact prefixLift 3205946
  have htrace : WordTrace (prefixWord ++ tailWord_3205946) baseStart_3205946 baseEnd_3205946 := by
    simpa [prefixWord, tailWord_3205946, baseEnd_3205946] using wordTrace_append hprefix tailTrace_3205946
  have hstable : (prefixWord ++ tailWord_3205946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205946).length < 2 ^ (prefixWord ++ tailWord_3205946).sum := by decide
  have hdescent : baseEnd_3205946 < baseStart_3205946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205956 : List Nat := [2, 3, 4, 2, 1, 1, 1, 2, 1, 6]
def baseStart_3205956 : Nat := 118140960795 + 3205956 * 2 ^ 59
def prefixEnd_3205956 : Nat := 4983230072969 + 3 ^ 40 * 3205956 * 2
def baseEnd_3205956 : Nat := 548732128388587972035361

theorem tailTrace_3205956 : CollatzResearch.WordTrace tailWord_3205956 prefixEnd_3205956 548732128388587972035361 := by
  unfold tailWord_3205956
  simp only [CollatzResearch.WordTrace]
  refine ⟨58465410786688210269262861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77953881048917613692350481 58465410786688210269262861)
  ·
    refine ⟨21924529045008078850973573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58465410786688210269262861 21924529045008078850973573)
    ·
      refine ⟨4110849195939014784557545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21924529045008078850973573 4110849195939014784557545)
      ·
        refine ⟨3083136896954261088418159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4110849195939014784557545 3083136896954261088418159)
        ·
          refine ⟨4624705345431391632627239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3083136896954261088418159 4624705345431391632627239)
          ·
            refine ⟨6937058018147087448940859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4624705345431391632627239 6937058018147087448940859)
            ·
              refine ⟨10405587027220631173411289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6937058018147087448940859 10405587027220631173411289)
              ·
                refine ⟨7804190270415473380058467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10405587027220631173411289 7804190270415473380058467)
                ·
                  refine ⟨11706285405623210070087701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7804190270415473380058467 11706285405623210070087701)
                  ·
                    refine ⟨548732128388587972035361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11706285405623210070087701 548732128388587972035361)
                    ·
                      rfl

theorem cell23_3205956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_3205956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205956 prefixEnd_3205956 := by exact prefixLift 3205956
  have htrace : WordTrace (prefixWord ++ tailWord_3205956) baseStart_3205956 baseEnd_3205956 := by
    simpa [prefixWord, tailWord_3205956, baseEnd_3205956] using wordTrace_append hprefix tailTrace_3205956
  have hstable : (prefixWord ++ tailWord_3205956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205956).length < 2 ^ (prefixWord ++ tailWord_3205956).sum := by decide
  have hdescent : baseEnd_3205956 < baseStart_3205956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205980 : List Nat := [2, 2, 4, 2, 1, 2, 1, 4, 1, 2, 2]
def baseStart_3205980 : Nat := 118140960795 + 3205980 * 2 ^ 59
def prefixEnd_3205980 : Nat := 4983230072969 + 3 ^ 40 * 3205980 * 2
def baseEnd_3205980 : Nat := 1646208708701471822205973

theorem tailTrace_3205980 : CollatzResearch.WordTrace tailWord_3205980 prefixEnd_3205980 1646208708701471822205973 := by
  unfold tailWord_3205980
  simp only [CollatzResearch.WordTrace]
  refine ⟨58465848462644736318699697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77954464616859648424932929 58465848462644736318699697)
  ·
    refine ⟨43849386346983552239024773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58465848462644736318699697 43849386346983552239024773)
    ·
      refine ⟨8221759940059416044817145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43849386346983552239024773 8221759940059416044817145)
      ·
        refine ⟨6166319955044562033612859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8221759940059416044817145 6166319955044562033612859)
        ·
          refine ⟨9249479932566843050419289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6166319955044562033612859 9249479932566843050419289)
          ·
            refine ⟨6937109949425132287814467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9249479932566843050419289 6937109949425132287814467)
            ·
              refine ⟨10405664924137698431721701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6937109949425132287814467 10405664924137698431721701)
              ·
                refine ⟨1951062173275818455947819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10405664924137698431721701 1951062173275818455947819)
                ·
                  refine ⟨2926593259913727683921729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951062173275818455947819 2926593259913727683921729)
                  ·
                    refine ⟨2194944944935295762941297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2926593259913727683921729 2194944944935295762941297)
                    ·
                      refine ⟨1646208708701471822205973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2194944944935295762941297 1646208708701471822205973)
                      ·
                        rfl

theorem cell23_3205980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_3205980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205980 prefixEnd_3205980 := by exact prefixLift 3205980
  have htrace : WordTrace (prefixWord ++ tailWord_3205980) baseStart_3205980 baseEnd_3205980 := by
    simpa [prefixWord, tailWord_3205980, baseEnd_3205980] using wordTrace_append hprefix tailTrace_3205980
  have hstable : (prefixWord ++ tailWord_3205980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205980).length < 2 ^ (prefixWord ++ tailWord_3205980).sum := by decide
  have hdescent : baseEnd_3205980 < baseStart_3205980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205986 : List Nat := [3, 3, 2, 1, 4, 1, 1, 8]
def baseStart_3205986 : Nat := 118140960795 + 3205986 * 2 ^ 59
def prefixEnd_3205986 : Nat := 4983230072969 + 3 ^ 40 * 3205986 * 2
def baseEnd_3205986 : Nat := 60970807021681436990035

theorem tailTrace_3205986 : CollatzResearch.WordTrace tailWord_3205986 prefixEnd_3205986 60970807021681436990035 := by
  unfold tailWord_3205986
  simp only [CollatzResearch.WordTrace]
  refine ⟨29232978940816933915529453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77954610508845157108078541 29232978940816933915529453)
  ·
    refine ⟨10962367102806350218323545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29232978940816933915529453 10962367102806350218323545)
    ·
      refine ⟨8221775327104762663742659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10962367102806350218323545 8221775327104762663742659)
      ·
        refine ⟨12332662990657143995613989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8221775327104762663742659 12332662990657143995613989)
        ·
          refine ⟨2312374310748214499177623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12332662990657143995613989 2312374310748214499177623)
          ·
            refine ⟨3468561466122321748766435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2312374310748214499177623 3468561466122321748766435)
            ·
              refine ⟨5202842199183482623149653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3468561466122321748766435 5202842199183482623149653)
              ·
                refine ⟨60970807021681436990035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5202842199183482623149653 60970807021681436990035)
                ·
                  rfl

theorem cell23_3205986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 4, 1, 1, 8].length) (baseStart_3205986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205986 prefixEnd_3205986 := by exact prefixLift 3205986
  have htrace : WordTrace (prefixWord ++ tailWord_3205986) baseStart_3205986 baseEnd_3205986 := by
    simpa [prefixWord, tailWord_3205986, baseEnd_3205986] using wordTrace_append hprefix tailTrace_3205986
  have hstable : (prefixWord ++ tailWord_3205986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205986).length < 2 ^ (prefixWord ++ tailWord_3205986).sum := by decide
  have hdescent : baseEnd_3205986 < baseStart_3205986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205989 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 3, 3, 2]
def baseStart_3205989 : Nat := 118140960795 + 3205989 * 2 ^ 59
def prefixEnd_3205989 : Nat := 4983230072969 + 3 ^ 40 * 3205989 * 2
def baseEnd_3205989 : Nat := 1646213330027362286993431

theorem tailTrace_3205989 : CollatzResearch.WordTrace tailWord_3205989 prefixEnd_3205989 1646213330027362286993431 := by
  unfold tailWord_3205989
  simp only [CollatzResearch.WordTrace]
  refine ⟨116932025182256867174477021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77954683454837911449651347 116932025182256867174477021)
  ·
    refine ⟨43849509443346325190428883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116932025182256867174477021 43849509443346325190428883)
    ·
      refine ⟨65774264165019487785643325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43849509443346325190428883 65774264165019487785643325)
      ·
        refine ⟨24665349061882307919616247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65774264165019487785643325 24665349061882307919616247)
        ·
          refine ⟨36998023592823461879424371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24665349061882307919616247 36998023592823461879424371)
          ·
            refine ⟨55497035389235192819136557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36998023592823461879424371 55497035389235192819136557)
            ·
              refine ⟨20811388270963197307176209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55497035389235192819136557 20811388270963197307176209)
              ·
                refine ⟨15608541203222397980382157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20811388270963197307176209 15608541203222397980382157)
                ·
                  refine ⟨5853202951208399242643309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15608541203222397980382157 5853202951208399242643309)
                  ·
                    refine ⟨2194951106703149715991241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5853202951208399242643309 2194951106703149715991241)
                    ·
                      refine ⟨1646213330027362286993431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2194951106703149715991241 1646213330027362286993431)
                      ·
                        rfl

theorem cell23_3205989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 3, 3, 2].length) (baseStart_3205989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205989 prefixEnd_3205989 := by exact prefixLift 3205989
  have htrace : WordTrace (prefixWord ++ tailWord_3205989) baseStart_3205989 baseEnd_3205989 := by
    simpa [prefixWord, tailWord_3205989, baseEnd_3205989] using wordTrace_append hprefix tailTrace_3205989
  have hstable : (prefixWord ++ tailWord_3205989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205989).length < 2 ^ (prefixWord ++ tailWord_3205989).sum := by decide
  have hdescent : baseEnd_3205989 < baseStart_3205989 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3205995 : List Nat := [1, 1, 1, 1, 2, 2, 5, 1, 1, 8]
def baseStart_3205995 : Nat := 118140960795 + 3205995 * 2 ^ 59
def prefixEnd_3205995 : Nat := 4983230072969 + 3 ^ 40 * 3205995 * 2
def baseEnd_3205995 : Nat := 548738803637096421172801

theorem tailTrace_3205995 : CollatzResearch.WordTrace tailWord_3205995 prefixEnd_3205995 548738803637096421172801 := by
  unfold tailWord_3205995
  simp only [CollatzResearch.WordTrace]
  refine ⟨116932244020235130199195439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77954829346823420132796959 116932244020235130199195439)
  ·
    refine ⟨175398366030352695298793159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116932244020235130199195439 175398366030352695298793159)
    ·
      refine ⟨263097549045529042948189739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175398366030352695298793159 263097549045529042948189739)
      ·
        refine ⟨394646323568293564422284609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263097549045529042948189739 394646323568293564422284609)
        ·
          refine ⟨295984742676220173316713457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394646323568293564422284609 295984742676220173316713457)
          ·
            refine ⟨221988557007165129987535093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295984742676220173316713457 221988557007165129987535093)
            ·
              refine ⟨20811427219421730936331415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 221988557007165129987535093 20811427219421730936331415)
              ·
                refine ⟨31217140829132596404497123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20811427219421730936331415 31217140829132596404497123)
                ·
                  refine ⟨46825711243698894606745685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31217140829132596404497123 46825711243698894606745685)
                  ·
                    refine ⟨548738803637096421172801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46825711243698894606745685 548738803637096421172801)
                    ·
                      rfl

theorem cell23_3205995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 5, 1, 1, 8].length) (baseStart_3205995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3205995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3205995 prefixEnd_3205995 := by exact prefixLift 3205995
  have htrace : WordTrace (prefixWord ++ tailWord_3205995) baseStart_3205995 baseEnd_3205995 := by
    simpa [prefixWord, tailWord_3205995, baseEnd_3205995] using wordTrace_append hprefix tailTrace_3205995
  have hstable : (prefixWord ++ tailWord_3205995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3205995).length < 2 ^ (prefixWord ++ tailWord_3205995).sum := by decide
  have hdescent : baseEnd_3205995 < baseStart_3205995 := by decide
  rcases family_descends (prefixWord ++ tailWord_3205995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206019 : List Nat := [1, 1, 1, 3, 4, 1, 1, 4, 1, 4, 2]
def baseStart_3206019 : Nat := 118140960795 + 3206019 * 2 ^ 59
def prefixEnd_3206019 : Nat := 4983230072969 + 3 ^ 40 * 3206019 * 2
def baseEnd_3206019 : Nat := 1646228734446997169618293

theorem tailTrace_3206019 : CollatzResearch.WordTrace tailWord_3206019 prefixEnd_3206019 1646228734446997169618293 := by
  unfold tailWord_3206019
  simp only [CollatzResearch.WordTrace]
  refine ⟨116933119372148182298069111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77955412914765454865379407 116933119372148182298069111)
  ·
    refine ⟨175399679058222273447103667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116933119372148182298069111 175399679058222273447103667)
    ·
      refine ⟨263099518587333410170655501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175399679058222273447103667 263099518587333410170655501)
      ·
        refine ⟨98662319470250028813995813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263099518587333410170655501 98662319470250028813995813)
        ·
          refine ⟨18499184900671880402624215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98662319470250028813995813 18499184900671880402624215)
          ·
            refine ⟨27748777351007820603936323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18499184900671880402624215 27748777351007820603936323)
            ·
              refine ⟨41623166026511730905904485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27748777351007820603936323 41623166026511730905904485)
              ·
                refine ⟨7804343629970949544857091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41623166026511730905904485 7804343629970949544857091)
                ·
                  refine ⟨11706515444956424317285637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7804343629970949544857091 11706515444956424317285637)
                  ·
                    refine ⟨2194971645929329559491057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11706515444956424317285637 2194971645929329559491057)
                    ·
                      refine ⟨1646228734446997169618293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2194971645929329559491057 1646228734446997169618293)
                      ·
                        rfl

theorem cell23_3206019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 4, 2].length) (baseStart_3206019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206019 prefixEnd_3206019 := by exact prefixLift 3206019
  have htrace : WordTrace (prefixWord ++ tailWord_3206019) baseStart_3206019 baseEnd_3206019 := by
    simpa [prefixWord, tailWord_3206019, baseEnd_3206019] using wordTrace_append hprefix tailTrace_3206019
  have hstable : (prefixWord ++ tailWord_3206019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206019).length < 2 ^ (prefixWord ++ tailWord_3206019).sum := by decide
  have hdescent : baseEnd_3206019 < baseStart_3206019 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206023 : List Nat := [1, 1, 4, 2, 3, 1, 4, 1, 1, 3, 2]
def baseStart_3206023 : Nat := 118140960795 + 3206023 * 2 ^ 59
def prefixEnd_3206023 : Nat := 4983230072969 + 3 ^ 40 * 3206023 * 2
def baseEnd_3206023 : Nat := 1646230788369615153968275

theorem tailTrace_3206023 : CollatzResearch.WordTrace tailWord_3206023 prefixEnd_3206023 1646230788369615153968275 := by
  unfold tailWord_3206023
  simp only [CollatzResearch.WordTrace]
  refine ⟨116933265264133690981214723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77955510176089127320809815 116933265264133690981214723)
  ·
    refine ⟨175399897896200536471822085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116933265264133690981214723 175399897896200536471822085)
    ·
      refine ⟨32887480855537600588466641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175399897896200536471822085 32887480855537600588466641)
      ·
        refine ⟨24665610641653200441349981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32887480855537600588466641 24665610641653200441349981)
        ·
          refine ⟨9249603990619950165506243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24665610641653200441349981 9249603990619950165506243)
          ·
            refine ⟨13874405985929925248259365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9249603990619950165506243 13874405985929925248259365)
            ·
              refine ⟨2601451122361860984048631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13874405985929925248259365 2601451122361860984048631)
              ·
                refine ⟨3902176683542791476072947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601451122361860984048631 3902176683542791476072947)
                ·
                  refine ⟨5853265025314187214109421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902176683542791476072947 5853265025314187214109421)
                  ·
                    refine ⟨2194974384492820205291033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5853265025314187214109421 2194974384492820205291033)
                    ·
                      refine ⟨1646230788369615153968275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2194974384492820205291033 1646230788369615153968275)
                      ·
                        rfl

theorem cell23_3206023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_3206023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206023 prefixEnd_3206023 := by exact prefixLift 3206023
  have htrace : WordTrace (prefixWord ++ tailWord_3206023) baseStart_3206023 baseEnd_3206023 := by
    simpa [prefixWord, tailWord_3206023, baseEnd_3206023] using wordTrace_append hprefix tailTrace_3206023
  have hstable : (prefixWord ++ tailWord_3206023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206023).length < 2 ^ (prefixWord ++ tailWord_3206023).sum := by decide
  have hdescent : baseEnd_3206023 < baseStart_3206023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206035 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 9]
def baseStart_3206035 : Nat := 118140960795 + 3206035 * 2 ^ 59
def prefixEnd_3206035 : Nat := 4983230072969 + 3 ^ 40 * 3206035 * 2
def baseEnd_3206035 : Nat := 1646236950137469107018219

theorem tailTrace_3206035 : CollatzResearch.WordTrace tailWord_3206035 prefixEnd_3206035 1646236950137469107018219 := by
  unfold tailWord_3206035
  simp only [CollatzResearch.WordTrace]
  refine ⟨116933702940090217030651559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77955801960060144687101039 116933702940090217030651559)
  ·
    refine ⟨175400554410135325545977339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116933702940090217030651559 175400554410135325545977339)
    ·
      refine ⟨263100831615202988318966009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175400554410135325545977339 263100831615202988318966009)
      ·
        refine ⟨197325623711402241239224507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263100831615202988318966009 197325623711402241239224507)
        ·
          refine ⟨295988435567103361858836761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197325623711402241239224507 295988435567103361858836761)
          ·
            refine ⟨221991326675327521394127571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 295988435567103361858836761 221991326675327521394127571)
            ·
              refine ⟨332986990012991282091191357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 221991326675327521394127571 332986990012991282091191357)
              ·
                refine ⟨124870121254871730784196759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 332986990012991282091191357 124870121254871730784196759)
                ·
                  refine ⟨187305181882307596176295139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124870121254871730784196759 187305181882307596176295139)
                  ·
                    refine ⟨280957772823461394264442709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 187305181882307596176295139 280957772823461394264442709)
                    ·
                      refine ⟨1646236950137469107018219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 280957772823461394264442709 1646236950137469107018219)
                      ·
                        rfl

theorem cell23_3206035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_3206035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206035 prefixEnd_3206035 := by exact prefixLift 3206035
  have htrace : WordTrace (prefixWord ++ tailWord_3206035) baseStart_3206035 baseEnd_3206035 := by
    simpa [prefixWord, tailWord_3206035, baseEnd_3206035] using wordTrace_append hprefix tailTrace_3206035
  have hstable : (prefixWord ++ tailWord_3206035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206035).length < 2 ^ (prefixWord ++ tailWord_3206035).sum := by decide
  have hdescent : baseEnd_3206035 < baseStart_3206035 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206049 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 2, 2, 4]
def baseStart_3206049 : Nat := 118140960795 + 3206049 * 2 ^ 59
def prefixEnd_3206049 : Nat := 4983230072969 + 3 ^ 40 * 3206049 * 2
def baseEnd_3206049 : Nat := 1646244138866632052243155

theorem tailTrace_3206049 : CollatzResearch.WordTrace tailWord_3206049 prefixEnd_3206049 1646244138866632052243155 := by
  unfold tailWord_3206049
  simp only [CollatzResearch.WordTrace]
  refine ⟨116934213562039497421661201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77956142374692998281107467 116934213562039497421661201)
  ·
    refine ⟨87700660171529623066245901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116934213562039497421661201 87700660171529623066245901)
    ·
      refine ⟨32887747564323608649842213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87700660171529623066245901 32887747564323608649842213)
      ·
        refine ⟨6166452668310676621845415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32887747564323608649842213 6166452668310676621845415)
        ·
          refine ⟨9249679002466014932768123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6166452668310676621845415 9249679002466014932768123)
          ·
            refine ⟨13874518503699022399152185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9249679002466014932768123 13874518503699022399152185)
            ·
              refine ⟨10405888877774266799364139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13874518503699022399152185 10405888877774266799364139)
              ·
                refine ⟨15608833316661400199046209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10405888877774266799364139 15608833316661400199046209)
                ·
                  refine ⟨11706624987496050149284657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15608833316661400199046209 11706624987496050149284657)
                  ·
                    refine ⟨8779968740622037611963493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11706624987496050149284657 8779968740622037611963493)
                    ·
                      refine ⟨1646244138866632052243155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8779968740622037611963493 1646244138866632052243155)
                      ·
                        rfl

theorem cell23_3206049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_3206049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206049 prefixEnd_3206049 := by exact prefixLift 3206049
  have htrace : WordTrace (prefixWord ++ tailWord_3206049) baseStart_3206049 baseEnd_3206049 := by
    simpa [prefixWord, tailWord_3206049, baseEnd_3206049] using wordTrace_append hprefix tailTrace_3206049
  have hstable : (prefixWord ++ tailWord_3206049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206049).length < 2 ^ (prefixWord ++ tailWord_3206049).sum := by decide
  have hdescent : baseEnd_3206049 < baseStart_3206049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206072 : List Nat := [2, 1, 2, 1, 2, 4, 2, 1, 1, 7]
def baseStart_3206072 : Nat := 118140960795 + 3206072 * 2 ^ 59
def prefixEnd_3206072 : Nat := 4983230072969 + 3 ^ 40 * 3206072 * 2
def baseEnd_3206072 : Nat := 548751982973895154085183

theorem tailTrace_3206072 : CollatzResearch.WordTrace tailWord_3206072 prefixEnd_3206072 548751982973895154085183 := by
  unfold tailWord_3206072
  simp only [CollatzResearch.WordTrace]
  refine ⟨58467526220478086174874235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77956701627304114899832313 58467526220478086174874235)
  ·
    refine ⟨87701289330717129262311353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58467526220478086174874235 87701289330717129262311353)
    ·
      refine ⟨65775966998037846946733515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87701289330717129262311353 65775966998037846946733515)
      ·
        refine ⟨98663950497056770420100273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65775966998037846946733515 98663950497056770420100273)
        ·
          refine ⟨73997962872792577815075205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98663950497056770420100273 73997962872792577815075205)
          ·
            refine ⟨13874618038648608340326601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 73997962872792577815075205 13874618038648608340326601)
            ·
              refine ⟨10405963528986456255244951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13874618038648608340326601 10405963528986456255244951)
              ·
                refine ⟨15608945293479684382867427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10405963528986456255244951 15608945293479684382867427)
                ·
                  refine ⟨23413417940219526574301141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15608945293479684382867427 23413417940219526574301141)
                  ·
                    refine ⟨548751982973895154085183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23413417940219526574301141 548751982973895154085183)
                    ·
                      rfl

theorem cell23_3206072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 1, 7].length) (baseStart_3206072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206072 prefixEnd_3206072 := by exact prefixLift 3206072
  have htrace : WordTrace (prefixWord ++ tailWord_3206072) baseStart_3206072 baseEnd_3206072 := by
    simpa [prefixWord, tailWord_3206072, baseEnd_3206072] using wordTrace_append hprefix tailTrace_3206072
  have hstable : (prefixWord ++ tailWord_3206072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206072).length < 2 ^ (prefixWord ++ tailWord_3206072).sum := by decide
  have hdescent : baseEnd_3206072 < baseStart_3206072 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206136 : List Nat := [2, 1, 2, 1, 1, 3, 1, 7, 1, 4]
def baseStart_3206136 : Nat := 118140960795 + 3206136 * 2 ^ 59
def prefixEnd_3206136 : Nat := 4983230072969 + 3 ^ 40 * 3206136 * 2
def baseEnd_3206136 : Nat := 548762937227857737285085

theorem tailTrace_3206136 : CollatzResearch.WordTrace tailWord_3206136 prefixEnd_3206136 548762937227857737285085 := by
  unfold tailWord_3206136
  simp only [CollatzResearch.WordTrace]
  refine ⟨58468693356362155640039131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77958257808482874186718841 58468693356362155640039131)
  ·
    refine ⟨87703040034543233460058697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58468693356362155640039131 87703040034543233460058697)
    ·
      refine ⟨65777280025907425095044023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87703040034543233460058697 65777280025907425095044023)
      ·
        refine ⟨98665920038861137642566035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65777280025907425095044023 98665920038861137642566035)
        ·
          refine ⟨147998880058291706463849053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98665920038861137642566035 147998880058291706463849053)
          ·
            refine ⟨55499580021859389923943395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 147998880058291706463849053 55499580021859389923943395)
            ·
              refine ⟨83249370032789084885915093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55499580021859389923943395 83249370032789084885915093)
              ·
                refine ⟨1951157110143494177013635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 83249370032789084885915093 1951157110143494177013635)
                ·
                  refine ⟨2926735665215241265520453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951157110143494177013635 2926735665215241265520453)
                  ·
                    refine ⟨548762937227857737285085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2926735665215241265520453 548762937227857737285085)
                    ·
                      rfl

theorem cell23_3206136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 7, 1, 4].length) (baseStart_3206136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206136 prefixEnd_3206136 := by exact prefixLift 3206136
  have htrace : WordTrace (prefixWord ++ tailWord_3206136) baseStart_3206136 baseEnd_3206136 := by
    simpa [prefixWord, tailWord_3206136, baseEnd_3206136] using wordTrace_append hprefix tailTrace_3206136
  have hstable : (prefixWord ++ tailWord_3206136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206136).length < 2 ^ (prefixWord ++ tailWord_3206136).sum := by decide
  have hdescent : baseEnd_3206136 < baseStart_3206136 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206149 : List Nat := [1, 3, 1, 1, 2, 3, 4, 2, 6]
def baseStart_3206149 : Nat := 118140960795 + 3206149 * 2 ^ 59
def prefixEnd_3206149 : Nat := 4983230072969 + 3 ^ 40 * 3206149 * 2
def baseEnd_3206149 : Nat := 182921720770231295665855

theorem tailTrace_3206149 : CollatzResearch.WordTrace tailWord_3206149 prefixEnd_3206149 182921720770231295665855 := by
  unfold tailWord_3206149
  simp only [CollatzResearch.WordTrace]
  refine ⟨116937860861677214500301501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77958573907784809666867667 116937860861677214500301501)
  ·
    refine ⟨43851697823128955437613063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116937860861677214500301501 43851697823128955437613063)
    ·
      refine ⟨65777546734693433156419595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43851697823128955437613063 65777546734693433156419595)
      ·
        refine ⟨98666320102040149734629393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65777546734693433156419595 98666320102040149734629393)
        ·
          refine ⟨73999740076530112300972045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98666320102040149734629393 73999740076530112300972045)
          ·
            refine ⟨27749902528698792112864517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 73999740076530112300972045 27749902528698792112864517)
            ·
              refine ⟨5203106724131023521162097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27749902528698792112864517 5203106724131023521162097)
              ·
                refine ⟨3902330043098267640871573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5203106724131023521162097 3902330043098267640871573)
                ·
                  refine ⟨182921720770231295665855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3902330043098267640871573 182921720770231295665855)
                  ·
                    rfl

theorem cell23_3206149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 4, 2, 6].length) (baseStart_3206149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206149 prefixEnd_3206149 := by exact prefixLift 3206149
  have htrace : WordTrace (prefixWord ++ tailWord_3206149) baseStart_3206149 baseEnd_3206149 := by
    simpa [prefixWord, tailWord_3206149, baseEnd_3206149] using wordTrace_append hprefix tailTrace_3206149
  have hstable : (prefixWord ++ tailWord_3206149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206149).length < 2 ^ (prefixWord ++ tailWord_3206149).sum := by decide
  have hdescent : baseEnd_3206149 < baseStart_3206149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206179 : List Nat := [1, 1, 1, 4, 3, 2, 2, 1, 3, 5]
def baseStart_3206179 : Nat := 118140960795 + 3206179 * 2 ^ 59
def prefixEnd_3206179 : Nat := 4983230072969 + 3 ^ 40 * 3206179 * 2
def baseEnd_3206179 : Nat := 548770297117238847872519

theorem tailTrace_3206179 : CollatzResearch.WordTrace tailWord_3206179 prefixEnd_3206179 548770297117238847872519 := by
  unfold tailWord_3206179
  simp only [CollatzResearch.WordTrace]
  refine ⟨116938955051568529623893591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77959303367712353082595727 116938955051568529623893591)
  ·
    refine ⟨175408432577352794435840387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116938955051568529623893591 175408432577352794435840387)
    ·
      refine ⟨263112648866029191653760581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175408432577352794435840387 263112648866029191653760581)
      ·
        refine ⟨49333621662380473435080109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263112648866029191653760581 49333621662380473435080109)
        ·
          refine ⟨18500108123392677538155041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49333621662380473435080109 18500108123392677538155041)
          ·
            refine ⟨13875081092544508153616281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18500108123392677538155041 13875081092544508153616281)
            ·
              refine ⟨10406310819408381115212211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13875081092544508153616281 10406310819408381115212211)
              ·
                refine ⟨15609466229112571672818317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10406310819408381115212211 15609466229112571672818317)
                ·
                  refine ⟨5853549835917214377306869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15609466229112571672818317 5853549835917214377306869)
                  ·
                    refine ⟨548770297117238847872519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5853549835917214377306869 548770297117238847872519)
                    ·
                      rfl

theorem cell23_3206179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 2, 1, 3, 5].length) (baseStart_3206179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206179 prefixEnd_3206179 := by exact prefixLift 3206179
  have htrace : WordTrace (prefixWord ++ tailWord_3206179) baseStart_3206179 baseEnd_3206179 := by
    simpa [prefixWord, tailWord_3206179, baseEnd_3206179] using wordTrace_append hprefix tailTrace_3206179
  have hstable : (prefixWord ++ tailWord_3206179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206179).length < 2 ^ (prefixWord ++ tailWord_3206179).sum := by decide
  have hdescent : baseEnd_3206179 < baseStart_3206179 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206226 : List Nat := [3, 2, 2, 1, 3, 1, 3, 1, 1, 6]
def baseStart_3206226 : Nat := 118140960795 + 3206226 * 2 ^ 59
def prefixEnd_3206226 : Nat := 4983230072969 + 3 ^ 40 * 3206226 * 2
def baseEnd_3206226 : Nat := 548778341647492619909947

theorem tailTrace_3206226 : CollatzResearch.WordTrace tailWord_3206226 prefixEnd_3206226 548778341647492619909947 := by
  unfold tailWord_3206226
  simp only [CollatzResearch.WordTrace]
  refine ⟨29235167320599564162713633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77960446188265504433903021 29235167320599564162713633)
  ·
    refine ⟨21926375490449673122035225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29235167320599564162713633 21926375490449673122035225)
    ·
      refine ⟨16444781617837254841526419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21926375490449673122035225 16444781617837254841526419)
      ·
        refine ⟨24667172426755882262289629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16444781617837254841526419 24667172426755882262289629)
        ·
          refine ⟨9250189660033455848358611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24667172426755882262289629 9250189660033455848358611)
          ·
            refine ⟨13875284490050183772537917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9250189660033455848358611 13875284490050183772537917)
            ·
              refine ⟨5203231683768818914701719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13875284490050183772537917 5203231683768818914701719)
              ·
                refine ⟨7804847525653228372052579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5203231683768818914701719 7804847525653228372052579)
                ·
                  refine ⟨11707271288479842558078869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7804847525653228372052579 11707271288479842558078869)
                  ·
                    refine ⟨548778341647492619909947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11707271288479842558078869 548778341647492619909947)
                    ·
                      rfl

theorem cell23_3206226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 3, 1, 1, 6].length) (baseStart_3206226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206226 prefixEnd_3206226 := by exact prefixLift 3206226
  have htrace : WordTrace (prefixWord ++ tailWord_3206226) baseStart_3206226 baseEnd_3206226 := by
    simpa [prefixWord, tailWord_3206226, baseEnd_3206226] using wordTrace_append hprefix tailTrace_3206226
  have hstable : (prefixWord ++ tailWord_3206226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206226).length < 2 ^ (prefixWord ++ tailWord_3206226).sum := by decide
  have hdescent : baseEnd_3206226 < baseStart_3206226 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206229 : List Nat := [1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 6]
def baseStart_3206229 : Nat := 118140960795 + 3206229 * 2 ^ 59
def prefixEnd_3206229 : Nat := 4983230072969 + 3 ^ 40 * 3206229 * 2
def baseEnd_3206229 : Nat := 1646336565384441347992327

theorem tailTrace_3206229 : CollatzResearch.WordTrace tailWord_3206229 prefixEnd_3206229 1646336565384441347992327 := by
  unfold tailWord_3206229
  simp only [CollatzResearch.WordTrace]
  refine ⟨116940778701387388163213741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77960519134258258775475827 116940778701387388163213741)
  ·
    refine ⟨43852792013020270561205153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116940778701387388163213741 43852792013020270561205153)
    ·
      refine ⟨32889594009765202920903865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43852792013020270561205153 32889594009765202920903865)
      ·
        refine ⟨24667195507323902190677899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32889594009765202920903865 24667195507323902190677899)
        ·
          refine ⟨37000793260985853286016849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24667195507323902190677899 37000793260985853286016849)
          ·
            refine ⟨27750594945739389964512637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37000793260985853286016849 27750594945739389964512637)
            ·
              refine ⟨10406473104652271236692239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27750594945739389964512637 10406473104652271236692239)
              ·
                refine ⟨15609709656978406855038359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10406473104652271236692239 15609709656978406855038359)
                ·
                  refine ⟨23414564485467610282557539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15609709656978406855038359 23414564485467610282557539)
                  ·
                    refine ⟨35121846728201415423836309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23414564485467610282557539 35121846728201415423836309)
                    ·
                      refine ⟨1646336565384441347992327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35121846728201415423836309 1646336565384441347992327)
                      ·
                        rfl

theorem cell23_3206229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_3206229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206229 prefixEnd_3206229 := by exact prefixLift 3206229
  have htrace : WordTrace (prefixWord ++ tailWord_3206229) baseStart_3206229 baseEnd_3206229 := by
    simpa [prefixWord, tailWord_3206229, baseEnd_3206229] using wordTrace_append hprefix tailTrace_3206229
  have hstable : (prefixWord ++ tailWord_3206229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206229).length < 2 ^ (prefixWord ++ tailWord_3206229).sum := by decide
  have hdescent : baseEnd_3206229 < baseStart_3206229 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206253 : List Nat := [1, 5, 1, 1, 2, 2, 2, 3, 1, 2, 3]
def baseStart_3206253 : Nat := 118140960795 + 3206253 * 2 ^ 59
def prefixEnd_3206253 : Nat := 4983230072969 + 3 ^ 40 * 3206253 * 2
def baseEnd_3206253 : Nat := 1646348888920149254092217

theorem tailTrace_3206253 : CollatzResearch.WordTrace tailWord_3206253 prefixEnd_3206253 1646348888920149254092217 := by
  unfold tailWord_3206253
  simp only [CollatzResearch.WordTrace]
  refine ⟨116941654053300440262087413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77961102702200293508058275 116941654053300440262087413)
  ·
    refine ⟨10963280067496916274570695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116941654053300440262087413 10963280067496916274570695)
    ·
      refine ⟨16444920101245374411856043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10963280067496916274570695 16444920101245374411856043)
      ·
        refine ⟨24667380151868061617784065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16444920101245374411856043 24667380151868061617784065)
        ·
          refine ⟨18500535113901046213338049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24667380151868061617784065 18500535113901046213338049)
          ·
            refine ⟨13875401335425784660003537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18500535113901046213338049 13875401335425784660003537)
            ·
              refine ⟨10406551001569338495002653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13875401335425784660003537 10406551001569338495002653)
              ·
                refine ⟨3902456625588501935625995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10406551001569338495002653 3902456625588501935625995)
                ·
                  refine ⟨5853684938382752903438993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902456625588501935625995 5853684938382752903438993)
                  ·
                    refine ⟨4390263703787064677579245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5853684938382752903438993 4390263703787064677579245)
                    ·
                      refine ⟨1646348888920149254092217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4390263703787064677579245 1646348888920149254092217)
                      ·
                        rfl

theorem cell23_3206253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 2, 3, 1, 2, 3].length) (baseStart_3206253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206253 prefixEnd_3206253 := by exact prefixLift 3206253
  have htrace : WordTrace (prefixWord ++ tailWord_3206253) baseStart_3206253 baseEnd_3206253 := by
    simpa [prefixWord, tailWord_3206253, baseEnd_3206253] using wordTrace_append hprefix tailTrace_3206253
  have hstable : (prefixWord ++ tailWord_3206253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206253).length < 2 ^ (prefixWord ++ tailWord_3206253).sum := by decide
  have hdescent : baseEnd_3206253 < baseStart_3206253 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206269 : List Nat := [1, 4, 1, 1, 3, 1, 2, 1, 2, 7]
def baseStart_3206269 : Nat := 118140960795 + 3206269 * 2 ^ 59
def prefixEnd_3206269 : Nat := 4983230072969 + 3 ^ 40 * 3206269 * 2
def baseEnd_3206269 : Nat := 548785701536873730497381

theorem tailTrace_3206269 : CollatzResearch.WordTrace tailWord_3206269 prefixEnd_3206269 548785701536873730497381 := by
  unfold tailWord_3206269
  simp only [CollatzResearch.WordTrace]
  refine ⟨116942237621242474994669861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77961491747494983329779907 116942237621242474994669861)
  ·
    refine ⟨21926669553982964061500599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116942237621242474994669861 21926669553982964061500599)
    ·
      refine ⟨32890004330974446092250899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21926669553982964061500599 32890004330974446092250899)
      ·
        refine ⟨49335006496461669138376349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32890004330974446092250899 49335006496461669138376349)
        ·
          refine ⟨18500627436173125926891131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49335006496461669138376349 18500627436173125926891131)
          ·
            refine ⟨27750941154259688890336697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18500627436173125926891131 27750941154259688890336697)
            ·
              refine ⟨20813205865694766667752523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27750941154259688890336697 20813205865694766667752523)
              ·
                refine ⟨31219808798542150001628785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20813205865694766667752523 31219808798542150001628785)
                ·
                  refine ⟨23414856598906612501221589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31219808798542150001628785 23414856598906612501221589)
                  ·
                    refine ⟨548785701536873730497381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23414856598906612501221589 548785701536873730497381)
                    ·
                      rfl

theorem cell23_3206269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_3206269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206269 prefixEnd_3206269 := by exact prefixLift 3206269
  have htrace : WordTrace (prefixWord ++ tailWord_3206269) baseStart_3206269 baseEnd_3206269 := by
    simpa [prefixWord, tailWord_3206269, baseEnd_3206269] using wordTrace_append hprefix tailTrace_3206269
  have hstable : (prefixWord ++ tailWord_3206269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206269).length < 2 ^ (prefixWord ++ tailWord_3206269).sum := by decide
  have hdescent : baseEnd_3206269 < baseStart_3206269 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206277 : List Nat := [1, 3, 1, 1, 7, 1, 2, 1, 2, 4]
def baseStart_3206277 : Nat := 118140960795 + 3206277 * 2 ^ 59
def prefixEnd_3206277 : Nat := 4983230072969 + 3 ^ 40 * 3206277 * 2
def baseEnd_3206277 : Nat := 548787070818619053397369

theorem tailTrace_3206277 : CollatzResearch.WordTrace tailWord_3206277 prefixEnd_3206277 548787070818619053397369 := by
  unfold tailWord_3206277
  simp only [CollatzResearch.WordTrace]
  refine ⟨116942529405213492360961085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77961686270142328240640723 116942529405213492360961085)
  ·
    refine ⟨43853448526955059635360407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116942529405213492360961085 43853448526955059635360407)
    ·
      refine ⟨65780172790432589453040611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43853448526955059635360407 65780172790432589453040611)
      ·
        refine ⟨98670259185648884179560917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65780172790432589453040611 98670259185648884179560917)
        ·
          refine ⟨2312584199663645722958459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 98670259185648884179560917 2312584199663645722958459)
          ·
            refine ⟨3468876299495468584437689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2312584199663645722958459 3468876299495468584437689)
            ·
              refine ⟨2601657224621601438328267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3468876299495468584437689 2601657224621601438328267)
              ·
                refine ⟨3902485836932402157492401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601657224621601438328267 3902485836932402157492401)
                ·
                  refine ⟨2926864377699301618119301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3902485836932402157492401 2926864377699301618119301)
                  ·
                    refine ⟨548787070818619053397369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2926864377699301618119301 548787070818619053397369)
                    ·
                      rfl

theorem cell23_3206277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 2, 1, 2, 4].length) (baseStart_3206277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206277 prefixEnd_3206277 := by exact prefixLift 3206277
  have htrace : WordTrace (prefixWord ++ tailWord_3206277) baseStart_3206277 baseEnd_3206277 := by
    simpa [prefixWord, tailWord_3206277, baseEnd_3206277] using wordTrace_append hprefix tailTrace_3206277
  have hstable : (prefixWord ++ tailWord_3206277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206277).length < 2 ^ (prefixWord ++ tailWord_3206277).sum := by decide
  have hdescent : baseEnd_3206277 < baseStart_3206277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206293 : List Nat := [1, 3, 2, 1, 1, 1, 2, 6, 1, 3, 2]
def baseStart_3206293 : Nat := 118140960795 + 3206293 * 2 ^ 59
def prefixEnd_3206293 : Nat := 4983230072969 + 3 ^ 40 * 3206293 * 2
def baseEnd_3206293 : Nat := 1646369428146329097592033

theorem tailTrace_3206293 : CollatzResearch.WordTrace tailWord_3206293 prefixEnd_3206293 1646369428146329097592033 := by
  unfold tailWord_3206293
  simp only [CollatzResearch.WordTrace]
  refine ⟨116943112973155527093543533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77962075315437018062362355 116943112973155527093543533)
  ·
    refine ⟨43853667364933322660078825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116943112973155527093543533 43853667364933322660078825)
    ·
      refine ⟨32890250523699991995059119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43853667364933322660078825 32890250523699991995059119)
      ·
        refine ⟨49335375785549987992588679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32890250523699991995059119 49335375785549987992588679)
        ·
          refine ⟨74003063678324981988883019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49335375785549987992588679 74003063678324981988883019)
          ·
            refine ⟨111004595517487472983324529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74003063678324981988883019 111004595517487472983324529)
            ·
              refine ⟨83253446638115604737493397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111004595517487472983324529 83253446638115604737493397)
              ·
                refine ⟨3902505311161668972070003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83253446638115604737493397 3902505311161668972070003)
                ·
                  refine ⟨5853757966742503458105005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902505311161668972070003 5853757966742503458105005)
                  ·
                    refine ⟨2195159237528438796789377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5853757966742503458105005 2195159237528438796789377)
                    ·
                      refine ⟨1646369428146329097592033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2195159237528438796789377 1646369428146329097592033)
                      ·
                        rfl

theorem cell23_3206293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_3206293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206293 prefixEnd_3206293 := by exact prefixLift 3206293
  have htrace : WordTrace (prefixWord ++ tailWord_3206293) baseStart_3206293 baseEnd_3206293 := by
    simpa [prefixWord, tailWord_3206293, baseEnd_3206293] using wordTrace_append hprefix tailTrace_3206293
  have hstable : (prefixWord ++ tailWord_3206293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206293).length < 2 ^ (prefixWord ++ tailWord_3206293).sum := by decide
  have hdescent : baseEnd_3206293 < baseStart_3206293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206317 : List Nat := [1, 5, 2, 1, 3, 1, 2, 2, 2, 1, 3]
def baseStart_3206317 : Nat := 118140960795 + 3206317 * 2 ^ 59
def prefixEnd_3206317 : Nat := 4983230072969 + 3 ^ 40 * 3206317 * 2
def baseEnd_3206317 : Nat := 1646381751682037003691923

theorem tailTrace_3206317 : CollatzResearch.WordTrace tailWord_3206317 prefixEnd_3206317 1646381751682037003691923 := by
  unfold tailWord_3206317
  simp only [CollatzResearch.WordTrace]
  refine ⟨116943988325068579192417205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77962658883379052794944803 116943988325068579192417205)
  ·
    refine ⟨10963498905475179299289113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 116943988325068579192417205 10963498905475179299289113)
    ·
      refine ⟨8222624179106384474466835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10963498905475179299289113 8222624179106384474466835)
      ·
        refine ⟨12333936268659576711700253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8222624179106384474466835 12333936268659576711700253)
        ·
          refine ⟨4625226100747341266887595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12333936268659576711700253 4625226100747341266887595)
          ·
            refine ⟨6937839151121011900331393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4625226100747341266887595 6937839151121011900331393)
            ·
              refine ⟨5203379363340758925248545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6937839151121011900331393 5203379363340758925248545)
              ·
                refine ⟨3902534522505569193936409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5203379363340758925248545 3902534522505569193936409)
                ·
                  refine ⟨2926900891879176895452307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3902534522505569193936409 2926900891879176895452307)
                  ·
                    refine ⟨4390351337818765343178461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2926900891879176895452307 4390351337818765343178461)
                    ·
                      refine ⟨1646381751682037003691923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4390351337818765343178461 1646381751682037003691923)
                      ·
                        rfl

theorem cell23_3206317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_3206317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206317 prefixEnd_3206317 := by exact prefixLift 3206317
  have htrace : WordTrace (prefixWord ++ tailWord_3206317) baseStart_3206317 baseEnd_3206317 := by
    simpa [prefixWord, tailWord_3206317, baseEnd_3206317] using wordTrace_append hprefix tailTrace_3206317
  have hstable : (prefixWord ++ tailWord_3206317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206317).length < 2 ^ (prefixWord ++ tailWord_3206317).sum := by decide
  have hdescent : baseEnd_3206317 < baseStart_3206317 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206323 : List Nat := [1, 1, 1, 2, 3, 2, 2, 3, 4, 2, 2]
def baseStart_3206323 : Nat := 118140960795 + 3206323 * 2 ^ 59
def prefixEnd_3206323 : Nat := 4983230072969 + 3 ^ 40 * 3206323 * 2
def baseEnd_3206323 : Nat := 1646384832565963980216895

theorem tailTrace_3206323 : CollatzResearch.WordTrace tailWord_3206323 prefixEnd_3206323 1646384832565963980216895 := by
  unfold tailWord_3206323
  simp only [CollatzResearch.WordTrace]
  refine ⟨116944207163046842217135623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77962804775364561478090415 116944207163046842217135623)
  ·
    refine ⟨175416310744570263325703435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116944207163046842217135623 175416310744570263325703435)
    ·
      refine ⟨263124466116855394988555153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175416310744570263325703435 263124466116855394988555153)
      ·
        refine ⟨197343349587641546241416365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263124466116855394988555153 197343349587641546241416365)
        ·
          refine ⟨74003756095365579840531137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197343349587641546241416365 74003756095365579840531137)
          ·
            refine ⟨55502817071524184880398353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74003756095365579840531137 55502817071524184880398353)
            ·
              refine ⟨41627112803643138660298765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55502817071524184880398353 41627112803643138660298765)
              ·
                refine ⟨15610167301366176997612037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41627112803643138660298765 15610167301366176997612037)
                ·
                  refine ⟨2926906369006158187052257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15610167301366176997612037 2926906369006158187052257)
                  ·
                    refine ⟨2195179776754618640289193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2926906369006158187052257 2195179776754618640289193)
                    ·
                      refine ⟨1646384832565963980216895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2195179776754618640289193 1646384832565963980216895)
                      ·
                        rfl

theorem cell23_3206323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 3, 4, 2, 2].length) (baseStart_3206323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206323 prefixEnd_3206323 := by exact prefixLift 3206323
  have htrace : WordTrace (prefixWord ++ tailWord_3206323) baseStart_3206323 baseEnd_3206323 := by
    simpa [prefixWord, tailWord_3206323, baseEnd_3206323] using wordTrace_append hprefix tailTrace_3206323
  have hstable : (prefixWord ++ tailWord_3206323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206323).length < 2 ^ (prefixWord ++ tailWord_3206323).sum := by decide
  have hdescent : baseEnd_3206323 < baseStart_3206323 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206346 : List Nat := [3, 1, 2, 1, 3, 3, 1, 2, 7]
def baseStart_3206346 : Nat := 118140960795 + 3206346 * 2 ^ 59
def prefixEnd_3206346 : Nat := 4983230072969 + 3 ^ 40 * 3206346 * 2
def baseEnd_3206346 : Nat := 182932960291224154469921

theorem tailTrace_3206346 : CollatzResearch.WordTrace tailWord_3206346 prefixEnd_3206346 182932960291224154469921 := by
  unfold tailWord_3206346
  simp only [CollatzResearch.WordTrace]
  refine ⟨29236261510490879286305723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77963364027975678096815261 29236261510490879286305723)
  ·
    refine ⟨43854392265736318929458585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29236261510490879286305723 43854392265736318929458585)
    ·
      refine ⟨32890794199302239197093939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43854392265736318929458585 32890794199302239197093939)
      ·
        refine ⟨49336191298953358795640909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32890794199302239197093939 49336191298953358795640909)
        ·
          refine ⟨18501071737107509548365341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49336191298953358795640909 18501071737107509548365341)
          ·
            refine ⟨6937901901415316080637003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18501071737107509548365341 6937901901415316080637003)
            ·
              refine ⟨10406852852122974120955505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6937901901415316080637003 10406852852122974120955505)
              ·
                refine ⟨7805139639092230590716629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10406852852122974120955505 7805139639092230590716629)
                ·
                  refine ⟨182932960291224154469921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7805139639092230590716629 182932960291224154469921)
                  ·
                    rfl

theorem cell23_3206346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 3, 1, 2, 7].length) (baseStart_3206346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206346 prefixEnd_3206346 := by exact prefixLift 3206346
  have htrace : WordTrace (prefixWord ++ tailWord_3206346) baseStart_3206346 baseEnd_3206346 := by
    simpa [prefixWord, tailWord_3206346, baseEnd_3206346] using wordTrace_append hprefix tailTrace_3206346
  have hstable : (prefixWord ++ tailWord_3206346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206346).length < 2 ^ (prefixWord ++ tailWord_3206346).sum := by decide
  have hdescent : baseEnd_3206346 < baseStart_3206346 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206376 : List Nat := [2, 1, 4, 1, 2, 1, 2, 1, 4, 5]
def baseStart_3206376 : Nat := 118140960795 + 3206376 * 2 ^ 59
def prefixEnd_3206376 : Nat := 4983230072969 + 3 ^ 40 * 3206376 * 2
def baseEnd_3206376 : Nat := 548804015680217424284717

theorem tailTrace_3206376 : CollatzResearch.WordTrace tailWord_3206376 prefixEnd_3206376 548804015680217424284717 := by
  unfold tailWord_3206376
  simp only [CollatzResearch.WordTrace]
  refine ⟨58473070115927416134407491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77964093487903221512543321 58473070115927416134407491)
  ·
    refine ⟨87709605173891124201611237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58473070115927416134407491 87709605173891124201611237)
    ·
      refine ⟨16445550970104585787802107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87709605173891124201611237 16445550970104585787802107)
      ·
        refine ⟨24668326455156878681703161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16445550970104585787802107 24668326455156878681703161)
        ·
          refine ⟨18501244841367659011277371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24668326455156878681703161 18501244841367659011277371)
          ·
            refine ⟨27751867262051488516916057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18501244841367659011277371 27751867262051488516916057)
            ·
              refine ⟨20813900446538616387687043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27751867262051488516916057 20813900446538616387687043)
              ·
                refine ⟨31220850669807924581530565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20813900446538616387687043 31220850669807924581530565)
                ·
                  refine ⟨5853909500588985859036981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31220850669807924581530565 5853909500588985859036981)
                  ·
                    refine ⟨548804015680217424284717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5853909500588985859036981 548804015680217424284717)
                    ·
                      rfl

theorem cell23_3206376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 2, 1, 4, 5].length) (baseStart_3206376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206376 prefixEnd_3206376 := by exact prefixLift 3206376
  have htrace : WordTrace (prefixWord ++ tailWord_3206376) baseStart_3206376 baseEnd_3206376 := by
    simpa [prefixWord, tailWord_3206376, baseEnd_3206376] using wordTrace_append hprefix tailTrace_3206376
  have hstable : (prefixWord ++ tailWord_3206376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206376).length < 2 ^ (prefixWord ++ tailWord_3206376).sum := by decide
  have hdescent : baseEnd_3206376 < baseStart_3206376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206436 : List Nat := [2, 3, 1, 3, 1, 1, 1, 3, 8]
def baseStart_3206436 : Nat := 118140960795 + 3206436 * 2 ^ 59
def prefixEnd_3206436 : Nat := 4983230072969 + 3 ^ 40 * 3206436 * 2
def baseEnd_3206436 : Nat := 182938095097769115344875

theorem tailTrace_3206436 : CollatzResearch.WordTrace tailWord_3206436 prefixEnd_3206436 182938095097769115344875 := by
  unfold tailWord_3206436
  simp only [CollatzResearch.WordTrace]
  refine ⟨58474164305818731257999581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77965552407758308343999441 58474164305818731257999581)
  ·
    refine ⟨21927811614682024221749843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58474164305818731257999581 21927811614682024221749843)
    ·
      refine ⟨32891717422023036332624765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21927811614682024221749843 32891717422023036332624765)
      ·
        refine ⟨12334394033258638624734287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32891717422023036332624765 12334394033258638624734287)
        ·
          refine ⟨18501591049887957937101431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12334394033258638624734287 18501591049887957937101431)
          ·
            refine ⟨27752386574831936905652147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18501591049887957937101431 27752386574831936905652147)
            ·
              refine ⟨41628579862247905358478221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27752386574831936905652147 41628579862247905358478221)
              ·
                refine ⟨15610717448342964509429333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41628579862247905358478221 15610717448342964509429333)
                ·
                  refine ⟨182938095097769115344875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15610717448342964509429333 182938095097769115344875)
                  ·
                    rfl

theorem cell23_3206436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 1, 3, 8].length) (baseStart_3206436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206436 prefixEnd_3206436 := by exact prefixLift 3206436
  have htrace : WordTrace (prefixWord ++ tailWord_3206436) baseStart_3206436 baseEnd_3206436 := by
    simpa [prefixWord, tailWord_3206436, baseEnd_3206436] using wordTrace_append hprefix tailTrace_3206436
  have hstable : (prefixWord ++ tailWord_3206436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206436).length < 2 ^ (prefixWord ++ tailWord_3206436).sum := by decide
  have hdescent : baseEnd_3206436 < baseStart_3206436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206440 : List Nat := [2, 1, 5, 1, 2, 1, 3, 1, 3, 4]
def baseStart_3206440 : Nat := 118140960795 + 3206440 * 2 ^ 59
def prefixEnd_3206440 : Nat := 4983230072969 + 3 ^ 40 * 3206440 * 2
def baseEnd_3206440 : Nat := 548814969934180007484619

theorem tailTrace_3206440 : CollatzResearch.WordTrace tailWord_3206440 prefixEnd_3206440 548814969934180007484619 := by
  unfold tailWord_3206440
  simp only [CollatzResearch.WordTrace]
  refine ⟨58474237251811485599572387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77965649669081980799429849 58474237251811485599572387)
  ·
    refine ⟨87711355877717228399358581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58474237251811485599572387 87711355877717228399358581)
    ·
      refine ⟨8222939613535990162439867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87711355877717228399358581 8222939613535990162439867)
      ·
        refine ⟨12334409420303985243659801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8222939613535990162439867 12334409420303985243659801)
        ·
          refine ⟨9250807065227988932744851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12334409420303985243659801 9250807065227988932744851)
          ·
            refine ⟨13876210597841983399117277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9250807065227988932744851 13876210597841983399117277)
            ·
              refine ⟨5203578974190743774668979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13876210597841983399117277 5203578974190743774668979)
              ·
                refine ⟨7805368461286115662003469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5203578974190743774668979 7805368461286115662003469)
                ·
                  refine ⟨2927013172982293373251301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7805368461286115662003469 2927013172982293373251301)
                  ·
                    refine ⟨548814969934180007484619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2927013172982293373251301 548814969934180007484619)
                    ·
                      rfl

theorem cell23_3206440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 1, 3, 4].length) (baseStart_3206440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206440 prefixEnd_3206440 := by exact prefixLift 3206440
  have htrace : WordTrace (prefixWord ++ tailWord_3206440) baseStart_3206440 baseEnd_3206440 := by
    simpa [prefixWord, tailWord_3206440, baseEnd_3206440] using wordTrace_append hprefix tailTrace_3206440
  have hstable : (prefixWord ++ tailWord_3206440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206440).length < 2 ^ (prefixWord ++ tailWord_3206440).sum := by decide
  have hdescent : baseEnd_3206440 < baseStart_3206440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206453 : List Nat := [1, 3, 3, 1, 2, 3, 1, 3, 6]
def baseStart_3206453 : Nat := 118140960795 + 3206453 * 2 ^ 59
def prefixEnd_3206453 : Nat := 4983230072969 + 3 ^ 40 * 3206453 * 2
def baseEnd_3206453 : Nat := 182939065005672052399033

theorem tailTrace_3206453 : CollatzResearch.WordTrace tailWord_3206453 prefixEnd_3206453 182939065005672052399033 := by
  unfold tailWord_3206453
  simp only [CollatzResearch.WordTrace]
  refine ⟨116948948652575874419368013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77965965768383916279578675 116948948652575874419368013)
  ·
    refine ⟨43855855744715952907263005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116948948652575874419368013 43855855744715952907263005)
    ·
      refine ⟨16445945904268482340223627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43855855744715952907263005 16445945904268482340223627)
      ·
        refine ⟨24668918856402723510335441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16445945904268482340223627 24668918856402723510335441)
        ·
          refine ⟨18501689142302042632751581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24668918856402723510335441 18501689142302042632751581)
          ·
            refine ⟨6938133428363265987281843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18501689142302042632751581 6938133428363265987281843)
            ·
              refine ⟨10407200142544898980922765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6938133428363265987281843 10407200142544898980922765)
              ·
                refine ⟨3902700053454337117846037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10407200142544898980922765 3902700053454337117846037)
                ·
                  refine ⟨182939065005672052399033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3902700053454337117846037 182939065005672052399033)
                  ·
                    rfl

theorem cell23_3206453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 6].length) (baseStart_3206453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206453 prefixEnd_3206453 := by exact prefixLift 3206453
  have htrace : WordTrace (prefixWord ++ tailWord_3206453) baseStart_3206453 baseEnd_3206453 := by
    simpa [prefixWord, tailWord_3206453, baseEnd_3206453] using wordTrace_append hprefix tailTrace_3206453
  have hstable : (prefixWord ++ tailWord_3206453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206453).length < 2 ^ (prefixWord ++ tailWord_3206453).sum := by decide
  have hdescent : baseEnd_3206453 < baseStart_3206453 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206473 : List Nat := [1, 2, 1, 1, 2, 3, 2, 3, 1, 5, 2]
def baseStart_3206473 : Nat := 118140960795 + 3206473 * 2 ^ 59
def prefixEnd_3206473 : Nat := 4983230072969 + 3 ^ 40 * 3206473 * 2
def baseEnd_3206473 : Nat := 1646461854664138393341205

theorem tailTrace_3206473 : CollatzResearch.WordTrace tailWord_3206473 prefixEnd_3206473 1646461854664138393341205 := by
  unfold tailWord_3206473
  simp only [CollatzResearch.WordTrace]
  refine ⟨116949678112503417835096073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77966452075002278556730715 116949678112503417835096073)
  ·
    refine ⟨87712258584377563376322055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116949678112503417835096073 87712258584377563376322055)
    ·
      refine ⟨131568387876566345064483083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87712258584377563376322055 131568387876566345064483083)
      ·
        refine ⟨197352581814849517596724625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131568387876566345064483083 197352581814849517596724625)
        ·
          refine ⟨148014436361137138197543469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197352581814849517596724625 148014436361137138197543469)
          ·
            refine ⟨55505413635426426824078801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148014436361137138197543469 55505413635426426824078801)
            ·
              refine ⟨41629060226569820118059101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55505413635426426824078801 41629060226569820118059101)
              ·
                refine ⟨15610897584963682544272163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41629060226569820118059101 15610897584963682544272163)
                ·
                  refine ⟨23416346377445523816408245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15610897584963682544272163 23416346377445523816408245)
                  ·
                    refine ⟨2195282472885517857788273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23416346377445523816408245 2195282472885517857788273)
                    ·
                      refine ⟨1646461854664138393341205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2195282472885517857788273 1646461854664138393341205)
                      ·
                        rfl

theorem cell23_3206473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 5, 2].length) (baseStart_3206473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206473 prefixEnd_3206473 := by exact prefixLift 3206473
  have htrace : WordTrace (prefixWord ++ tailWord_3206473) baseStart_3206473 baseEnd_3206473 := by
    simpa [prefixWord, tailWord_3206473, baseEnd_3206473] using wordTrace_append hprefix tailTrace_3206473
  have hstable : (prefixWord ++ tailWord_3206473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206473).length < 2 ^ (prefixWord ++ tailWord_3206473).sum := by decide
  have hdescent : baseEnd_3206473 < baseStart_3206473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206490 : List Nat := [3, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2]
def baseStart_3206490 : Nat := 118140960795 + 3206490 * 2 ^ 59
def prefixEnd_3206490 : Nat := 4983230072969 + 3 ^ 40 * 3206490 * 2
def baseEnd_3206490 : Nat := 1646470583835264826828627

theorem tailTrace_3206490 : CollatzResearch.WordTrace tailWord_3206490 prefixEnd_3206490 1646470583835264826828627 := by
  unfold tailWord_3206490
  simp only [CollatzResearch.WordTrace]
  refine ⟨29237574538360457434616231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77966865435627886492309949 29237574538360457434616231)
  ·
    refine ⟨43856361807540686151924347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29237574538360457434616231 43856361807540686151924347)
    ·
      refine ⟨65784542711311029227886521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43856361807540686151924347 65784542711311029227886521)
      ·
        refine ⟨49338407033483271920914891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65784542711311029227886521 49338407033483271920914891)
        ·
          refine ⟨74007610550224907881372337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49338407033483271920914891 74007610550224907881372337)
          ·
            refine ⟨55505707912668680911029253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74007610550224907881372337 55505707912668680911029253)
            ·
              refine ⟨10407320233625377670817985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55505707912668680911029253 10407320233625377670817985)
              ·
                refine ⟨7805490175219033253113489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10407320233625377670817985 7805490175219033253113489)
                ·
                  refine ⟨5854117631414274939835117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7805490175219033253113489 5854117631414274939835117)
                  ·
                    refine ⟨2195294111780353102438169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5854117631414274939835117 2195294111780353102438169)
                    ·
                      refine ⟨1646470583835264826828627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2195294111780353102438169 1646470583835264826828627)
                      ·
                        rfl

theorem cell23_3206490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 4, 2, 2, 3, 2].length) (baseStart_3206490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206490 prefixEnd_3206490 := by exact prefixLift 3206490
  have htrace : WordTrace (prefixWord ++ tailWord_3206490) baseStart_3206490 baseEnd_3206490 := by
    simpa [prefixWord, tailWord_3206490, baseEnd_3206490] using wordTrace_append hprefix tailTrace_3206490
  have hstable : (prefixWord ++ tailWord_3206490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206490).length < 2 ^ (prefixWord ++ tailWord_3206490).sum := by decide
  have hdescent : baseEnd_3206490 < baseStart_3206490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206523 : List Nat := [1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 3]
def baseStart_3206523 : Nat := 118140960795 + 3206523 * 2 ^ 59
def prefixEnd_3206523 : Nat := 4983230072969 + 3 ^ 40 * 3206523 * 2
def baseEnd_3206523 : Nat := 1646487528696863197715975

theorem tailTrace_3206523 : CollatzResearch.WordTrace tailWord_3206523 prefixEnd_3206523 1646487528696863197715975 := by
  unfold tailWord_3206523
  simp only [CollatzResearch.WordTrace]
  refine ⟨116951501762322276374416223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77967667841548184249610815 116951501762322276374416223)
  ·
    refine ⟨175427252643483414561624335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116951501762322276374416223 175427252643483414561624335)
    ·
      refine ⟨263140878965225121842436503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175427252643483414561624335 263140878965225121842436503)
      ·
        refine ⟨394711318447837682763654755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263140878965225121842436503 394711318447837682763654755)
        ·
          refine ⟨592066977671756524145482133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 394711318447837682763654755 592066977671756524145482133)
          ·
            refine ⟨27753139578363587069319475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 592066977671756524145482133 27753139578363587069319475)
            ·
              refine ⟨41629709367545380603979213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27753139578363587069319475 41629709367545380603979213)
              ·
                refine ⟨15611141012829517726492205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41629709367545380603979213 15611141012829517726492205)
                ·
                  refine ⟨5854177879811069147434577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15611141012829517726492205 5854177879811069147434577)
                  ·
                    refine ⟨4390633409858301860575933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5854177879811069147434577 4390633409858301860575933)
                    ·
                      refine ⟨1646487528696863197715975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4390633409858301860575933 1646487528696863197715975)
                      ·
                        rfl

theorem cell23_3206523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 3, 3, 2, 3].length) (baseStart_3206523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206523 prefixEnd_3206523 := by exact prefixLift 3206523
  have htrace : WordTrace (prefixWord ++ tailWord_3206523) baseStart_3206523 baseEnd_3206523 := by
    simpa [prefixWord, tailWord_3206523, baseEnd_3206523] using wordTrace_append hprefix tailTrace_3206523
  have hstable : (prefixWord ++ tailWord_3206523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206523).length < 2 ^ (prefixWord ++ tailWord_3206523).sum := by decide
  have hdescent : baseEnd_3206523 < baseStart_3206523 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206533 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 1, 2, 4]
def baseStart_3206533 : Nat := 118140960795 + 3206533 * 2 ^ 59
def prefixEnd_3206533 : Nat := 4983230072969 + 3 ^ 40 * 3206533 * 2
def baseEnd_3206533 : Nat := 1646492663503408158590929

theorem tailTrace_3206533 : CollatzResearch.WordTrace tailWord_3206533 prefixEnd_3206533 1646492663503408158590929 := by
  unfold tailWord_3206533
  simp only [CollatzResearch.WordTrace]
  refine ⟨116951866492286048082280253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77967910994857365388186835 116951866492286048082280253)
  ·
    refine ⟨43856949934607268030855095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116951866492286048082280253 43856949934607268030855095)
    ·
      refine ⟨65785424901910902046282643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43856949934607268030855095 65785424901910902046282643)
      ·
        refine ⟨98678137352866353069423965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65785424901910902046282643 98678137352866353069423965)
        ·
          refine ⟨37004301507324882401033987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98678137352866353069423965 37004301507324882401033987)
          ·
            refine ⟨55506452260987323601550981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37004301507324882401033987 55506452260987323601550981)
            ·
              refine ⟨10407459798935123175290809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55506452260987323601550981 10407459798935123175290809)
              ·
                refine ⟨7805594849201342381468107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10407459798935123175290809 7805594849201342381468107)
                ·
                  refine ⟨11708392273802013572202161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7805594849201342381468107 11708392273802013572202161)
                  ·
                    refine ⟨8781294205351510179151621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11708392273802013572202161 8781294205351510179151621)
                    ·
                      refine ⟨1646492663503408158590929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8781294205351510179151621 1646492663503408158590929)
                      ·
                        rfl

theorem cell23_3206533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 1, 2, 4].length) (baseStart_3206533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206533 prefixEnd_3206533 := by exact prefixLift 3206533
  have htrace : WordTrace (prefixWord ++ tailWord_3206533) baseStart_3206533 baseEnd_3206533 := by
    simpa [prefixWord, tailWord_3206533, baseEnd_3206533] using wordTrace_append hprefix tailTrace_3206533
  have hstable : (prefixWord ++ tailWord_3206533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206533).length < 2 ^ (prefixWord ++ tailWord_3206533).sum := by decide
  have hdescent : baseEnd_3206533 < baseStart_3206533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206540 : List Nat := [2, 2, 1, 2, 1, 3, 3, 3, 1, 2, 3]
def baseStart_3206540 : Nat := 118140960795 + 3206540 * 2 ^ 59
def prefixEnd_3206540 : Nat := 4983230072969 + 3 ^ 40 * 3206540 * 2
def baseEnd_3206540 : Nat := 1646496257867989631203397

theorem tailTrace_3206540 : CollatzResearch.WordTrace tailWord_3206540 prefixEnd_3206540 1646496257867989631203397 := by
  unfold tailWord_3206540
  simp only [CollatzResearch.WordTrace]
  refine ⟨58476060901630344138892537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77968081202173792185190049 58476060901630344138892537)
  ·
    refine ⟨43857045676222758104169403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58476060901630344138892537 43857045676222758104169403)
    ·
      refine ⟨65785568514334137156254105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43857045676222758104169403 65785568514334137156254105)
      ·
        refine ⟨49339176385750602867190579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65785568514334137156254105 49339176385750602867190579)
        ·
          refine ⟨74008764578625904300785869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49339176385750602867190579 74008764578625904300785869)
          ·
            refine ⟨27753286716984714112794701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74008764578625904300785869 27753286716984714112794701)
            ·
              refine ⟨10407482518869267792298013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27753286716984714112794701 10407482518869267792298013)
              ·
                refine ⟨3902805944575975422111755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10407482518869267792298013 3902805944575975422111755)
                ·
                  refine ⟨5854208916863963133167633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3902805944575975422111755 5854208916863963133167633)
                  ·
                    refine ⟨4390656687647972349875725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5854208916863963133167633 4390656687647972349875725)
                    ·
                      refine ⟨1646496257867989631203397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4390656687647972349875725 1646496257867989631203397)
                      ·
                        rfl

theorem cell23_3206540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_3206540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206540 prefixEnd_3206540 := by exact prefixLift 3206540
  have htrace : WordTrace (prefixWord ++ tailWord_3206540) baseStart_3206540 baseEnd_3206540 := by
    simpa [prefixWord, tailWord_3206540, baseEnd_3206540] using wordTrace_append hprefix tailTrace_3206540
  have hstable : (prefixWord ++ tailWord_3206540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206540).length < 2 ^ (prefixWord ++ tailWord_3206540).sum := by decide
  have hdescent : baseEnd_3206540 < baseStart_3206540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206554 : List Nat := [3, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2]
def baseStart_3206554 : Nat := 118140960795 + 3206554 * 2 ^ 59
def prefixEnd_3206554 : Nat := 4983230072969 + 3 ^ 40 * 3206554 * 2
def baseEnd_3206554 : Nat := 1646503446597152576428333

theorem tailTrace_3206554 : CollatzResearch.WordTrace tailWord_3206554 prefixEnd_3206554 1646503446597152576428333 := by
  unfold tailWord_3206554
  simp only [CollatzResearch.WordTrace]
  refine ⟨29238158106302492167198679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77968421616806645779196477 29238158106302492167198679)
  ·
    refine ⟨43857237159453738250798019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29238158106302492167198679 43857237159453738250798019)
    ·
      refine ⟨65785855739180607376197029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43857237159453738250798019 65785855739180607376197029)
      ·
        refine ⟨12334847951096363883036943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65785855739180607376197029 12334847951096363883036943)
        ·
          refine ⟨18502271926644545824555415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12334847951096363883036943 18502271926644545824555415)
          ·
            refine ⟨27753407889966818736833123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18502271926644545824555415 27753407889966818736833123)
            ·
              refine ⟨41630111834950228105249685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27753407889966818736833123 41630111834950228105249685)
              ·
                refine ⟨1951411492263291942433579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41630111834950228105249685 1951411492263291942433579)
                ·
                  refine ⟨2927117238394937913650369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951411492263291942433579 2927117238394937913650369)
                  ·
                    refine ⟨2195337928796203435237777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2927117238394937913650369 2195337928796203435237777)
                    ·
                      refine ⟨1646503446597152576428333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2195337928796203435237777 1646503446597152576428333)
                      ·
                        rfl

theorem cell23_3206554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_3206554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206554 prefixEnd_3206554 := by exact prefixLift 3206554
  have htrace : WordTrace (prefixWord ++ tailWord_3206554) baseStart_3206554 baseEnd_3206554 := by
    simpa [prefixWord, tailWord_3206554, baseEnd_3206554] using wordTrace_append hprefix tailTrace_3206554
  have hstable : (prefixWord ++ tailWord_3206554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206554).length < 2 ^ (prefixWord ++ tailWord_3206554).sum := by decide
  have hdescent : baseEnd_3206554 < baseStart_3206554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206576 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 8]
def baseStart_3206576 : Nat := 118140960795 + 3206576 * 2 ^ 59
def prefixEnd_3206576 : Nat := 4983230072969 + 3 ^ 40 * 3206576 * 2
def baseEnd_3206576 : Nat := 1646514743171551490353231

theorem tailTrace_3206576 : CollatzResearch.WordTrace tailWord_3206576 prefixEnd_3206576 1646514743171551490353231 := by
  unfold tailWord_3206576
  simp only [CollatzResearch.WordTrace]
  refine ⟨58476717415565133213047791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77968956554086844284063721 58476717415565133213047791)
  ·
    refine ⟨87715076123347699819571687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58476717415565133213047791 87715076123347699819571687)
    ·
      refine ⟨131572614185021549729357531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87715076123347699819571687 131572614185021549729357531)
      ·
        refine ⟨197358921277532324594036297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131572614185021549729357531 197358921277532324594036297)
        ·
          refine ⟨148019190958149243445527223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197358921277532324594036297 148019190958149243445527223)
          ·
            refine ⟨222028786437223865168290835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148019190958149243445527223 222028786437223865168290835)
            ·
              refine ⟨333043179655835797752436253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222028786437223865168290835 333043179655835797752436253)
              ·
                refine ⟨124891192370938424157163595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 333043179655835797752436253 124891192370938424157163595)
                ·
                  refine ⟨187336788556407636235745393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124891192370938424157163595 187336788556407636235745393)
                  ·
                    refine ⟨140502591417305727176809045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 187336788556407636235745393 140502591417305727176809045)
                    ·
                      refine ⟨1646514743171551490353231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 140502591417305727176809045 1646514743171551490353231)
                      ·
                        rfl

theorem cell23_3206576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 8].length) (baseStart_3206576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206576 prefixEnd_3206576 := by exact prefixLift 3206576
  have htrace : WordTrace (prefixWord ++ tailWord_3206576) baseStart_3206576 baseEnd_3206576 := by
    simpa [prefixWord, tailWord_3206576, baseEnd_3206576] using wordTrace_append hprefix tailTrace_3206576
  have hstable : (prefixWord ++ tailWord_3206576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206576).length < 2 ^ (prefixWord ++ tailWord_3206576).sum := by decide
  have hdescent : baseEnd_3206576 < baseStart_3206576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206588 : List Nat := [2, 2, 2, 4, 2, 2, 1, 3, 1, 2, 2]
def baseStart_3206588 : Nat := 118140960795 + 3206588 * 2 ^ 59
def prefixEnd_3206588 : Nat := 4983230072969 + 3 ^ 40 * 3206588 * 2
def baseEnd_3206588 : Nat := 1646520904939405443403177

theorem tailTrace_3206588 : CollatzResearch.WordTrace tailWord_3206588 prefixEnd_3206588 1646520904939405443403177 := by
  unfold tailWord_3206588
  simp only [CollatzResearch.WordTrace]
  refine ⟨58476936253543396237766209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77969248338057861650354945 58476936253543396237766209)
  ·
    refine ⟨43857702190157547178324657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58476936253543396237766209 43857702190157547178324657)
    ·
      refine ⟨32893276642618160383743493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43857702190157547178324657 32893276642618160383743493)
      ·
        refine ⟨6167489370490905071951905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32893276642618160383743493 6167489370490905071951905)
        ·
          refine ⟨4625617027868178803963929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6167489370490905071951905 4625617027868178803963929)
          ·
            refine ⟨3469212770901134102972947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4625617027868178803963929 3469212770901134102972947)
            ·
              refine ⟨5203819156351701154459421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3469212770901134102972947 5203819156351701154459421)
              ·
                refine ⟨1951432183631887932922283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5203819156351701154459421 1951432183631887932922283)
                ·
                  refine ⟨2927148275447831899383425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951432183631887932922283 2927148275447831899383425)
                  ·
                    refine ⟨2195361206585873924537569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2927148275447831899383425 2195361206585873924537569)
                    ·
                      refine ⟨1646520904939405443403177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2195361206585873924537569 1646520904939405443403177)
                      ·
                        rfl

theorem cell23_3206588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_3206588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206588 prefixEnd_3206588 := by exact prefixLift 3206588
  have htrace : WordTrace (prefixWord ++ tailWord_3206588) baseStart_3206588 baseEnd_3206588 := by
    simpa [prefixWord, tailWord_3206588, baseEnd_3206588] using wordTrace_append hprefix tailTrace_3206588
  have hstable : (prefixWord ++ tailWord_3206588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206588).length < 2 ^ (prefixWord ++ tailWord_3206588).sum := by decide
  have hdescent : baseEnd_3206588 < baseStart_3206588 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206613 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 5]
def baseStart_3206613 : Nat := 118140960795 + 3206613 * 2 ^ 59
def prefixEnd_3206613 : Nat := 4983230072969 + 3 ^ 40 * 3206613 * 2
def baseEnd_3206613 : Nat := 1646533741955767845590561

theorem tailTrace_3206613 : CollatzResearch.WordTrace tailWord_3206613 prefixEnd_3206613 1646533741955767845590561 := by
  unfold tailWord_3206613
  simp only [CollatzResearch.WordTrace]
  refine ⟨116954784331996221745192493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77969856221330814496794995 116954784331996221745192493)
  ·
    refine ⟨43858044124498583154447185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 116954784331996221745192493 43858044124498583154447185)
    ·
      refine ⟨32893533093373937365835389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43858044124498583154447185 32893533093373937365835389)
      ·
        refine ⟨12335074910015226512188271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32893533093373937365835389 12335074910015226512188271)
        ·
          refine ⟨18502612365022839768282407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12335074910015226512188271 18502612365022839768282407)
          ·
            refine ⟨27753918547534259652423611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18502612365022839768282407 27753918547534259652423611)
            ·
              refine ⟨41630877821301389478635417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27753918547534259652423611 41630877821301389478635417)
              ·
                refine ⟨31223158365976042108976563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41630877821301389478635417 31223158365976042108976563)
                ·
                  refine ⟨46834737548964063163464845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31223158365976042108976563 46834737548964063163464845)
                  ·
                    refine ⟨17563026580861523686299317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46834737548964063163464845 17563026580861523686299317)
                    ·
                      refine ⟨1646533741955767845590561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17563026580861523686299317 1646533741955767845590561)
                      ·
                        rfl

theorem cell23_3206613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_3206613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206613 prefixEnd_3206613 := by exact prefixLift 3206613
  have htrace : WordTrace (prefixWord ++ tailWord_3206613) baseStart_3206613 baseEnd_3206613 := by
    simpa [prefixWord, tailWord_3206613, baseEnd_3206613] using wordTrace_append hprefix tailTrace_3206613
  have hstable : (prefixWord ++ tailWord_3206613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206613).length < 2 ^ (prefixWord ++ tailWord_3206613).sum := by decide
  have hdescent : baseEnd_3206613 < baseStart_3206613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206621 : List Nat := [1, 4, 3, 1, 1, 4, 2, 1, 2, 1, 3]
def baseStart_3206621 : Nat := 118140960795 + 3206621 * 2 ^ 59
def prefixEnd_3206621 : Nat := 4983230072969 + 3 ^ 40 * 3206621 * 2
def baseEnd_3206621 : Nat := 1646537849801003814290525

theorem tailTrace_3206621 : CollatzResearch.WordTrace tailWord_3206621 prefixEnd_3206621 1646537849801003814290525 := by
  unfold tailWord_3206621
  simp only [CollatzResearch.WordTrace]
  refine ⟨116955076115967239111483717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77970050743978159407655811 116955076115967239111483717)
  ·
    refine ⟨21929076771743857333403197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 116955076115967239111483717 21929076771743857333403197)
    ·
      refine ⟨8223403789403946500026199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21929076771743857333403197 8223403789403946500026199)
      ·
        refine ⟨12335105684105919750039299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8223403789403946500026199 12335105684105919750039299)
        ·
          refine ⟨18502658526158879625058949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12335105684105919750039299 18502658526158879625058949)
          ·
            refine ⟨3469248473654789929698553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18502658526158879625058949 3469248473654789929698553)
            ·
              refine ⟨2601936355241092447273915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3469248473654789929698553 2601936355241092447273915)
              ·
                refine ⟨3902904532861638670910873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2601936355241092447273915 3902904532861638670910873)
                ·
                  refine ⟨2927178399646229003183155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3902904532861638670910873 2927178399646229003183155)
                  ·
                    refine ⟨4390767599469343504774733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2927178399646229003183155 4390767599469343504774733)
                    ·
                      refine ⟨1646537849801003814290525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4390767599469343504774733 1646537849801003814290525)
                      ·
                        rfl

theorem cell23_3206621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 1, 2, 1, 3].length) (baseStart_3206621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206621 prefixEnd_3206621 := by exact prefixLift 3206621
  have htrace : WordTrace (prefixWord ++ tailWord_3206621) baseStart_3206621 baseEnd_3206621 := by
    simpa [prefixWord, tailWord_3206621, baseEnd_3206621] using wordTrace_append hprefix tailTrace_3206621
  have hstable : (prefixWord ++ tailWord_3206621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206621).length < 2 ^ (prefixWord ++ tailWord_3206621).sum := by decide
  have hdescent : baseEnd_3206621 < baseStart_3206621 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206623 : List Nat := [1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 4]
def baseStart_3206623 : Nat := 118140960795 + 3206623 * 2 ^ 59
def prefixEnd_3206623 : Nat := 4983230072969 + 3 ^ 40 * 3206623 * 2
def baseEnd_3206623 : Nat := 1646538876762312806465515

theorem tailTrace_3206623 : CollatzResearch.WordTrace tailWord_3206623 prefixEnd_3206623 1646538876762312806465515 := by
  unfold tailWord_3206623
  simp only [CollatzResearch.WordTrace]
  refine ⟨116955149061959993453056523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77970099374639995635371015 116955149061959993453056523)
  ·
    refine ⟨175432723592939990179584785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116955149061959993453056523 175432723592939990179584785)
    ·
      refine ⟨131574542694704992634688589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175432723592939990179584785 131574542694704992634688589)
      ·
        refine ⟨49340453510514372238008221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131574542694704992634688589 49340453510514372238008221)
        ·
          refine ⟨18502670066442889589253083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49340453510514372238008221 18502670066442889589253083)
          ·
            refine ⟨27754005099664334383879625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18502670066442889589253083 27754005099664334383879625)
            ·
              refine ⟨20815503824748250787909719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27754005099664334383879625 20815503824748250787909719)
              ·
                refine ⟨31223255737122376181864579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20815503824748250787909719 31223255737122376181864579)
                ·
                  refine ⟨46834883605683564272796869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31223255737122376181864579 46834883605683564272796869)
                  ·
                    refine ⟨8781540676065668301149413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46834883605683564272796869 8781540676065668301149413)
                    ·
                      refine ⟨1646538876762312806465515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8781540676065668301149413 1646538876762312806465515)
                      ·
                        rfl

theorem cell23_3206623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 1, 1, 4, 4].length) (baseStart_3206623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206623 prefixEnd_3206623 := by exact prefixLift 3206623
  have htrace : WordTrace (prefixWord ++ tailWord_3206623) baseStart_3206623 baseEnd_3206623 := by
    simpa [prefixWord, tailWord_3206623, baseEnd_3206623] using wordTrace_append hprefix tailTrace_3206623
  have hstable : (prefixWord ++ tailWord_3206623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206623).length < 2 ^ (prefixWord ++ tailWord_3206623).sum := by decide
  have hdescent : baseEnd_3206623 < baseStart_3206623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206643 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 3]
def baseStart_3206643 : Nat := 118140960795 + 3206643 * 2 ^ 59
def prefixEnd_3206643 : Nat := 4983230072969 + 3 ^ 40 * 3206643 * 2
def baseEnd_3206643 : Nat := 1646549146375402728215423

theorem tailTrace_3206643 : CollatzResearch.WordTrace tailWord_3206643 prefixEnd_3206643 1646549146375402728215423 := by
  unfold tailWord_3206643
  simp only [CollatzResearch.WordTrace]
  refine ⟨116955878521887536868784583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77970585681258357912523055 116955878521887536868784583)
  ·
    refine ⟨175433817782831305303176875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116955878521887536868784583 175433817782831305303176875)
    ·
      refine ⟨263150726674246957954765313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175433817782831305303176875 263150726674246957954765313)
      ·
        refine ⟨197363045005685218466073985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263150726674246957954765313 197363045005685218466073985)
        ·
          refine ⟨148022283754263913849555489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197363045005685218466073985 148022283754263913849555489)
          ·
            refine ⟨111016712815697935387166617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148022283754263913849555489 111016712815697935387166617)
            ·
              refine ⟨83262534611773451540374963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111016712815697935387166617 83262534611773451540374963)
              ·
                refine ⟨124893801917660177310562445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83262534611773451540374963 124893801917660177310562445)
                ·
                  refine ⟨46835175719122566491460917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124893801917660177310562445 46835175719122566491460917)
                  ·
                    refine ⟨4390797723667740608574461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46835175719122566491460917 4390797723667740608574461)
                    ·
                      refine ⟨1646549146375402728215423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4390797723667740608574461 1646549146375402728215423)
                      ·
                        rfl

theorem cell23_3206643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 3, 5, 3].length) (baseStart_3206643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206643 prefixEnd_3206643 := by exact prefixLift 3206643
  have htrace : WordTrace (prefixWord ++ tailWord_3206643) baseStart_3206643 baseEnd_3206643 := by
    simpa [prefixWord, tailWord_3206643, baseEnd_3206643] using wordTrace_append hprefix tailTrace_3206643
  have hstable : (prefixWord ++ tailWord_3206643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206643).length < 2 ^ (prefixWord ++ tailWord_3206643).sum := by decide
  have hdescent : baseEnd_3206643 < baseStart_3206643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206650 : List Nat := [3, 1, 1, 1, 1, 2, 4, 5, 5]
def baseStart_3206650 : Nat := 118140960795 + 3206650 * 2 ^ 59
def prefixEnd_3206650 : Nat := 4983230072969 + 3 ^ 40 * 3206650 * 2
def baseEnd_3206650 : Nat := 182950304526664911203099

theorem tailTrace_3206650 : CollatzResearch.WordTrace tailWord_3206650 prefixEnd_3206650 182950304526664911203099 := by
  unfold tailWord_3206650
  simp only [CollatzResearch.WordTrace]
  refine ⟨29239033458215544266072351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77970755888574784709526269 29239033458215544266072351)
  ·
    refine ⟨43858550187323316399108527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29239033458215544266072351 43858550187323316399108527)
    ·
      refine ⟨65787825280984974598662791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43858550187323316399108527 65787825280984974598662791)
      ·
        refine ⟨98681737921477461897994187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65787825280984974598662791 98681737921477461897994187)
        ·
          refine ⟨148022606882216192846991281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98681737921477461897994187 148022606882216192846991281)
          ·
            refine ⟨111016955161662144635243461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148022606882216192846991281 111016955161662144635243461)
            ·
              refine ⟨20815679092811652119108149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111016955161662144635243461 20815679092811652119108149)
              ·
                refine ⟨1951469914951092386166389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20815679092811652119108149 1951469914951092386166389)
                ·
                  refine ⟨182950304526664911203099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1951469914951092386166389 182950304526664911203099)
                  ·
                    rfl

theorem cell23_3206650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 5, 5].length) (baseStart_3206650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206650 prefixEnd_3206650 := by exact prefixLift 3206650
  have htrace : WordTrace (prefixWord ++ tailWord_3206650) baseStart_3206650 baseEnd_3206650 := by
    simpa [prefixWord, tailWord_3206650, baseEnd_3206650] using wordTrace_append hprefix tailTrace_3206650
  have hstable : (prefixWord ++ tailWord_3206650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206650).length < 2 ^ (prefixWord ++ tailWord_3206650).sum := by decide
  have hdescent : baseEnd_3206650 < baseStart_3206650 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206667 : List Nat := [1, 1, 1, 1, 8, 1, 1, 4, 5]
def baseStart_3206667 : Nat := 118140960795 + 3206667 * 2 ^ 59
def prefixEnd_3206667 : Nat := 4983230072969 + 3 ^ 40 * 3206667 * 2
def baseEnd_3206667 : Nat := 182951274434567848257257

theorem tailTrace_3206667 : CollatzResearch.WordTrace tailWord_3206667 prefixEnd_3206667 182951274434567848257257 := by
  unfold tailWord_3206667
  simp only [CollatzResearch.WordTrace]
  refine ⟨116956753873800588967658255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77971169249200392645105503 116956753873800588967658255)
  ·
    refine ⟨175435130810700883451487383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116956753873800588967658255 175435130810700883451487383)
    ·
      refine ⟨263152696216051325177231075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175435130810700883451487383 263152696216051325177231075)
      ·
        refine ⟨394729044324076987765846613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263152696216051325177231075 394729044324076987765846613)
        ·
          refine ⟨4625730988172777200381015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 394729044324076987765846613 4625730988172777200381015)
          ·
            refine ⟨6938596482259165800571523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4625730988172777200381015 6938596482259165800571523)
            ·
              refine ⟨10407894723388748700857285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6938596482259165800571523 10407894723388748700857285)
              ·
                refine ⟨1951480260635390381410741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10407894723388748700857285 1951480260635390381410741)
                ·
                  refine ⟨182951274434567848257257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1951480260635390381410741 182951274434567848257257)
                  ·
                    rfl

theorem cell23_3206667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 4, 5].length) (baseStart_3206667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206667 prefixEnd_3206667 := by exact prefixLift 3206667
  have htrace : WordTrace (prefixWord ++ tailWord_3206667) baseStart_3206667 baseEnd_3206667 := by
    simpa [prefixWord, tailWord_3206667, baseEnd_3206667] using wordTrace_append hprefix tailTrace_3206667
  have hstable : (prefixWord ++ tailWord_3206667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206667).length < 2 ^ (prefixWord ++ tailWord_3206667).sum := by decide
  have hdescent : baseEnd_3206667 < baseStart_3206667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206673 : List Nat := [1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 5]
def baseStart_3206673 : Nat := 118140960795 + 3206673 * 2 ^ 59
def prefixEnd_3206673 : Nat := 4983230072969 + 3 ^ 40 * 3206673 * 2
def baseEnd_3206673 : Nat := 1646564550795037610840285

theorem tailTrace_3206673 : CollatzResearch.WordTrace tailWord_3206673 prefixEnd_3206673 1646564550795037610840285 := by
  unfold tailWord_3206673
  simp only [CollatzResearch.WordTrace]
  refine ⟨116956972711778851992376673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77971315141185901328251115 116956972711778851992376673)
  ·
    refine ⟨87717729533834138994282505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116956972711778851992376673 87717729533834138994282505)
    ·
      refine ⟨65788297150375604245711879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87717729533834138994282505 65788297150375604245711879)
      ·
        refine ⟨98682445725563406368567819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65788297150375604245711879 98682445725563406368567819)
        ·
          refine ⟨148023668588345109552851729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98682445725563406368567819 148023668588345109552851729)
          ·
            refine ⟨111017751441258832164638797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148023668588345109552851729 111017751441258832164638797)
            ·
              refine ⟨41631656790472062061739549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111017751441258832164638797 41631656790472062061739549)
              ·
                refine ⟨15611871296427023273152331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 41631656790472062061739549 15611871296427023273152331)
                ·
                  refine ⟨23417806944640534909728497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15611871296427023273152331 23417806944640534909728497)
                  ·
                    refine ⟨17563355208480401182296373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23417806944640534909728497 17563355208480401182296373)
                    ·
                      refine ⟨1646564550795037610840285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17563355208480401182296373 1646564550795037610840285)
                      ·
                        rfl

theorem cell23_3206673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 5].length) (baseStart_3206673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206673 prefixEnd_3206673 := by exact prefixLift 3206673
  have htrace : WordTrace (prefixWord ++ tailWord_3206673) baseStart_3206673 baseEnd_3206673 := by
    simpa [prefixWord, tailWord_3206673, baseEnd_3206673] using wordTrace_append hprefix tailTrace_3206673
  have hstable : (prefixWord ++ tailWord_3206673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206673).length < 2 ^ (prefixWord ++ tailWord_3206673).sum := by decide
  have hdescent : baseEnd_3206673 < baseStart_3206673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206720 : List Nat := [2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 3]
def baseStart_3206720 : Nat := 118140960795 + 3206720 * 2 ^ 59
def prefixEnd_3206720 : Nat := 4983230072969 + 3 ^ 40 * 3206720 * 2
def baseEnd_3206720 : Nat := 1646588684385798926952569

theorem tailTrace_3206720 : CollatzResearch.WordTrace tailWord_3206720 prefixEnd_3206720 1646588684385798926952569 := by
  unfold tailWord_3206720
  simp only [CollatzResearch.WordTrace]
  refine ⟨58479343471304289509668807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77972457961739052679558409 58479343471304289509668807)
  ·
    refine ⟨87719015206956434264503211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58479343471304289509668807 87719015206956434264503211)
    ·
      refine ⟨131578522810434651396754817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87719015206956434264503211 131578522810434651396754817)
      ·
        refine ⟨98683892107825988547566113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131578522810434651396754817 98683892107825988547566113)
        ·
          refine ⟨74012919080869491410674585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98683892107825988547566113 74012919080869491410674585)
          ·
            refine ⟨55509689310652118558005939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74012919080869491410674585 55509689310652118558005939)
            ·
              refine ⟨83264533965978177837008909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55509689310652118558005939 83264533965978177837008909)
              ·
                refine ⟨31224200237241816688878341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 83264533965978177837008909 31224200237241816688878341)
                ·
                  refine ⟨5854537544482840629164689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31224200237241816688878341 5854537544482840629164689)
                  ·
                    refine ⟨4390903158362130471873517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5854537544482840629164689 4390903158362130471873517)
                    ·
                      refine ⟨1646588684385798926952569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4390903158362130471873517 1646588684385798926952569)
                      ·
                        rfl

theorem cell23_3206720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 3, 4, 2, 3].length) (baseStart_3206720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206720 prefixEnd_3206720 := by exact prefixLift 3206720
  have htrace : WordTrace (prefixWord ++ tailWord_3206720) baseStart_3206720 baseEnd_3206720 := by
    simpa [prefixWord, tailWord_3206720, baseEnd_3206720] using wordTrace_append hprefix tailTrace_3206720
  have hstable : (prefixWord ++ tailWord_3206720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206720).length < 2 ^ (prefixWord ++ tailWord_3206720).sum := by decide
  have hdescent : baseEnd_3206720 < baseStart_3206720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206763 : List Nat := [1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 7]
def baseStart_3206763 : Nat := 118140960795 + 3206763 * 2 ^ 59
def prefixEnd_3206763 : Nat := 4983230072969 + 3 ^ 40 * 3206763 * 2
def baseEnd_3206763 : Nat := 1646610764053942258714871

theorem tailTrace_3206763 : CollatzResearch.WordTrace tailWord_3206763 prefixEnd_3206763 1646610764053942258714871 := by
  unfold tailWord_3206763
  simp only [CollatzResearch.WordTrace]
  refine ⟨116960255281452797363152943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77973503520968531575435295 116960255281452797363152943)
  ·
    refine ⟨175440382922179196044729415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116960255281452797363152943 175440382922179196044729415)
    ·
      refine ⟨263160574383268794067094123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175440382922179196044729415 263160574383268794067094123)
      ·
        refine ⟨394740861574903191100641185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263160574383268794067094123 394740861574903191100641185)
        ·
          refine ⟨296055646181177393325480889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 394740861574903191100641185 296055646181177393325480889)
          ·
            refine ⟨222041734635883044994110667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296055646181177393325480889 222041734635883044994110667)
            ·
              refine ⟨333062601953824567491166001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222041734635883044994110667 333062601953824567491166001)
              ·
                refine ⟨249796951465368425618374501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333062601953824567491166001 249796951465368425618374501)
                ·
                  refine ⟨46836928399756579803445219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 249796951465368425618374501 46836928399756579803445219)
                  ·
                    refine ⟨70255392599634869705167829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46836928399756579803445219 70255392599634869705167829)
                    ·
                      refine ⟨1646610764053942258714871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 70255392599634869705167829 1646610764053942258714871)
                      ·
                        rfl

theorem cell23_3206763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_3206763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206763 prefixEnd_3206763 := by exact prefixLift 3206763
  have htrace : WordTrace (prefixWord ++ tailWord_3206763) baseStart_3206763 baseEnd_3206763 := by
    simpa [prefixWord, tailWord_3206763, baseEnd_3206763] using wordTrace_append hprefix tailTrace_3206763
  have hstable : (prefixWord ++ tailWord_3206763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206763).length < 2 ^ (prefixWord ++ tailWord_3206763).sum := by decide
  have hdescent : baseEnd_3206763 < baseStart_3206763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206804 : List Nat := [2, 4, 2, 2, 2, 1, 1, 1, 3, 5]
def baseStart_3206804 : Nat := 118140960795 + 3206804 * 2 ^ 59
def prefixEnd_3206804 : Nat := 4983230072969 + 3 ^ 40 * 3206804 * 2
def baseEnd_3206804 : Nat := 548877272253592199434061

theorem tailTrace_3206804 : CollatzResearch.WordTrace tailWord_3206804 prefixEnd_3206804 548877272253592199434061 := by
  unfold tailWord_3206804
  simp only [CollatzResearch.WordTrace]
  refine ⟨58480875337152130682697733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77974500449536174243596977 58480875337152130682697733)
  ·
    refine ⟨10965164125716024503005825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58480875337152130682697733 10965164125716024503005825)
    ·
      refine ⟨8223873094287018377254369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10965164125716024503005825 8223873094287018377254369)
      ·
        refine ⟨6167904820715263782940777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8223873094287018377254369 6167904820715263782940777)
        ·
          refine ⟨4625928615536447837205583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6167904820715263782940777 4625928615536447837205583)
          ·
            refine ⟨6938892923304671755808375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4625928615536447837205583 6938892923304671755808375)
            ·
              refine ⟨10408339384957007633712563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6938892923304671755808375 10408339384957007633712563)
              ·
                refine ⟨15612509077435511450568845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10408339384957007633712563 15612509077435511450568845)
                ·
                  refine ⟨5854690904038316793963317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15612509077435511450568845 5854690904038316793963317)
                  ·
                    refine ⟨548877272253592199434061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5854690904038316793963317 548877272253592199434061)
                    ·
                      rfl

theorem cell23_3206804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_3206804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206804 prefixEnd_3206804 := by exact prefixLift 3206804
  have htrace : WordTrace (prefixWord ++ tailWord_3206804) baseStart_3206804 baseEnd_3206804 := by
    simpa [prefixWord, tailWord_3206804, baseEnd_3206804] using wordTrace_append hprefix tailTrace_3206804
  have hstable : (prefixWord ++ tailWord_3206804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206804).length < 2 ^ (prefixWord ++ tailWord_3206804).sum := by decide
  have hdescent : baseEnd_3206804 < baseStart_3206804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206807 : List Nat := [1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 4]
def baseStart_3206807 : Nat := 118140960795 + 3206807 * 2 ^ 59
def prefixEnd_3206807 : Nat := 4983230072969 + 3 ^ 40 * 3206807 * 2
def baseEnd_3206807 : Nat := 1646633357202740086564669

theorem tailTrace_3206807 : CollatzResearch.WordTrace tailWord_3206807 prefixEnd_3206807 1646633357202740086564669 := by
  unfold tailWord_3206807
  simp only [CollatzResearch.WordTrace]
  refine ⟨116961860093293392877754675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77974573395528928585169783 116961860093293392877754675)
  ·
    refine ⟨175442790139940089316632013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116961860093293392877754675 175442790139940089316632013)
    ·
      refine ⟨65791046302477533493737005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175442790139940089316632013 65791046302477533493737005)
      ·
        refine ⟨24671642363429075060151377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65791046302477533493737005 24671642363429075060151377)
        ·
          refine ⟨18503731772571806295113533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24671642363429075060151377 18503731772571806295113533)
          ·
            refine ⟨6938899414714427360667575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18503731772571806295113533 6938899414714427360667575)
            ·
              refine ⟨10408349122071641041001363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6938899414714427360667575 10408349122071641041001363)
              ·
                refine ⟨15612523683107461561502045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10408349122071641041001363 15612523683107461561502045)
                ·
                  refine ⟨5854696381165298085563267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15612523683107461561502045 5854696381165298085563267)
                  ·
                    refine ⟨8782044571747947128344901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5854696381165298085563267 8782044571747947128344901)
                    ·
                      refine ⟨1646633357202740086564669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8782044571747947128344901 1646633357202740086564669)
                      ·
                        rfl

theorem cell23_3206807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_3206807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206807 prefixEnd_3206807 := by exact prefixLift 3206807
  have htrace : WordTrace (prefixWord ++ tailWord_3206807) baseStart_3206807 baseEnd_3206807 := by
    simpa [prefixWord, tailWord_3206807, baseEnd_3206807] using wordTrace_append hprefix tailTrace_3206807
  have hstable : (prefixWord ++ tailWord_3206807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206807).length < 2 ^ (prefixWord ++ tailWord_3206807).sum := by decide
  have hdescent : baseEnd_3206807 < baseStart_3206807 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206817 : List Nat := [1, 2, 3, 3, 2, 2, 1, 2, 1, 6]
def baseStart_3206817 : Nat := 118140960795 + 3206817 * 2 ^ 59
def prefixEnd_3206817 : Nat := 4983230072969 + 3 ^ 40 * 3206817 * 2
def baseEnd_3206817 : Nat := 548879497336428349146541

theorem tailTrace_3206817 : CollatzResearch.WordTrace tailWord_3206817 prefixEnd_3206817 548879497336428349146541 := by
  unfold tailWord_3206817
  simp only [CollatzResearch.WordTrace]
  refine ⟨116962224823257164585618705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77974816548838109723745803 116962224823257164585618705)
  ·
    refine ⟨87721668617442873439214029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116962224823257164585618705 87721668617442873439214029)
    ·
      refine ⟨32895625731541077539705261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87721668617442873439214029 32895625731541077539705261)
      ·
        refine ⟨12335859649327904077389473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32895625731541077539705261 12335859649327904077389473)
        ·
          refine ⟨9251894736995928058042105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12335859649327904077389473 9251894736995928058042105)
          ·
            refine ⟨6938921052746946043531579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9251894736995928058042105 6938921052746946043531579)
            ·
              refine ⟨10408381579120419065297369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6938921052746946043531579 10408381579120419065297369)
              ·
                refine ⟨7806286184340314298973027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10408381579120419065297369 7806286184340314298973027)
                ·
                  refine ⟨11709429276510471448459541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7806286184340314298973027 11709429276510471448459541)
                  ·
                    refine ⟨548879497336428349146541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11709429276510471448459541 548879497336428349146541)
                    ·
                      rfl

theorem cell23_3206817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 1, 2, 1, 6].length) (baseStart_3206817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206817 prefixEnd_3206817 := by exact prefixLift 3206817
  have htrace : WordTrace (prefixWord ++ tailWord_3206817) baseStart_3206817 baseEnd_3206817 := by
    simpa [prefixWord, tailWord_3206817, baseEnd_3206817] using wordTrace_append hprefix tailTrace_3206817
  have hstable : (prefixWord ++ tailWord_3206817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206817).length < 2 ^ (prefixWord ++ tailWord_3206817).sum := by decide
  have hdescent : baseEnd_3206817 < baseStart_3206817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206861 : List Nat := [1, 6, 2, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_3206861 : Nat := 118140960795 + 3206861 * 2 ^ 59
def prefixEnd_3206861 : Nat := 4983230072969 + 3 ^ 40 * 3206861 * 2
def baseEnd_3206861 : Nat := 1646661085158082875289421

theorem tailTrace_3206861 : CollatzResearch.WordTrace tailWord_3206861 prefixEnd_3206861 1646661085158082875289421 := by
  unfold tailWord_3206861
  simp only [CollatzResearch.WordTrace]
  refine ⟨116963829635097760100220437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77975886423398506733480291 116963829635097760100220437)
  ·
    refine ⟨5482679514145207504697833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 116963829635097760100220437 5482679514145207504697833)
    ·
      refine ⟨4112009635608905628523375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5482679514145207504697833 4112009635608905628523375)
      ·
        refine ⟨6168014453413358442785063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112009635608905628523375 6168014453413358442785063)
        ·
          refine ⟨9252021680120037664177595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6168014453413358442785063 9252021680120037664177595)
          ·
            refine ⟨13878032520180056496266393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9252021680120037664177595 13878032520180056496266393)
            ·
              refine ⟨10408524390135042372199795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13878032520180056496266393 10408524390135042372199795)
              ·
                refine ⟨15612786585202563558299693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10408524390135042372199795 15612786585202563558299693)
                ·
                  refine ⟨5854794969450961334362385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15612786585202563558299693 5854794969450961334362385)
                  ·
                    refine ⟨4391096227088221000771789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5854794969450961334362385 4391096227088221000771789)
                    ·
                      refine ⟨1646661085158082875289421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4391096227088221000771789 1646661085158082875289421)
                      ·
                        rfl

theorem cell23_3206861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_3206861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206861 prefixEnd_3206861 := by exact prefixLift 3206861
  have htrace : WordTrace (prefixWord ++ tailWord_3206861) baseStart_3206861 baseEnd_3206861 := by
    simpa [prefixWord, tailWord_3206861, baseEnd_3206861] using wordTrace_append hprefix tailTrace_3206861
  have hstable : (prefixWord ++ tailWord_3206861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206861).length < 2 ^ (prefixWord ++ tailWord_3206861).sum := by decide
  have hdescent : baseEnd_3206861 < baseStart_3206861 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206947 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 3]
def baseStart_3206947 : Nat := 118140960795 + 3206947 * 2 ^ 59
def prefixEnd_3206947 : Nat := 4983230072969 + 3 ^ 40 * 3206947 * 2
def baseEnd_3206947 : Nat := 1646705244494369538814025

theorem tailTrace_3206947 : CollatzResearch.WordTrace tailWord_3206947 prefixEnd_3206947 1646705244494369538814025 := by
  unfold tailWord_3206947
  simp only [CollatzResearch.WordTrace]
  refine ⟨116966966312786196787851095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77977977541857464525234063 116966966312786196787851095)
  ·
    refine ⟨175450449469179295181776643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116966966312786196787851095 175450449469179295181776643)
    ·
      refine ⟨263175674203768942772664965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175450449469179295181776643 263175674203768942772664965)
      ·
        refine ⟨49345438913206676769874681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263175674203768942772664965 49345438913206676769874681)
        ·
          refine ⟨37009079184905007577406011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49345438913206676769874681 37009079184905007577406011)
          ·
            refine ⟨55513618777357511366109017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37009079184905007577406011 55513618777357511366109017)
            ·
              refine ⟨41635214083018133524581763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55513618777357511366109017 41635214083018133524581763)
              ·
                refine ⟨62452821124527200286872645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41635214083018133524581763 62452821124527200286872645)
                ·
                  refine ⟨11709903960848850053788621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62452821124527200286872645 11709903960848850053788621)
                  ·
                    refine ⟨4391213985318318770170733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11709903960848850053788621 4391213985318318770170733)
                    ·
                      refine ⟨1646705244494369538814025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4391213985318318770170733 1646705244494369538814025)
                      ·
                        rfl

theorem cell23_3206947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 4, 3, 3].length) (baseStart_3206947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206947 prefixEnd_3206947 := by exact prefixLift 3206947
  have htrace : WordTrace (prefixWord ++ tailWord_3206947) baseStart_3206947 baseEnd_3206947 := by
    simpa [prefixWord, tailWord_3206947, baseEnd_3206947] using wordTrace_append hprefix tailTrace_3206947
  have hstable : (prefixWord ++ tailWord_3206947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206947).length < 2 ^ (prefixWord ++ tailWord_3206947).sum := by decide
  have hdescent : baseEnd_3206947 < baseStart_3206947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3206984 : List Nat := [2, 1, 3, 1, 1, 5, 2, 1, 2, 5]
def baseStart_3206984 : Nat := 118140960795 + 3206984 * 2 ^ 59
def prefixEnd_3206984 : Nat := 4983230072969 + 3 ^ 40 * 3206984 * 2
def baseEnd_3206984 : Nat := 548908081092861964683785

theorem tailTrace_3206984 : CollatzResearch.WordTrace tailWord_3206984 prefixEnd_3206984 548908081092861964683785 := by
  unfold tailWord_3206984
  simp only [CollatzResearch.WordTrace]
  refine ⟨58484157906826076053474003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77978877209101434737965337 58484157906826076053474003)
  ·
    refine ⟨87726236860239114080211005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58484157906826076053474003 87726236860239114080211005)
    ·
      refine ⟨32897338822589667780079127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87726236860239114080211005 32897338822589667780079127)
      ·
        refine ⟨49346008233884501670118691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32897338822589667780079127 49346008233884501670118691)
        ·
          refine ⟨74019012350826752505178037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49346008233884501670118691 74019012350826752505178037)
          ·
            refine ⟨6939282407890008047360441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74019012350826752505178037 6939282407890008047360441)
            ·
              refine ⟨5204461805917506035520331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6939282407890008047360441 5204461805917506035520331)
              ·
                refine ⟨7806692708876259053280497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5204461805917506035520331 7806692708876259053280497)
                ·
                  refine ⟨5855019531657194289960373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7806692708876259053280497 5855019531657194289960373)
                  ·
                    refine ⟨548908081092861964683785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5855019531657194289960373 548908081092861964683785)
                    ·
                      rfl

theorem cell23_3206984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 2, 5].length) (baseStart_3206984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3206984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3206984 prefixEnd_3206984 := by exact prefixLift 3206984
  have htrace : WordTrace (prefixWord ++ tailWord_3206984) baseStart_3206984 baseEnd_3206984 := by
    simpa [prefixWord, tailWord_3206984, baseEnd_3206984] using wordTrace_append hprefix tailTrace_3206984
  have hstable : (prefixWord ++ tailWord_3206984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3206984).length < 2 ^ (prefixWord ++ tailWord_3206984).sum := by decide
  have hdescent : baseEnd_3206984 < baseStart_3206984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3206984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207038 : List Nat := [4, 2, 3, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_3207038 : Nat := 118140960795 + 3207038 * 2 ^ 59
def prefixEnd_3207038 : Nat := 4983230072969 + 3 ^ 40 * 3207038 * 2
def baseEnd_3207038 : Nat := 1646751971233928682776107

theorem tailTrace_3207038 : CollatzResearch.WordTrace tailWord_3207038 prefixEnd_3207038 1646751971233928682776107 := by
  unfold tailWord_3207038
  simp only [CollatzResearch.WordTrace]
  refine ⟨14621285669432064916176721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77980190236971012886275845 14621285669432064916176721)
  ·
    refine ⟨10965964252074048687132541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14621285669432064916176721 10965964252074048687132541)
    ·
      refine ⟨4112236594527768257674703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10965964252074048687132541 4112236594527768257674703)
      ·
        refine ⟨6168354891791652386512055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4112236594527768257674703 6168354891791652386512055)
        ·
          refine ⟨9252532337687478579768083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6168354891791652386512055 9252532337687478579768083)
          ·
            refine ⟨13878798506531217869652125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9252532337687478579768083 13878798506531217869652125)
            ·
              refine ⟨5204549439949206701119547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13878798506531217869652125 5204549439949206701119547)
              ·
                refine ⟨7806824159923810051679321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5204549439949206701119547 7806824159923810051679321)
                ·
                  refine ⟨5855118119942857538759491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7806824159923810051679321 5855118119942857538759491)
                  ·
                    refine ⟨8782677179914286308139237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5855118119942857538759491 8782677179914286308139237)
                    ·
                      refine ⟨1646751971233928682776107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8782677179914286308139237 1646751971233928682776107)
                      ·
                        rfl

theorem cell23_3207038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_3207038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207038 prefixEnd_3207038 := by exact prefixLift 3207038
  have htrace : WordTrace (prefixWord ++ tailWord_3207038) baseStart_3207038 baseEnd_3207038 := by
    simpa [prefixWord, tailWord_3207038, baseEnd_3207038] using wordTrace_append hprefix tailTrace_3207038
  have hstable : (prefixWord ++ tailWord_3207038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207038).length < 2 ^ (prefixWord ++ tailWord_3207038).sum := by decide
  have hdescent : baseEnd_3207038 < baseStart_3207038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207104 : List Nat := [2, 1, 1, 2, 3, 2, 1, 1, 6, 4]
def baseStart_3207104 : Nat := 118140960795 + 3207104 * 2 ^ 59
def prefixEnd_3207104 : Nat := 4983230072969 + 3 ^ 40 * 3207104 * 2
def baseEnd_3207104 : Nat := 548928620319041808183601

theorem tailTrace_3207104 : CollatzResearch.WordTrace tailWord_3207104 prefixEnd_3207104 548928620319041808183601 := by
  unfold tailWord_3207104
  simp only [CollatzResearch.WordTrace]
  refine ⟨58486346286608706300658183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77981795048811608400877577 58486346286608706300658183)
  ·
    refine ⟨87729519429913059450987275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58486346286608706300658183 87729519429913059450987275)
    ·
      refine ⟨131594279144869589176480913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87729519429913059450987275 131594279144869589176480913)
      ·
        refine ⟨98695709358652191882360685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131594279144869589176480913 98695709358652191882360685)
        ·
          refine ⟨37010891009494571955885257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98695709358652191882360685 37010891009494571955885257)
          ·
            refine ⟨27758168257120928966913943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37010891009494571955885257 27758168257120928966913943)
            ·
              refine ⟨41637252385681393450370915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27758168257120928966913943 41637252385681393450370915)
              ·
                refine ⟨62455878578522090175556373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41637252385681393450370915 62455878578522090175556373)
                ·
                  refine ⟨2927619308368222976979205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62455878578522090175556373 2927619308368222976979205)
                  ·
                    refine ⟨548928620319041808183601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2927619308368222976979205 548928620319041808183601)
                    ·
                      rfl

theorem cell23_3207104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 1, 6, 4].length) (baseStart_3207104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207104 prefixEnd_3207104 := by exact prefixLift 3207104
  have htrace : WordTrace (prefixWord ++ tailWord_3207104) baseStart_3207104 baseEnd_3207104 := by
    simpa [prefixWord, tailWord_3207104, baseEnd_3207104] using wordTrace_append hprefix tailTrace_3207104
  have hstable : (prefixWord ++ tailWord_3207104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207104).length < 2 ^ (prefixWord ++ tailWord_3207104).sum := by decide
  have hdescent : baseEnd_3207104 < baseStart_3207104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207107 : List Nat := [1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 6]
def baseStart_3207107 : Nat := 118140960795 + 3207107 * 2 ^ 59
def prefixEnd_3207107 : Nat := 4983230072969 + 3 ^ 40 * 3207107 * 2
def baseEnd_3207107 : Nat := 1646787401399088912813289

theorem tailTrace_3207107 : CollatzResearch.WordTrace tailWord_3207107 prefixEnd_3207107 1646787401399088912813289 := by
  unfold tailWord_3207107
  simp only [CollatzResearch.WordTrace]
  refine ⟨116972801992206544113675575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77981867994804362742450383 116972801992206544113675575)
  ·
    refine ⟨175459202988309816170513363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116972801992206544113675575 175459202988309816170513363)
    ·
      refine ⟨263188804482464724255770045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175459202988309816170513363 263188804482464724255770045)
      ·
        refine ⟨98695801680924271595913767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263188804482464724255770045 98695801680924271595913767)
        ·
          refine ⟨148043702521386407393870651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98695801680924271595913767 148043702521386407393870651)
          ·
            refine ⟨222065553782079611090805977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148043702521386407393870651 222065553782079611090805977)
            ·
              refine ⟨166549165336559708318104483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222065553782079611090805977 166549165336559708318104483)
              ·
                refine ⟨249823748004839562477156725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166549165336559708318104483 249823748004839562477156725)
                ·
                  refine ⟨23420976375453708982233443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 249823748004839562477156725 23420976375453708982233443)
                  ·
                    refine ⟨35131464563180563473350165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23420976375453708982233443 35131464563180563473350165)
                    ·
                      refine ⟨1646787401399088912813289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35131464563180563473350165 1646787401399088912813289)
                      ·
                        rfl

theorem cell23_3207107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_3207107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207107 prefixEnd_3207107 := by exact prefixLift 3207107
  have htrace : WordTrace (prefixWord ++ tailWord_3207107) baseStart_3207107 baseEnd_3207107 := by
    simpa [prefixWord, tailWord_3207107, baseEnd_3207107] using wordTrace_append hprefix tailTrace_3207107
  have hstable : (prefixWord ++ tailWord_3207107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207107).length < 2 ^ (prefixWord ++ tailWord_3207107).sum := by decide
  have hdescent : baseEnd_3207107 < baseStart_3207107 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207114 : List Nat := [3, 1, 2, 1, 2, 1, 3, 3, 1, 1, 5]
def baseStart_3207114 : Nat := 118140960795 + 3207114 * 2 ^ 59
def prefixEnd_3207114 : Nat := 4983230072969 + 3 ^ 40 * 3207114 * 2
def baseEnd_3207114 : Nat := 1646790995763670385425757

theorem tailTrace_3207114 : CollatzResearch.WordTrace tailWord_3207114 prefixEnd_3207114 1646790995763670385425757 := by
  unfold tailWord_3207114
  simp only [CollatzResearch.WordTrace]
  refine ⟨29243264325795296077295099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77982038202120789539453597 29243264325795296077295099)
  ·
    refine ⟨43864896488692944115942649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29243264325795296077295099 43864896488692944115942649)
    ·
      refine ⟨32898672366519708086956987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43864896488692944115942649 32898672366519708086956987)
      ·
        refine ⟨49348008549779562130435481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32898672366519708086956987 49348008549779562130435481)
        ·
          refine ⟨37011006412334671597826611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49348008549779562130435481 37011006412334671597826611)
          ·
            refine ⟨55516509618502007396739917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37011006412334671597826611 55516509618502007396739917)
            ·
              refine ⟨20818691106938252773777469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 55516509618502007396739917 20818691106938252773777469)
              ·
                refine ⟨7807009165101844790166551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20818691106938252773777469 7807009165101844790166551)
                ·
                  refine ⟨11710513747652767185249827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7807009165101844790166551 11710513747652767185249827)
                  ·
                    refine ⟨17565770621479150777874741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11710513747652767185249827 17565770621479150777874741)
                    ·
                      refine ⟨1646790995763670385425757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17565770621479150777874741 1646790995763670385425757)
                      ·
                        rfl

theorem cell23_3207114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 1, 1, 5].length) (baseStart_3207114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207114 prefixEnd_3207114 := by exact prefixLift 3207114
  have htrace : WordTrace (prefixWord ++ tailWord_3207114) baseStart_3207114 baseEnd_3207114 := by
    simpa [prefixWord, tailWord_3207114, baseEnd_3207114] using wordTrace_append hprefix tailTrace_3207114
  have hstable : (prefixWord ++ tailWord_3207114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207114).length < 2 ^ (prefixWord ++ tailWord_3207114).sum := by decide
  have hdescent : baseEnd_3207114 < baseStart_3207114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207122 : List Nat := [3, 2, 2, 3, 3, 1, 1, 1, 3, 1, 3]
def baseStart_3207122 : Nat := 118140960795 + 3207122 * 2 ^ 59
def prefixEnd_3207122 : Nat := 4983230072969 + 3 ^ 40 * 3207122 * 2
def baseEnd_3207122 : Nat := 1646795103608906354125721

theorem tailTrace_3207122 : CollatzResearch.WordTrace tailWord_3207122 prefixEnd_3207122 1646795103608906354125721 := by
  unfold tailWord_3207122
  simp only [CollatzResearch.WordTrace]
  refine ⟨29243337271788050418867905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77982232724768134450314413 29243337271788050418867905)
  ·
    refine ⟨21932502953841037814150929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29243337271788050418867905 21932502953841037814150929)
    ·
      refine ⟨16449377215380778360613197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21932502953841037814150929 16449377215380778360613197)
      ·
        refine ⟨6168516455767791885229949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16449377215380778360613197 6168516455767791885229949)
        ·
          refine ⟨2313193670912921956961231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6168516455767791885229949 2313193670912921956961231)
          ·
            refine ⟨3469790506369382935441847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2313193670912921956961231 3469790506369382935441847)
            ·
              refine ⟨5204685759554074403162771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3469790506369382935441847 5204685759554074403162771)
              ·
                refine ⟨7807028639331111604744157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5204685759554074403162771 7807028639331111604744157)
                ·
                  refine ⟨2927635739749166851779059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7807028639331111604744157 2927635739749166851779059)
                  ·
                    refine ⟨4391453609623750277668589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2927635739749166851779059 4391453609623750277668589)
                    ·
                      refine ⟨1646795103608906354125721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4391453609623750277668589 1646795103608906354125721)
                      ·
                        rfl

theorem cell23_3207122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_3207122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207122 prefixEnd_3207122 := by exact prefixLift 3207122
  have htrace : WordTrace (prefixWord ++ tailWord_3207122) baseStart_3207122 baseEnd_3207122 := by
    simpa [prefixWord, tailWord_3207122, baseEnd_3207122] using wordTrace_append hprefix tailTrace_3207122
  have hstable : (prefixWord ++ tailWord_3207122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207122).length < 2 ^ (prefixWord ++ tailWord_3207122).sum := by decide
  have hdescent : baseEnd_3207122 < baseStart_3207122 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207124 : List Nat := [2, 4, 1, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_3207124 : Nat := 118140960795 + 3207124 * 2 ^ 59
def prefixEnd_3207124 : Nat := 4983230072969 + 3 ^ 40 * 3207124 * 2
def baseEnd_3207124 : Nat := 1646796130570215346300711

theorem tailTrace_3207124 : CollatzResearch.WordTrace tailWord_3207124 prefixEnd_3207124 1646796130570215346300711 := by
  unfold tailWord_3207124
  simp only [CollatzResearch.WordTrace]
  refine ⟨58486711016572478008522213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77982281355429970678029617 58486711016572478008522213)
  ·
    refine ⟨10966258315607339626597915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58486711016572478008522213 10966258315607339626597915)
    ·
      refine ⟨16449387473411009439896873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10966258315607339626597915 16449387473411009439896873)
      ·
        refine ⟨12337040605058257079922655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16449387473411009439896873 12337040605058257079922655)
        ·
          refine ⟨18505560907587385619883983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12337040605058257079922655 18505560907587385619883983)
          ·
            refine ⟨27758341361381078429825975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18505560907587385619883983 27758341361381078429825975)
            ·
              refine ⟨41637512042071617644738963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27758341361381078429825975 41637512042071617644738963)
              ·
                refine ⟨62456268063107426467108445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41637512042071617644738963 62456268063107426467108445)
                ·
                  refine ⟨23421100523665284925165667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 62456268063107426467108445 23421100523665284925165667)
                  ·
                    refine ⟨35131650785497927387748501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23421100523665284925165667 35131650785497927387748501)
                    ·
                      refine ⟨1646796130570215346300711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35131650785497927387748501 1646796130570215346300711)
                      ·
                        rfl

theorem cell23_3207124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_3207124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207124 prefixEnd_3207124 := by exact prefixLift 3207124
  have htrace : WordTrace (prefixWord ++ tailWord_3207124) baseStart_3207124 baseEnd_3207124 := by
    simpa [prefixWord, tailWord_3207124, baseEnd_3207124] using wordTrace_append hprefix tailTrace_3207124
  have hstable : (prefixWord ++ tailWord_3207124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207124).length < 2 ^ (prefixWord ++ tailWord_3207124).sum := by decide
  have hdescent : baseEnd_3207124 < baseStart_3207124 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207158 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_3207158 : Nat := 118140960795 + 3207158 * 2 ^ 59
def prefixEnd_3207158 : Nat := 4983230072969 + 3 ^ 40 * 3207158 * 2
def baseEnd_3207158 : Nat := 1646813588912468213275555

theorem tailTrace_3207158 : CollatzResearch.WordTrace tailWord_3207158 prefixEnd_3207158 1646813588912468213275555 := by
  unfold tailWord_3207158
  simp only [CollatzResearch.WordTrace]
  refine ⟨7310916382188861238986383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 77983108076681186549188085 7310916382188861238986383)
  ·
    refine ⟨10966374573283291858479575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7310916382188861238986383 10966374573283291858479575)
    ·
      refine ⟨16449561859924937787719363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10966374573283291858479575 16449561859924937787719363)
      ·
        refine ⟨24674342789887406681579045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16449561859924937787719363 24674342789887406681579045)
        ·
          refine ⟨4626439273103888752796071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24674342789887406681579045 4626439273103888752796071)
          ·
            refine ⟨6939658909655833129194107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4626439273103888752796071 6939658909655833129194107)
            ·
              refine ⟨10409488364483749693791161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6939658909655833129194107 10409488364483749693791161)
              ·
                refine ⟨7807116273362812270343371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10409488364483749693791161 7807116273362812270343371)
                ·
                  refine ⟨11710674410044218405515057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7807116273362812270343371 11710674410044218405515057)
                  ·
                    refine ⟨8783005807533163804136293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11710674410044218405515057 8783005807533163804136293)
                    ·
                      refine ⟨1646813588912468213275555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8783005807533163804136293 1646813588912468213275555)
                      ·
                        rfl

theorem cell23_3207158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_3207158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207158 prefixEnd_3207158 := by exact prefixLift 3207158
  have htrace : WordTrace (prefixWord ++ tailWord_3207158) baseStart_3207158 baseEnd_3207158 := by
    simpa [prefixWord, tailWord_3207158, baseEnd_3207158] using wordTrace_append hprefix tailTrace_3207158
  have hstable : (prefixWord ++ tailWord_3207158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207158).length < 2 ^ (prefixWord ++ tailWord_3207158).sum := by decide
  have hdescent : baseEnd_3207158 < baseStart_3207158 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207161 : List Nat := [1, 2, 1, 3, 1, 5, 1, 2, 1, 3, 3]
def baseStart_3207161 : Nat := 118140960795 + 3207161 * 2 ^ 59
def prefixEnd_3207161 : Nat := 4983230072969 + 3 ^ 40 * 3207161 * 2
def baseEnd_3207161 : Nat := 1646815129354431701538041

theorem tailTrace_3207161 : CollatzResearch.WordTrace tailWord_3207161 prefixEnd_3207161 1646815129354431701538041 := by
  unfold tailWord_3207161
  simp only [CollatzResearch.WordTrace]
  refine ⟨116974771534010911336141337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77983181022673940890760891 116974771534010911336141337)
  ·
    refine ⟨87731078650508183502106003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116974771534010911336141337 87731078650508183502106003)
    ·
      refine ⟨131596617975762275253159005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87731078650508183502106003 131596617975762275253159005)
      ·
        refine ⟨49348731740910853219934627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131596617975762275253159005 49348731740910853219934627)
        ·
          refine ⟨74023097611366279829901941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49348731740910853219934627 74023097611366279829901941)
          ·
            refine ⟨6939665401065588734053307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74023097611366279829901941 6939665401065588734053307)
            ·
              refine ⟨10409498101598383101079961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6939665401065588734053307 10409498101598383101079961)
              ·
                refine ⟨7807123576198787325809971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10409498101598383101079961 7807123576198787325809971)
                ·
                  refine ⟨11710685364298180988714957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7807123576198787325809971 11710685364298180988714957)
                  ·
                    refine ⟨4391507011611817870768109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11710685364298180988714957 4391507011611817870768109)
                    ·
                      refine ⟨1646815129354431701538041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4391507011611817870768109 1646815129354431701538041)
                      ·
                        rfl

theorem cell23_3207161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3, 3].length) (baseStart_3207161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207161 prefixEnd_3207161 := by exact prefixLift 3207161
  have htrace : WordTrace (prefixWord ++ tailWord_3207161) baseStart_3207161 baseEnd_3207161 := by
    simpa [prefixWord, tailWord_3207161, baseEnd_3207161] using wordTrace_append hprefix tailTrace_3207161
  have hstable : (prefixWord ++ tailWord_3207161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207161).length < 2 ^ (prefixWord ++ tailWord_3207161).sum := by decide
  have hdescent : baseEnd_3207161 < baseStart_3207161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207194 : List Nat := [3, 1, 1, 3, 1, 3, 1, 1, 1, 8]
def baseStart_3207194 : Nat := 118140960795 + 3207194 * 2 ^ 59
def prefixEnd_3207194 : Nat := 4983230072969 + 3 ^ 40 * 3207194 * 2
def baseEnd_3207194 : Nat := 548944024738676690808463

theorem tailTrace_3207194 : CollatzResearch.WordTrace tailWord_3207194 prefixEnd_3207194 548944024738676690808463 := by
  unfold tailWord_3207194
  simp only [CollatzResearch.WordTrace]
  refine ⟨29243993785722839493023159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77983983428594238648061757 29243993785722839493023159)
  ·
    refine ⟨43865990678584259239534739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29243993785722839493023159 43865990678584259239534739)
    ·
      refine ⟨65798986017876388859302109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43865990678584259239534739 65798986017876388859302109)
      ·
        refine ⟨24674619756703645822238291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65798986017876388859302109 24674619756703645822238291)
        ·
          refine ⟨37011929635055468733357437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24674619756703645822238291 37011929635055468733357437)
          ·
            refine ⟨13879473613145800775009039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37011929635055468733357437 13879473613145800775009039)
            ·
              refine ⟨20819210419718701162513559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13879473613145800775009039 20819210419718701162513559)
              ·
                refine ⟨31228815629578051743770339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20819210419718701162513559 31228815629578051743770339)
                ·
                  refine ⟨46843223444367077615655509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31228815629578051743770339 46843223444367077615655509)
                  ·
                    refine ⟨548944024738676690808463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46843223444367077615655509 548944024738676690808463)
                    ·
                      rfl

theorem cell23_3207194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 1, 1, 1, 8].length) (baseStart_3207194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207194 prefixEnd_3207194 := by exact prefixLift 3207194
  have htrace : WordTrace (prefixWord ++ tailWord_3207194) baseStart_3207194 baseEnd_3207194 := by
    simpa [prefixWord, tailWord_3207194, baseEnd_3207194] using wordTrace_append hprefix tailTrace_3207194
  have hstable : (prefixWord ++ tailWord_3207194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207194).length < 2 ^ (prefixWord ++ tailWord_3207194).sum := by decide
  have hdescent : baseEnd_3207194 < baseStart_3207194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207218 : List Nat := [3, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2]
def baseStart_3207218 : Nat := 118140960795 + 3207218 * 2 ^ 59
def prefixEnd_3207218 : Nat := 4983230072969 + 3 ^ 40 * 3207218 * 2
def baseEnd_3207218 : Nat := 1646844397751737978525279

theorem tailTrace_3207218 : CollatzResearch.WordTrace tailWord_3207218 prefixEnd_3207218 1646844397751737978525279 := by
  unfold tailWord_3207218
  simp only [CollatzResearch.WordTrace]
  refine ⟨29244212623701102517741577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77984566996536273380644205 29244212623701102517741577)
  ·
    refine ⟨21933159467775826888306183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29244212623701102517741577 21933159467775826888306183)
    ·
      refine ⟨32899739201663740332459275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21933159467775826888306183 32899739201663740332459275)
      ·
        refine ⟨49349608802495610498688913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32899739201663740332459275 49349608802495610498688913)
        ·
          refine ⟨37012206601871707874016685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49349608802495610498688913 37012206601871707874016685)
          ·
            refine ⟨13879577475701890452756257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37012206601871707874016685 13879577475701890452756257)
            ·
              refine ⟨10409683106776417839567193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13879577475701890452756257 10409683106776417839567193)
              ·
                refine ⟨7807262330082313379675395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10409683106776417839567193 7807262330082313379675395)
                ·
                  refine ⟨11710893495123470069513093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7807262330082313379675395 11710893495123470069513093)
                  ·
                    refine ⟨2195792530335650638033705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11710893495123470069513093 2195792530335650638033705)
                    ·
                      refine ⟨1646844397751737978525279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2195792530335650638033705 1646844397751737978525279)
                      ·
                        rfl

theorem cell23_3207218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2].length) (baseStart_3207218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207218 prefixEnd_3207218 := by exact prefixLift 3207218
  have htrace : WordTrace (prefixWord ++ tailWord_3207218) baseStart_3207218 baseEnd_3207218 := by
    simpa [prefixWord, tailWord_3207218, baseEnd_3207218] using wordTrace_append hprefix tailTrace_3207218
  have hstable : (prefixWord ++ tailWord_3207218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207218).length < 2 ^ (prefixWord ++ tailWord_3207218).sum := by decide
  have hdescent : baseEnd_3207218 < baseStart_3207218 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207241 : List Nat := [1, 2, 1, 1, 2, 2, 3, 6, 5]
def baseStart_3207241 : Nat := 118140960795 + 3207241 * 2 ^ 59
def prefixEnd_3207241 : Nat := 4983230072969 + 3 ^ 40 * 3207241 * 2
def baseEnd_3207241 : Nat := 182984023089643487615297

theorem tailTrace_3207241 : CollatzResearch.WordTrace tailWord_3207241 prefixEnd_3207241 182984023089643487615297 := by
  unfold tailWord_3207241
  simp only [CollatzResearch.WordTrace]
  refine ⟨116977689373721084999053577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77985126249147389999369051 116977689373721084999053577)
  ·
    refine ⟨87733267030290813749290183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116977689373721084999053577 87733267030290813749290183)
    ·
      refine ⟨131599900545436220623935275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87733267030290813749290183 131599900545436220623935275)
      ·
        refine ⟨197399850818154330935902913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131599900545436220623935275 197399850818154330935902913)
        ·
          refine ⟨148049888113615748201927185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197399850818154330935902913 148049888113615748201927185)
          ·
            refine ⟨111037416085211811151445389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148049888113615748201927185 111037416085211811151445389)
            ·
              refine ⟨41639031031954429181792021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111037416085211811151445389 41639031031954429181792021)
              ·
                refine ⟨1951829579622863867896501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41639031031954429181792021 1951829579622863867896501)
                ·
                  refine ⟨182984023089643487615297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1951829579622863867896501 182984023089643487615297)
                  ·
                    rfl

theorem cell23_3207241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 6, 5].length) (baseStart_3207241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207241 prefixEnd_3207241 := by exact prefixLift 3207241
  have htrace : WordTrace (prefixWord ++ tailWord_3207241) baseStart_3207241 baseEnd_3207241 := by
    simpa [prefixWord, tailWord_3207241, baseEnd_3207241] using wordTrace_append hprefix tailTrace_3207241
  have hstable : (prefixWord ++ tailWord_3207241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207241).length < 2 ^ (prefixWord ++ tailWord_3207241).sum := by decide
  have hdescent : baseEnd_3207241 < baseStart_3207241 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207271 : List Nat := [1, 1, 5, 1, 1, 2, 2, 3, 2, 5]
def baseStart_3207271 : Nat := 118140960795 + 3207271 * 2 ^ 59
def prefixEnd_3207271 : Nat := 4983230072969 + 3 ^ 40 * 3207271 * 2
def baseEnd_3207271 : Nat := 548957204075475423720845

theorem tailTrace_3207271 : CollatzResearch.WordTrace tailWord_3207271 prefixEnd_3207271 548957204075475423720845 := by
  unfold tailWord_3207271
  simp only [CollatzResearch.WordTrace]
  refine ⟨116978783563612400122645667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77985855709074933415097111 116978783563612400122645667)
  ·
    refine ⟨175468175345418600183968501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116978783563612400122645667 175468175345418600183968501)
    ·
      refine ⟨16450141438632993767247047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 175468175345418600183968501 16450141438632993767247047)
      ·
        refine ⟨24675212157949490650870571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16450141438632993767247047 24675212157949490650870571)
        ·
          refine ⟨37012818236924235976305857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24675212157949490650870571 37012818236924235976305857)
          ·
            refine ⟨27759613677693176982229393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37012818236924235976305857 27759613677693176982229393)
            ·
              refine ⟨20819710258269882736672045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27759613677693176982229393 20819710258269882736672045)
              ·
                refine ⟨7807391346851206026252017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20819710258269882736672045 7807391346851206026252017)
                ·
                  refine ⟨5855543510138404519689013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807391346851206026252017 5855543510138404519689013)
                  ·
                    refine ⟨548957204075475423720845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5855543510138404519689013 548957204075475423720845)
                    ·
                      rfl

theorem cell23_3207271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_3207271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207271 prefixEnd_3207271 := by exact prefixLift 3207271
  have htrace : WordTrace (prefixWord ++ tailWord_3207271) baseStart_3207271 baseEnd_3207271 := by
    simpa [prefixWord, tailWord_3207271, baseEnd_3207271] using wordTrace_append hprefix tailTrace_3207271
  have hstable : (prefixWord ++ tailWord_3207271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207271).length < 2 ^ (prefixWord ++ tailWord_3207271).sum := by decide
  have hdescent : baseEnd_3207271 < baseStart_3207271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207328 : List Nat := [2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 3]
def baseStart_3207328 : Nat := 118140960795 + 3207328 * 2 ^ 59
def prefixEnd_3207328 : Nat := 4983230072969 + 3 ^ 40 * 3207328 * 2
def baseEnd_3207328 : Nat := 1646900880623732548149773

theorem tailTrace_3207328 : CollatzResearch.WordTrace tailWord_3207328 prefixEnd_3207328 1646900880623732548149773 := by
  unfold tailWord_3207328
  simp only [CollatzResearch.WordTrace]
  refine ⟨58490431262202949428735319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77987241682937265904980425 58490431262202949428735319)
  ·
    refine ⟨87735646893304424143102979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58490431262202949428735319 87735646893304424143102979)
    ·
      refine ⟨131603470339956636214654469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87735646893304424143102979 131603470339956636214654469)
      ·
        refine ⟨24675650688741869290247713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131603470339956636214654469 24675650688741869290247713)
        ·
          refine ⟨18506738016556401967685785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24675650688741869290247713 18506738016556401967685785)
          ·
            refine ⟨13880053512417301475764339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18506738016556401967685785 13880053512417301475764339)
            ·
              refine ⟨20820080268625952213646509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13880053512417301475764339 20820080268625952213646509)
              ·
                refine ⟨7807530100734732080117441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20820080268625952213646509 7807530100734732080117441)
                ·
                  refine ⟨5855647575551049060088081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807530100734732080117441 5855647575551049060088081)
                  ·
                    refine ⟨4391735681663286795066061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5855647575551049060088081 4391735681663286795066061)
                    ·
                      refine ⟨1646900880623732548149773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4391735681663286795066061 1646900880623732548149773)
                      ·
                        rfl

theorem cell23_3207328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 1, 3, 2, 2, 3].length) (baseStart_3207328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207328 prefixEnd_3207328 := by exact prefixLift 3207328
  have htrace : WordTrace (prefixWord ++ tailWord_3207328) baseStart_3207328 baseEnd_3207328 := by
    simpa [prefixWord, tailWord_3207328, baseEnd_3207328] using wordTrace_append hprefix tailTrace_3207328
  have hstable : (prefixWord ++ tailWord_3207328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207328).length < 2 ^ (prefixWord ++ tailWord_3207328).sum := by decide
  have hdescent : baseEnd_3207328 < baseStart_3207328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207368 : List Nat := [2, 1, 3, 1, 2, 1, 1, 4, 1, 5, 2]
def baseStart_3207368 : Nat := 118140960795 + 3207368 * 2 ^ 59
def prefixEnd_3207368 : Nat := 4983230072969 + 3 ^ 40 * 3207368 * 2
def baseEnd_3207368 : Nat := 1646921419849912391649589

theorem tailTrace_3207368 : CollatzResearch.WordTrace tailWord_3207368 prefixEnd_3207368 1646921419849912391649589 := by
  unfold tailWord_3207368
  simp only [CollatzResearch.WordTrace]
  refine ⟨58491160722130492844463379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77988214296173990459284505 58491160722130492844463379)
  ·
    refine ⟨87736741083195739266695069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58491160722130492844463379 87736741083195739266695069)
    ·
      refine ⟨32901277906198402225010651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87736741083195739266695069 32901277906198402225010651)
      ·
        refine ⟨49351916859297603337515977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32901277906198402225010651 49351916859297603337515977)
        ·
          refine ⟨37013937644473202503136983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49351916859297603337515977 37013937644473202503136983)
          ·
            refine ⟨55520906466709803754705475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37013937644473202503136983 55520906466709803754705475)
            ·
              refine ⟨83281359700064705632058213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55520906466709803754705475 83281359700064705632058213)
              ·
                refine ⟨15615254943762132306010915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83281359700064705632058213 15615254943762132306010915)
                ·
                  refine ⟨23422882415643198459016373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15615254943762132306010915 23422882415643198459016373)
                  ·
                    refine ⟨2195895226466549855532785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23422882415643198459016373 2195895226466549855532785)
                    ·
                      refine ⟨1646921419849912391649589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2195895226466549855532785 1646921419849912391649589)
                      ·
                        rfl

theorem cell23_3207368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 4, 1, 5, 2].length) (baseStart_3207368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207368 prefixEnd_3207368 := by exact prefixLift 3207368
  have htrace : WordTrace (prefixWord ++ tailWord_3207368) baseStart_3207368 baseEnd_3207368 := by
    simpa [prefixWord, tailWord_3207368, baseEnd_3207368] using wordTrace_append hprefix tailTrace_3207368
  have hstable : (prefixWord ++ tailWord_3207368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207368).length < 2 ^ (prefixWord ++ tailWord_3207368).sum := by decide
  have hdescent : baseEnd_3207368 < baseStart_3207368 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207378 : List Nat := [3, 2, 2, 2, 1, 2, 2, 1, 3, 5]
def baseStart_3207378 : Nat := 118140960795 + 3207378 * 2 ^ 59
def prefixEnd_3207378 : Nat := 4983230072969 + 3 ^ 40 * 3207378 * 2
def baseEnd_3207378 : Nat := 548975518218819117508181

theorem tailTrace_3207378 : CollatzResearch.WordTrace tailWord_3207378 prefixEnd_3207378 548975518218819117508181 := by
  unfold tailWord_3207378
  simp only [CollatzResearch.WordTrace]
  refine ⟨29245671543556189349197697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77988457449483171597860525 29245671543556189349197697)
  ·
    refine ⟨21934253657667142011898273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29245671543556189349197697 21934253657667142011898273)
    ·
      refine ⟨16450690243250356508923705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21934253657667142011898273 16450690243250356508923705)
      ·
        refine ⟨12338017682437767381692779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16450690243250356508923705 12338017682437767381692779)
        ·
          refine ⟨18507026523656651072539169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12338017682437767381692779 18507026523656651072539169)
          ·
            refine ⟨13880269892742488304404377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18507026523656651072539169 13880269892742488304404377)
            ·
              refine ⟨10410202419556866228303283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13880269892742488304404377 10410202419556866228303283)
              ·
                refine ⟨15615303629335299342454925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10410202419556866228303283 15615303629335299342454925)
                ·
                  refine ⟨5855738861000737253420597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15615303629335299342454925 5855738861000737253420597)
                  ·
                    refine ⟨548975518218819117508181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5855738861000737253420597 548975518218819117508181)
                    ·
                      rfl

theorem cell23_3207378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 1, 3, 5].length) (baseStart_3207378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207378 prefixEnd_3207378 := by exact prefixLift 3207378
  have htrace : WordTrace (prefixWord ++ tailWord_3207378) baseStart_3207378 baseEnd_3207378 := by
    simpa [prefixWord, tailWord_3207378, baseEnd_3207378] using wordTrace_append hprefix tailTrace_3207378
  have hstable : (prefixWord ++ tailWord_3207378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207378).length < 2 ^ (prefixWord ++ tailWord_3207378).sum := by decide
  have hdescent : baseEnd_3207378 < baseStart_3207378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207385 : List Nat := [1, 2, 1, 2, 3, 1, 5, 1, 2, 3, 2]
def baseStart_3207385 : Nat := 118140960795 + 3207385 * 2 ^ 59
def prefixEnd_3207385 : Nat := 4983230072969 + 3 ^ 40 * 3207385 * 2
def baseEnd_3207385 : Nat := 1646930149021038825137011

theorem tailTrace_3207385 : CollatzResearch.WordTrace tailWord_3207385 prefixEnd_3207385 1646930149021038825137011 := by
  unfold tailWord_3207385
  simp only [CollatzResearch.WordTrace]
  refine ⟨116982941485199397592295609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77988627656799598394863739 116982941485199397592295609)
  ·
    refine ⟨87737206113899548194221707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116982941485199397592295609 87737206113899548194221707)
    ·
      refine ⟨131605809170849322291332561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87737206113899548194221707 131605809170849322291332561)
      ·
        refine ⟨98704356878136991718499421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131605809170849322291332561 98704356878136991718499421)
        ·
          refine ⟨37014133829301371894437283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98704356878136991718499421 37014133829301371894437283)
          ·
            refine ⟨55521200743952057841655925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37014133829301371894437283 55521200743952057841655925)
            ·
              refine ⟨5205112569745505422655243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55521200743952057841655925 5205112569745505422655243)
              ·
                refine ⟨7807668854618258133982865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5205112569745505422655243 7807668854618258133982865)
                ·
                  refine ⟨5855751640963693600487149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7807668854618258133982865 5855751640963693600487149)
                  ·
                    refine ⟨2195906865361385100182681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5855751640963693600487149 2195906865361385100182681)
                    ·
                      refine ⟨1646930149021038825137011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2195906865361385100182681 1646930149021038825137011)
                      ·
                        rfl

theorem cell23_3207385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 3, 2].length) (baseStart_3207385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207385 prefixEnd_3207385 := by exact prefixLift 3207385
  have htrace : WordTrace (prefixWord ++ tailWord_3207385) baseStart_3207385 baseEnd_3207385 := by
    simpa [prefixWord, tailWord_3207385, baseEnd_3207385] using wordTrace_append hprefix tailTrace_3207385
  have hstable : (prefixWord ++ tailWord_3207385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207385).length < 2 ^ (prefixWord ++ tailWord_3207385).sum := by decide
  have hdescent : baseEnd_3207385 < baseStart_3207385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207392 : List Nat := [2, 1, 1, 3, 1, 3, 4, 3, 1, 1, 3]
def baseStart_3207392 : Nat := 118140960795 + 3207392 * 2 ^ 59
def prefixEnd_3207392 : Nat := 4983230072969 + 3 ^ 40 * 3207392 * 2
def baseEnd_3207392 : Nat := 1646933743385620297749479

theorem tailTrace_3207392 : CollatzResearch.WordTrace tailWord_3207392 prefixEnd_3207392 1646933743385620297749479 := by
  unfold tailWord_3207392
  simp only [CollatzResearch.WordTrace]
  refine ⟨58491598398087018893900215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77988797864116025191866953 58491598398087018893900215)
  ·
    refine ⟨87737397597130528340850323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58491598398087018893900215 87737397597130528340850323)
    ·
      refine ⟨131606096395695792511275485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87737397597130528340850323 131606096395695792511275485)
      ·
        refine ⟨49352286148385922191728307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131606096395695792511275485 49352286148385922191728307)
        ·
          refine ⟨74028429222578883287592461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49352286148385922191728307 74028429222578883287592461)
          ·
            refine ⟨27760660958467081232847173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74028429222578883287592461 27760660958467081232847173)
            ·
              refine ⟨5205123929712577731158845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27760660958467081232847173 5205123929712577731158845)
              ·
                refine ⟨1951921473642216649184567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5205123929712577731158845 1951921473642216649184567)
                ·
                  refine ⟨2927882210463324973776851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1951921473642216649184567 2927882210463324973776851)
                  ·
                    refine ⟨4391823315694987460665277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2927882210463324973776851 4391823315694987460665277)
                    ·
                      refine ⟨1646933743385620297749479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4391823315694987460665277 1646933743385620297749479)
                      ·
                        rfl

theorem cell23_3207392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3, 1, 1, 3].length) (baseStart_3207392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207392 prefixEnd_3207392 := by exact prefixLift 3207392
  have htrace : WordTrace (prefixWord ++ tailWord_3207392) baseStart_3207392 baseEnd_3207392 := by
    simpa [prefixWord, tailWord_3207392, baseEnd_3207392] using wordTrace_append hprefix tailTrace_3207392
  have hstable : (prefixWord ++ tailWord_3207392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207392).length < 2 ^ (prefixWord ++ tailWord_3207392).sum := by decide
  have hdescent : baseEnd_3207392 < baseStart_3207392 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207411 : List Nat := [1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 6]
def baseStart_3207411 : Nat := 118140960795 + 3207411 * 2 ^ 59
def prefixEnd_3207411 : Nat := 4983230072969 + 3 ^ 40 * 3207411 * 2
def baseEnd_3207411 : Nat := 1646943499518055723411891

theorem tailTrace_3207411 : CollatzResearch.WordTrace tailWord_3207411 prefixEnd_3207411 1646943499518055723411891 := by
  unfold tailWord_3207411
  simp only [CollatzResearch.WordTrace]
  refine ⟨116983889783105204032742087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77989259855403469355161391 116983889783105204032742087)
  ·
    refine ⟨175475834674657806049113131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116983889783105204032742087 175475834674657806049113131)
    ·
      refine ⟨263213752011986709073669697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175475834674657806049113131 263213752011986709073669697)
      ·
        refine ⟨197410314008990031805252273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263213752011986709073669697 197410314008990031805252273)
        ·
          refine ⟨148057735506742523853939205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197410314008990031805252273 148057735506742523853939205)
          ·
            refine ⟨27760825407514223222613601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148057735506742523853939205 27760825407514223222613601)
            ·
              refine ⟨20820619055635667416960201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27760825407514223222613601 20820619055635667416960201)
              ·
                refine ⟨15615464291726750562720151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20820619055635667416960201 15615464291726750562720151)
                ·
                  refine ⟨23423196437590125844080227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15615464291726750562720151 23423196437590125844080227)
                  ·
                    refine ⟨35134794656385188766120341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23423196437590125844080227 35134794656385188766120341)
                    ·
                      refine ⟨1646943499518055723411891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 35134794656385188766120341 1646943499518055723411891)
                      ·
                        rfl

theorem cell23_3207411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_3207411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207411 prefixEnd_3207411 := by exact prefixLift 3207411
  have htrace : WordTrace (prefixWord ++ tailWord_3207411) baseStart_3207411 baseEnd_3207411 := by
    simpa [prefixWord, tailWord_3207411, baseEnd_3207411] using wordTrace_append hprefix tailTrace_3207411
  have hstable : (prefixWord ++ tailWord_3207411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207411).length < 2 ^ (prefixWord ++ tailWord_3207411).sum := by decide
  have hdescent : baseEnd_3207411 < baseStart_3207411 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207418 : List Nat := [3, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5]
def baseStart_3207418 : Nat := 118140960795 + 3207418 * 2 ^ 59
def prefixEnd_3207418 : Nat := 4983230072969 + 3 ^ 40 * 3207418 * 2
def baseEnd_3207418 : Nat := 1646947093882637196024359

theorem tailTrace_3207418 : CollatzResearch.WordTrace tailWord_3207418 prefixEnd_3207418 1646947093882637196024359 := by
  unfold tailWord_3207418
  simp only [CollatzResearch.WordTrace]
  refine ⟨29246036273519961057061727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77989430062719896152164605 29246036273519961057061727)
  ·
    refine ⟨43869054410279941585592591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29246036273519961057061727 43869054410279941585592591)
    ·
      refine ⟨65803581615419912378388887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43869054410279941585592591 65803581615419912378388887)
      ·
        refine ⟨98705372423129868567583331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65803581615419912378388887 98705372423129868567583331)
        ·
          refine ⟨148058058634694802851374997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98705372423129868567583331 148058058634694802851374997)
          ·
            refine ⟨6940221498501318883658203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 148058058634694802851374997 6940221498501318883658203)
            ·
              refine ⟨10410332247751978325487305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6940221498501318883658203 10410332247751978325487305)
              ·
                refine ⟨7807749185813983744115479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10410332247751978325487305 7807749185813983744115479)
                ·
                  refine ⟨11711623778720975616173219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7807749185813983744115479 11711623778720975616173219)
                  ·
                    refine ⟨17567435668081463424259829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11711623778720975616173219 17567435668081463424259829)
                    ·
                      refine ⟨1646947093882637196024359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17567435668081463424259829 1646947093882637196024359)
                      ·
                        rfl

theorem cell23_3207418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_3207418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207418 prefixEnd_3207418 := by exact prefixLift 3207418
  have htrace : WordTrace (prefixWord ++ tailWord_3207418) baseStart_3207418 baseEnd_3207418 := by
    simpa [prefixWord, tailWord_3207418, baseEnd_3207418] using wordTrace_append hprefix tailTrace_3207418
  have hstable : (prefixWord ++ tailWord_3207418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207418).length < 2 ^ (prefixWord ++ tailWord_3207418).sum := by decide
  have hdescent : baseEnd_3207418 < baseStart_3207418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207432 : List Nat := [2, 1, 3, 2, 3, 1, 2, 2, 3, 2, 2]
def baseStart_3207432 : Nat := 118140960795 + 3207432 * 2 ^ 59
def prefixEnd_3207432 : Nat := 4983230072969 + 3 ^ 40 * 3207432 * 2
def baseEnd_3207432 : Nat := 1646954282611800141249295

theorem tailTrace_3207432 : CollatzResearch.WordTrace tailWord_3207432 prefixEnd_3207432 1646954282611800141249295 := by
  unfold tailWord_3207432
  simp only [CollatzResearch.WordTrace]
  refine ⟨58492327858014562309628275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77989770477352749746171033 58492327858014562309628275)
  ·
    refine ⟨87738491787021843464442413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58492327858014562309628275 87738491787021843464442413)
    ·
      refine ⟨32901934420133191299165905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87738491787021843464442413 32901934420133191299165905)
      ·
        refine ⟨24676450815099893474374429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32901934420133191299165905 24676450815099893474374429)
        ·
          refine ⟨9253669055662460052890411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24676450815099893474374429 9253669055662460052890411)
          ·
            refine ⟨13880503583493690079335617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9253669055662460052890411 13880503583493690079335617)
            ·
              refine ⟨10410377687620267559501713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13880503583493690079335617 10410377687620267559501713)
              ·
                refine ⟨7807783265715200669626285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10410377687620267559501713 7807783265715200669626285)
                ·
                  refine ⟨2927918724643200251109857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7807783265715200669626285 2927918724643200251109857)
                  ·
                    refine ⟨2195939043482400188332393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2927918724643200251109857 2195939043482400188332393)
                    ·
                      refine ⟨1646954282611800141249295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2195939043482400188332393 1646954282611800141249295)
                      ·
                        rfl

theorem cell23_3207432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 2, 2, 3, 2, 2].length) (baseStart_3207432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207432 prefixEnd_3207432 := by exact prefixLift 3207432
  have htrace : WordTrace (prefixWord ++ tailWord_3207432) baseStart_3207432 baseEnd_3207432 := by
    simpa [prefixWord, tailWord_3207432, baseEnd_3207432] using wordTrace_append hprefix tailTrace_3207432
  have hstable : (prefixWord ++ tailWord_3207432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207432).length < 2 ^ (prefixWord ++ tailWord_3207432).sum := by decide
  have hdescent : baseEnd_3207432 < baseStart_3207432 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207435 : List Nat := [1, 1, 1, 1, 5, 2, 4, 2, 1, 2, 3]
def baseStart_3207435 : Nat := 118140960795 + 3207435 * 2 ^ 59
def prefixEnd_3207435 : Nat := 4983230072969 + 3 ^ 40 * 3207435 * 2
def baseEnd_3207435 : Nat := 1646955823053763629511781

theorem tailTrace_3207435 : CollatzResearch.WordTrace tailWord_3207435 prefixEnd_3207435 1646955823053763629511781 := by
  unfold tailWord_3207435
  simp only [CollatzResearch.WordTrace]
  refine ⟨116984765135018256131615759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77989843423345504087743839 116984765135018256131615759)
  ·
    refine ⟨175477147702527384197423639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116984765135018256131615759 175477147702527384197423639)
    ·
      refine ⟨263215721553791076296135459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175477147702527384197423639 263215721553791076296135459)
      ·
        refine ⟨394823582330686614444203189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263215721553791076296135459 394823582330686614444203189)
        ·
          refine ⟨37014710843501870104144049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 394823582330686614444203189 37014710843501870104144049)
          ·
            refine ⟨27761033132626402578108037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37014710843501870104144049 27761033132626402578108037)
            ·
              refine ⟨5205193712367450483395257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27761033132626402578108037 5205193712367450483395257)
              ·
                refine ⟨3903895284275587862546443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5205193712367450483395257 3903895284275587862546443)
                ·
                  refine ⟨5855842926413381793819665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3903895284275587862546443 5855842926413381793819665)
                  ·
                    refine ⟨4391882194810036345364749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5855842926413381793819665 4391882194810036345364749)
                    ·
                      refine ⟨1646955823053763629511781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4391882194810036345364749 1646955823053763629511781)
                      ·
                        rfl

theorem cell23_3207435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 2, 1, 2, 3].length) (baseStart_3207435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207435 prefixEnd_3207435 := by exact prefixLift 3207435
  have htrace : WordTrace (prefixWord ++ tailWord_3207435) baseStart_3207435 baseEnd_3207435 := by
    simpa [prefixWord, tailWord_3207435, baseEnd_3207435] using wordTrace_append hprefix tailTrace_3207435
  have hstable : (prefixWord ++ tailWord_3207435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207435).length < 2 ^ (prefixWord ++ tailWord_3207435).sum := by decide
  have hdescent : baseEnd_3207435 < baseStart_3207435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207448 : List Nat := [2, 1, 2, 3, 1, 2, 2, 1, 3, 3, 3]
def baseStart_3207448 : Nat := 118140960795 + 3207448 * 2 ^ 59
def prefixEnd_3207448 : Nat := 4983230072969 + 3 ^ 40 * 3207448 * 2
def baseEnd_3207448 : Nat := 1646962498302272078649221

theorem tailTrace_3207448 : CollatzResearch.WordTrace tailWord_3207448 prefixEnd_3207448 1646962498302272078649221 := by
  unfold tailWord_3207448
  simp only [CollatzResearch.WordTrace]
  refine ⟨58492619641985579675919499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77990159522647439567892665 58492619641985579675919499)
  ·
    refine ⟨87738929462978369513879249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58492619641985579675919499 87738929462978369513879249)
    ·
      refine ⟨65804197097233777135409437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87738929462978369513879249 65804197097233777135409437)
      ·
        refine ⟨24676573911462666425778539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65804197097233777135409437 24676573911462666425778539)
        ·
          refine ⟨37014860867193999638667809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24676573911462666425778539 37014860867193999638667809)
          ·
            refine ⟨27761145650395499729000857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37014860867193999638667809 27761145650395499729000857)
            ·
              refine ⟨20820859237796624796750643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27761145650395499729000857 20820859237796624796750643)
              ·
                refine ⟨31231288856694937195125965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20820859237796624796750643 31231288856694937195125965)
                ·
                  refine ⟨11711733321260601448172237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31231288856694937195125965 11711733321260601448172237)
                  ·
                    refine ⟨4391899995472725543064589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11711733321260601448172237 4391899995472725543064589)
                    ·
                      refine ⟨1646962498302272078649221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4391899995472725543064589 1646962498302272078649221)
                      ·
                        rfl

theorem cell23_3207448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_3207448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207448 prefixEnd_3207448 := by exact prefixLift 3207448
  have htrace : WordTrace (prefixWord ++ tailWord_3207448) baseStart_3207448 baseEnd_3207448 := by
    simpa [prefixWord, tailWord_3207448, baseEnd_3207448] using wordTrace_append hprefix tailTrace_3207448
  have hstable : (prefixWord ++ tailWord_3207448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207448).length < 2 ^ (prefixWord ++ tailWord_3207448).sum := by decide
  have hdescent : baseEnd_3207448 < baseStart_3207448 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207466 : List Nat := [3, 1, 4, 2, 2, 2, 1, 1, 3, 2, 2]
def baseStart_3207466 : Nat := 118140960795 + 3207466 * 2 ^ 59
def prefixEnd_3207466 : Nat := 4983230072969 + 3 ^ 40 * 3207466 * 2
def baseEnd_3207466 : Nat := 1646971740954053008224139

theorem tailTrace_3207466 : CollatzResearch.WordTrace tailWord_3207466 prefixEnd_3207466 1646971740954053008224139 := by
  unfold tailWord_3207466
  simp only [CollatzResearch.WordTrace]
  refine ⟨29246473949476487106498563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77990597198603965617329501 29246473949476487106498563)
  ·
    refine ⟨43869710924214730659747845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29246473949476487106498563 43869710924214730659747845)
    ·
      refine ⟨8225570798290261998702721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43869710924214730659747845 8225570798290261998702721)
      ·
        refine ⟨6169178098717696499027041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8225570798290261998702721 6169178098717696499027041)
        ·
          refine ⟨4626883574038272374270281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6169178098717696499027041 4626883574038272374270281)
          ·
            refine ⟨3470162680528704280702711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4626883574038272374270281 3470162680528704280702711)
            ·
              refine ⟨5205244020793056421054067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470162680528704280702711 5205244020793056421054067)
              ·
                refine ⟨7807866031189584631581101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5205244020793056421054067 7807866031189584631581101)
                ·
                  refine ⟨2927949761696094236842913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7807866031189584631581101 2927949761696094236842913)
                  ·
                    refine ⟨2195962321272070677632185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2927949761696094236842913 2195962321272070677632185)
                    ·
                      refine ⟨1646971740954053008224139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2195962321272070677632185 1646971740954053008224139)
                      ·
                        rfl

theorem cell23_3207466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_3207466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207466 prefixEnd_3207466 := by exact prefixLift 3207466
  have htrace : WordTrace (prefixWord ++ tailWord_3207466) baseStart_3207466 baseEnd_3207466 := by
    simpa [prefixWord, tailWord_3207466, baseEnd_3207466] using wordTrace_append hprefix tailTrace_3207466
  have hstable : (prefixWord ++ tailWord_3207466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207466).length < 2 ^ (prefixWord ++ tailWord_3207466).sum := by decide
  have hdescent : baseEnd_3207466 < baseStart_3207466 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207475 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 3, 3, 2]
def baseStart_3207475 : Nat := 118140960795 + 3207475 * 2 ^ 59
def prefixEnd_3207475 : Nat := 4983230072969 + 3 ^ 40 * 3207475 * 2
def baseEnd_3207475 : Nat := 1646976362279943473011597

theorem tailTrace_3207475 : CollatzResearch.WordTrace tailWord_3207475 prefixEnd_3207475 1646976362279943473011597 := by
  unfold tailWord_3207475
  simp only [CollatzResearch.WordTrace]
  refine ⟨116986224054873342963071879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77990816036582228642047919 116986224054873342963071879)
  ·
    refine ⟨175479336082310014444607819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116986224054873342963071879 175479336082310014444607819)
    ·
      refine ⟨263219004123465021666911729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175479336082310014444607819 263219004123465021666911729)
      ·
        refine ⟨197414253092598766250183797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263219004123465021666911729 197414253092598766250183797)
        ·
          refine ⟨18507586227431134335954731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197414253092598766250183797 18507586227431134335954731)
          ·
            refine ⟨27761379341146701503932097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18507586227431134335954731 27761379341146701503932097)
            ·
              refine ⟨20821034505860026127949073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27761379341146701503932097 20821034505860026127949073)
              ·
                refine ⟨15615775879395019595961805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20821034505860026127949073 15615775879395019595961805)
                ·
                  refine ⟨5855915954773132348485677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15615775879395019595961805 5855915954773132348485677)
                  ·
                    refine ⟨2195968483039924630682129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5855915954773132348485677 2195968483039924630682129)
                    ·
                      refine ⟨1646976362279943473011597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2195968483039924630682129 1646976362279943473011597)
                      ·
                        rfl

theorem cell23_3207475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 3, 2].length) (baseStart_3207475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207475 prefixEnd_3207475 := by exact prefixLift 3207475
  have htrace : WordTrace (prefixWord ++ tailWord_3207475) baseStart_3207475 baseEnd_3207475 := by
    simpa [prefixWord, tailWord_3207475, baseEnd_3207475] using wordTrace_append hprefix tailTrace_3207475
  have hstable : (prefixWord ++ tailWord_3207475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207475).length < 2 ^ (prefixWord ++ tailWord_3207475).sum := by decide
  have hdescent : baseEnd_3207475 < baseStart_3207475 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207482 : List Nat := [3, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3]
def baseStart_3207482 : Nat := 118140960795 + 3207482 * 2 ^ 59
def prefixEnd_3207482 : Nat := 4983230072969 + 3 ^ 40 * 3207482 * 2
def baseEnd_3207482 : Nat := 1646979956644524945624065

theorem tailTrace_3207482 : CollatzResearch.WordTrace tailWord_3207482 prefixEnd_3207482 1646979956644524945624065 := by
  unfold tailWord_3207482
  simp only [CollatzResearch.WordTrace]
  refine ⟨29246619841461995789644175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 77990986243898655439051133 29246619841461995789644175)
  ·
    refine ⟨43869929762192993684466263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29246619841461995789644175 43869929762192993684466263)
    ·
      refine ⟨65804894643289490526699395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43869929762192993684466263 65804894643289490526699395)
      ·
        refine ⟨98707341964934235790049093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65804894643289490526699395 98707341964934235790049093)
        ·
          refine ⟨18507626618425169210634205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98707341964934235790049093 18507626618425169210634205)
          ·
            refine ⟨6940359981909438453987827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18507626618425169210634205 6940359981909438453987827)
            ·
              refine ⟨10410539972864157680981741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6940359981909438453987827 10410539972864157680981741)
              ·
                refine ⟨3903952489824059130368153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10410539972864157680981741 3903952489824059130368153)
                ·
                  refine ⟨2927964367368044347776115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3903952489824059130368153 2927964367368044347776115)
                  ·
                    refine ⟨4391946551052066521664173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2927964367368044347776115 4391946551052066521664173)
                    ·
                      refine ⟨1646979956644524945624065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4391946551052066521664173 1646979956644524945624065)
                      ·
                        rfl

theorem cell23_3207482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 3, 2, 1, 3].length) (baseStart_3207482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207482 prefixEnd_3207482 := by exact prefixLift 3207482
  have htrace : WordTrace (prefixWord ++ tailWord_3207482) baseStart_3207482 baseEnd_3207482 := by
    simpa [prefixWord, tailWord_3207482, baseEnd_3207482] using wordTrace_append hprefix tailTrace_3207482
  have hstable : (prefixWord ++ tailWord_3207482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207482).length < 2 ^ (prefixWord ++ tailWord_3207482).sum := by decide
  have hdescent : baseEnd_3207482 < baseStart_3207482 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207505 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 3, 4, 2]
def baseStart_3207505 : Nat := 118140960795 + 3207505 * 2 ^ 59
def prefixEnd_3207505 : Nat := 4983230072969 + 3 ^ 40 * 3207505 * 2
def baseEnd_3207505 : Nat := 1646991766699578355636459

theorem tailTrace_3207505 : CollatzResearch.WordTrace tailWord_3207505 prefixEnd_3207505 1646991766699578355636459 := by
  unfold tailWord_3207505
  simp only [CollatzResearch.WordTrace]
  refine ⟨116987318244764658086663969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77991545496509772057775979 116987318244764658086663969)
  ·
    refine ⟨87740488683573493564997977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116987318244764658086663969 87740488683573493564997977)
    ·
      refine ⟨65805366512680120173748483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87740488683573493564997977 65805366512680120173748483)
      ·
        refine ⟨98708049769020180260622725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65805366512680120173748483 98708049769020180260622725)
        ·
          refine ⟨18507759331691283798866761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98708049769020180260622725 18507759331691283798866761)
          ·
            refine ⟨13880819498768462849150071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18507759331691283798866761 13880819498768462849150071)
            ·
              refine ⟨20821229248152694273725107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13880819498768462849150071 20821229248152694273725107)
              ·
                refine ⟨31231843872229041410587661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20821229248152694273725107 31231843872229041410587661)
                ·
                  refine ⟨11711941452085890528970373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31231843872229041410587661 11711941452085890528970373)
                  ·
                    refine ⟨2195989022266104474181945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11711941452085890528970373 2195989022266104474181945)
                    ·
                      refine ⟨1646991766699578355636459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2195989022266104474181945 1646991766699578355636459)
                      ·
                        rfl

theorem cell23_3207505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 4, 2].length) (baseStart_3207505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207505 prefixEnd_3207505 := by exact prefixLift 3207505
  have htrace : WordTrace (prefixWord ++ tailWord_3207505) baseStart_3207505 baseEnd_3207505 := by
    simpa [prefixWord, tailWord_3207505, baseEnd_3207505] using wordTrace_append hprefix tailTrace_3207505
  have hstable : (prefixWord ++ tailWord_3207505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207505).length < 2 ^ (prefixWord ++ tailWord_3207505).sum := by decide
  have hdescent : baseEnd_3207505 < baseStart_3207505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207516 : List Nat := [2, 2, 4, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_3207516 : Nat := 118140960795 + 3207516 * 2 ^ 59
def prefixEnd_3207516 : Nat := 4983230072969 + 3 ^ 40 * 3207516 * 2
def baseEnd_3207516 : Nat := 1646997414986777812598909

theorem tailTrace_3207516 : CollatzResearch.WordTrace tailWord_3207516 prefixEnd_3207516 1646997414986777812598909 := by
  unfold tailWord_3207516
  simp only [CollatzResearch.WordTrace]
  refine ⟨58493859723862403482657201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77991812965149871310209601 58493859723862403482657201)
  ·
    refine ⟨43870394792896802611992901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58493859723862403482657201 43870394792896802611992901)
    ·
      refine ⟨8225699023668150489748669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43870394792896802611992901 8225699023668150489748669)
      ·
        refine ⟨3084637133875556433655751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8225699023668150489748669 3084637133875556433655751)
        ·
          refine ⟨4626955700813334650483627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3084637133875556433655751 4626955700813334650483627)
          ·
            refine ⟨6940433551220001975725441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4626955700813334650483627 6940433551220001975725441)
            ·
              refine ⟨5205325163415001481794081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6940433551220001975725441 5205325163415001481794081)
              ·
                refine ⟨3903993872561251111345561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5205325163415001481794081 3903993872561251111345561)
                ·
                  refine ⟨2927995404420938333509171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3903993872561251111345561 2927995404420938333509171)
                  ·
                    refine ⟨4391993106631407500263757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2927995404420938333509171 4391993106631407500263757)
                    ·
                      refine ⟨1646997414986777812598909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4391993106631407500263757 1646997414986777812598909)
                      ·
                        rfl

theorem cell23_3207516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_3207516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207516 prefixEnd_3207516 := by exact prefixLift 3207516
  have htrace : WordTrace (prefixWord ++ tailWord_3207516) baseStart_3207516 baseEnd_3207516 := by
    simpa [prefixWord, tailWord_3207516, baseEnd_3207516] using wordTrace_append hprefix tailTrace_3207516
  have hstable : (prefixWord ++ tailWord_3207516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207516).length < 2 ^ (prefixWord ++ tailWord_3207516).sum := by decide
  have hdescent : baseEnd_3207516 < baseStart_3207516 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207608 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 1, 6, 4]
def baseStart_3207608 : Nat := 118140960795 + 3207608 * 2 ^ 59
def prefixEnd_3207608 : Nat := 4983230072969 + 3 ^ 40 * 3207608 * 2
def baseEnd_3207608 : Nat := 1647044655206991452648485

theorem tailTrace_3207608 : CollatzResearch.WordTrace tailWord_3207608 prefixEnd_3207608 1647044655206991452648485 := by
  unfold tailWord_3207608
  simp only [CollatzResearch.WordTrace]
  refine ⟨58495537481695753338831739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 77994049975594337785108985 58495537481695753338831739)
  ·
    refine ⟨87743306222543630008247609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58495537481695753338831739 87743306222543630008247609)
    ·
      refine ⟨65807479666907722506185707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87743306222543630008247609 65807479666907722506185707)
      ·
        refine ⟨98711219500361583759278561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65807479666907722506185707 98711219500361583759278561)
        ·
          refine ⟨74033414625271187819458921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98711219500361583759278561 74033414625271187819458921)
          ·
            refine ⟨55525060968953390864594191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74033414625271187819458921 55525060968953390864594191)
            ·
              refine ⟨83287591453430086296891287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55525060968953390864594191 83287591453430086296891287)
              ·
                refine ⟨124931387180145129445336931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83287591453430086296891287 124931387180145129445336931)
                ·
                  refine ⟨187397080770217694168005397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 124931387180145129445336931 187397080770217694168005397)
                  ·
                    refine ⟨8784238161103954414125253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 187397080770217694168005397 8784238161103954414125253)
                    ·
                      refine ⟨1647044655206991452648485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8784238161103954414125253 1647044655206991452648485)
                      ·
                        rfl

theorem cell23_3207608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 1, 6, 4].length) (baseStart_3207608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207608 prefixEnd_3207608 := by exact prefixLift 3207608
  have htrace : WordTrace (prefixWord ++ tailWord_3207608) baseStart_3207608 baseEnd_3207608 := by
    simpa [prefixWord, tailWord_3207608, baseEnd_3207608] using wordTrace_append hprefix tailTrace_3207608
  have hstable : (prefixWord ++ tailWord_3207608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207608).length < 2 ^ (prefixWord ++ tailWord_3207608).sum := by decide
  have hdescent : baseEnd_3207608 < baseStart_3207608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207665 : List Nat := [1, 2, 2, 2, 3, 1, 3, 1, 3, 5]
def baseStart_3207665 : Nat := 118140960795 + 3207665 * 2 ^ 59
def prefixEnd_3207665 : Nat := 4983230072969 + 3 ^ 40 * 3207665 * 2
def baseEnd_3207665 : Nat := 549024641201432576545241

theorem tailTrace_3207665 : CollatzResearch.WordTrace tailWord_3207665 prefixEnd_3207665 549024641201432576545241 := by
  unfold tailWord_3207665
  simp only [CollatzResearch.WordTrace]
  refine ⟨116993153924185005412488449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77995435949456670274992299 116993153924185005412488449)
  ·
    refine ⟨87744865443138754059366337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 116993153924185005412488449 87744865443138754059366337)
    ·
      refine ⟨65808649082354065544524753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87744865443138754059366337 65808649082354065544524753)
      ·
        refine ⟨49356486811765549158393565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65808649082354065544524753 49356486811765549158393565)
        ·
          refine ⟨18508682554412080934397587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49356486811765549158393565 18508682554412080934397587)
          ·
            refine ⟨27763023831618121401596381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18508682554412080934397587 27763023831618121401596381)
            ·
              refine ⟨10411133936856795525598643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27763023831618121401596381 10411133936856795525598643)
              ·
                refine ⟨15616700905285193288397965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10411133936856795525598643 15616700905285193288397965)
                ·
                  refine ⟨5856262839481947483149237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15616700905285193288397965 5856262839481947483149237)
                  ·
                    refine ⟨549024641201432576545241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5856262839481947483149237 549024641201432576545241)
                    ·
                      rfl

theorem cell23_3207665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 3, 5].length) (baseStart_3207665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207665 prefixEnd_3207665 := by exact prefixLift 3207665
  have htrace : WordTrace (prefixWord ++ tailWord_3207665) baseStart_3207665 baseEnd_3207665 := by
    simpa [prefixWord, tailWord_3207665, baseEnd_3207665] using wordTrace_append hprefix tailTrace_3207665
  have hstable : (prefixWord ++ tailWord_3207665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207665).length < 2 ^ (prefixWord ++ tailWord_3207665).sum := by decide
  have hdescent : baseEnd_3207665 < baseStart_3207665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207679 : List Nat := [1, 1, 2, 2, 1, 2, 4, 5, 1, 1, 3]
def baseStart_3207679 : Nat := 118140960795 + 3207679 * 2 ^ 59
def prefixEnd_3207679 : Nat := 4983230072969 + 3 ^ 40 * 3207679 * 2
def baseEnd_3207679 : Nat := 1647081112333460674860659

theorem tailTrace_3207679 : CollatzResearch.WordTrace tailWord_3207679 prefixEnd_3207679 1647081112333460674860659 := by
  unfold tailWord_3207679
  simp only [CollatzResearch.WordTrace]
  refine ⟨116993664546134285803498091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77995776364089523868998727 116993664546134285803498091)
  ·
    refine ⟨175490496819201428705247137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116993664546134285803498091 175490496819201428705247137)
    ·
      refine ⟨131617872614401071528935353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175490496819201428705247137 131617872614401071528935353)
      ·
        refine ⟨98713404460800803646701515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131617872614401071528935353 98713404460800803646701515)
        ·
          refine ⟨148070106691201205470052273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98713404460800803646701515 148070106691201205470052273)
          ·
            refine ⟨111052580018400904102539205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148070106691201205470052273 111052580018400904102539205)
            ·
              refine ⟨20822358753450169519226101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 111052580018400904102539205 20822358753450169519226101)
              ·
                refine ⟨1952096133135953392427447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20822358753450169519226101 1952096133135953392427447)
                ·
                  refine ⟨2928144199703930088641171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1952096133135953392427447 2928144199703930088641171)
                  ·
                    refine ⟨4392216299555895132961757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2928144199703930088641171 4392216299555895132961757)
                    ·
                      refine ⟨1647081112333460674860659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4392216299555895132961757 1647081112333460674860659)
                      ·
                        rfl

theorem cell23_3207679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 5, 1, 1, 3].length) (baseStart_3207679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207679 prefixEnd_3207679 := by exact prefixLift 3207679
  have htrace : WordTrace (prefixWord ++ tailWord_3207679) baseStart_3207679 baseEnd_3207679 := by
    simpa [prefixWord, tailWord_3207679, baseEnd_3207679] using wordTrace_append hprefix tailTrace_3207679
  have hstable : (prefixWord ++ tailWord_3207679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207679).length < 2 ^ (prefixWord ++ tailWord_3207679).sum := by decide
  have hdescent : baseEnd_3207679 < baseStart_3207679 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207686 : List Nat := [6, 2, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3207686 : Nat := 118140960795 + 3207686 * 2 ^ 59
def prefixEnd_3207686 : Nat := 4983230072969 + 3 ^ 40 * 3207686 * 2
def baseEnd_3207686 : Nat := 183009411855338016385903

theorem tailTrace_3207686 : CollatzResearch.WordTrace tailWord_3207686 prefixEnd_3207686 183009411855338016385903 := by
  unfold tailWord_3207686
  simp only [CollatzResearch.WordTrace]
  refine ⟨3656059995534653937468841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 77995946571405950666001941 3656059995534653937468841)
  ·
    refine ⟨2742044996650990453101631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3656059995534653937468841 2742044996650990453101631)
    ·
      refine ⟨4113067494976485679652447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2742044996650990453101631 4113067494976485679652447)
      ·
        refine ⟨6169601242464728519478671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4113067494976485679652447 6169601242464728519478671)
        ·
          refine ⟨9254401863697092779218007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6169601242464728519478671 9254401863697092779218007)
          ·
            refine ⟨13881602795545639168827011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9254401863697092779218007 13881602795545639168827011)
            ·
              refine ⟨20822404193318458753240517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13881602795545639168827011 20822404193318458753240517)
              ·
                refine ⟨3904200786247211016232597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20822404193318458753240517 3904200786247211016232597)
                ·
                  refine ⟨183009411855338016385903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3904200786247211016232597 183009411855338016385903)
                  ·
                    rfl

theorem cell23_3207686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3207686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207686 prefixEnd_3207686 := by exact prefixLift 3207686
  have htrace : WordTrace (prefixWord ++ tailWord_3207686) baseStart_3207686 baseEnd_3207686 := by
    simpa [prefixWord, tailWord_3207686, baseEnd_3207686] using wordTrace_append hprefix tailTrace_3207686
  have hstable : (prefixWord ++ tailWord_3207686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207686).length < 2 ^ (prefixWord ++ tailWord_3207686).sum := by decide
  have hdescent : baseEnd_3207686 < baseStart_3207686 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207775 : List Nat := [1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 4]
def baseStart_3207775 : Nat := 118140960795 + 3207775 * 2 ^ 59
def prefixEnd_3207775 : Nat := 4983230072969 + 3 ^ 40 * 3207775 * 2
def baseEnd_3207775 : Nat := 1647130406476292299260217

theorem tailTrace_3207775 : CollatzResearch.WordTrace tailWord_3207775 prefixEnd_3207775 1647130406476292299260217 := by
  unfold tailWord_3207775
  simp only [CollatzResearch.WordTrace]
  refine ⟨116997165953786494198992779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 77998110635857662799328519 116997165953786494198992779)
  ·
    refine ⟨175495748930679741298489169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 116997165953786494198992779 175495748930679741298489169)
    ·
      refine ⟨131621811698009805973866877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175495748930679741298489169 131621811698009805973866877)
      ·
        refine ⟨49358179386753677240200079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131621811698009805973866877 49358179386753677240200079)
        ·
          refine ⟨74037269080130515860300119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49358179386753677240200079 74037269080130515860300119)
          ·
            refine ⟨111055903620195773790450179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74037269080130515860300119 111055903620195773790450179)
            ·
              refine ⟨166583855430293660685675269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111055903620195773790450179 166583855430293660685675269)
              ·
                refine ⟨31234472893180061378564113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166583855430293660685675269 31234472893180061378564113)
                ·
                  refine ⟨23425854669885046033923085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31234472893180061378564113 23425854669885046033923085)
                  ·
                    refine ⟨8784695501206892262721157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23425854669885046033923085 8784695501206892262721157)
                    ·
                      refine ⟨1647130406476292299260217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8784695501206892262721157 1647130406476292299260217)
                      ·
                        rfl

theorem cell23_3207775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 4].length) (baseStart_3207775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207775 prefixEnd_3207775 := by exact prefixLift 3207775
  have htrace : WordTrace (prefixWord ++ tailWord_3207775) baseStart_3207775 baseEnd_3207775 := by
    simpa [prefixWord, tailWord_3207775, baseEnd_3207775] using wordTrace_append hprefix tailTrace_3207775
  have hstable : (prefixWord ++ tailWord_3207775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207775).length < 2 ^ (prefixWord ++ tailWord_3207775).sum := by decide
  have hdescent : baseEnd_3207775 < baseStart_3207775 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207822 : List Nat := [4, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4]
def baseStart_3207822 : Nat := 118140960795 + 3207822 * 2 ^ 59
def prefixEnd_3207822 : Nat := 4983230072969 + 3 ^ 40 * 3207822 * 2
def baseEnd_3207822 : Nat := 1647154540067053615372501

theorem tailTrace_3207822 : CollatzResearch.WordTrace tailWord_3207822 prefixEnd_3207822 1647154540067053615372501 := by
  unfold tailWord_3207822
  simp only [CollatzResearch.WordTrace]
  refine ⟨14624860023077027653244215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 77999253456410814150635813 14624860023077027653244215)
  ·
    refine ⟨21937290034615541479866323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14624860023077027653244215 21937290034615541479866323)
    ·
      refine ⟨32905935051923312219799485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21937290034615541479866323 32905935051923312219799485)
      ·
        refine ⟨12339725644471242082424807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32905935051923312219799485 12339725644471242082424807)
        ·
          refine ⟨18509588466706863123637211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12339725644471242082424807 18509588466706863123637211)
          ·
            refine ⟨27764382700060294685455817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18509588466706863123637211 27764382700060294685455817)
            ·
              refine ⟨20823287025045221014091863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27764382700060294685455817 20823287025045221014091863)
              ·
                refine ⟨31234930537567831521137795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20823287025045221014091863 31234930537567831521137795)
                ·
                  refine ⟨46852395806351747281706693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31234930537567831521137795 46852395806351747281706693)
                  ·
                    refine ⟨8784824213690952615320005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46852395806351747281706693 8784824213690952615320005)
                    ·
                      refine ⟨1647154540067053615372501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8784824213690952615320005 1647154540067053615372501)
                      ·
                        rfl

theorem cell23_3207822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_3207822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207822 prefixEnd_3207822 := by exact prefixLift 3207822
  have htrace : WordTrace (prefixWord ++ tailWord_3207822) baseStart_3207822 baseEnd_3207822 := by
    simpa [prefixWord, tailWord_3207822, baseEnd_3207822] using wordTrace_append hprefix tailTrace_3207822
  have hstable : (prefixWord ++ tailWord_3207822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207822).length < 2 ^ (prefixWord ++ tailWord_3207822).sum := by decide
  have hdescent : baseEnd_3207822 < baseStart_3207822 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207869 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 2, 5, 2]
def baseStart_3207869 : Nat := 118140960795 + 3207869 * 2 ^ 59
def prefixEnd_3207869 : Nat := 4983230072969 + 3 ^ 40 * 3207869 * 2
def baseEnd_3207869 : Nat := 1647178673657814931484785

theorem tailTrace_3207869 : CollatzResearch.WordTrace tailWord_3207869 prefixEnd_3207869 1647178673657814931484785 := by
  unfold tailWord_3207869
  simp only [CollatzResearch.WordTrace]
  refine ⟨117000594415445948252914661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78000396276963965501943107 117000594415445948252914661)
  ·
    refine ⟨21937611452896115297421499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117000594415445948252914661 21937611452896115297421499)
    ·
      refine ⟨32906417179344172946132249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21937611452896115297421499 32906417179344172946132249)
      ·
        refine ⟨24679812884508129709599187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32906417179344172946132249 24679812884508129709599187)
        ·
          refine ⟨37019719326762194564398781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24679812884508129709599187 37019719326762194564398781)
          ·
            refine ⟨13882394747535822961649543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37019719326762194564398781 13882394747535822961649543)
            ·
              refine ⟨20823592121303734442474315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13882394747535822961649543 20823592121303734442474315)
              ·
                refine ⟨31235388181955601663711473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20823592121303734442474315 31235388181955601663711473)
                ·
                  refine ⟨23426541136466701247783605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31235388181955601663711473 23426541136466701247783605)
                  ·
                    refine ⟨2196238231543753241979713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23426541136466701247783605 2196238231543753241979713)
                    ·
                      refine ⟨1647178673657814931484785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2196238231543753241979713 1647178673657814931484785)
                      ·
                        rfl

theorem cell23_3207869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 5, 2].length) (baseStart_3207869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207869 prefixEnd_3207869 := by exact prefixLift 3207869
  have htrace : WordTrace (prefixWord ++ tailWord_3207869) baseStart_3207869 baseEnd_3207869 := by
    simpa [prefixWord, tailWord_3207869, baseEnd_3207869] using wordTrace_append hprefix tailTrace_3207869
  have hstable : (prefixWord ++ tailWord_3207869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207869).length < 2 ^ (prefixWord ++ tailWord_3207869).sum := by decide
  have hdescent : baseEnd_3207869 < baseStart_3207869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207872 : List Nat := [2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 5]
def baseStart_3207872 : Nat := 118140960795 + 3207872 * 2 ^ 59
def prefixEnd_3207872 : Nat := 4983230072969 + 3 ^ 40 * 3207872 * 2
def baseEnd_3207872 : Nat := 1647180214099778419747271

theorem tailTrace_3207872 : CollatzResearch.WordTrace tailWord_3207872 prefixEnd_3207872 1647180214099778419747271 := by
  unfold tailWord_3207872
  simp only [CollatzResearch.WordTrace]
  refine ⟨58500351917217539882636935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78000469222956719843515913 58500351917217539882636935)
  ·
    refine ⟨87750527875826309823955403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58500351917217539882636935 87750527875826309823955403)
    ·
      refine ⟨131625791813739464735933105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87750527875826309823955403 131625791813739464735933105)
      ·
        refine ⟨98719343860304598551949829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131625791813739464735933105 98719343860304598551949829)
        ·
          refine ⟨18509876973807112228490593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98719343860304598551949829 18509876973807112228490593)
          ·
            refine ⟨13882407730355334171367945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18509876973807112228490593 13882407730355334171367945)
            ·
              refine ⟨10411805797766500628525959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13882407730355334171367945 10411805797766500628525959)
              ·
                refine ⟨15617708696649750942788939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10411805797766500628525959 15617708696649750942788939)
                ·
                  refine ⟨23426563044974626414183409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15617708696649750942788939 23426563044974626414183409)
                  ·
                    refine ⟨17569922283730969810637557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23426563044974626414183409 17569922283730969810637557)
                    ·
                      refine ⟨1647180214099778419747271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17569922283730969810637557 1647180214099778419747271)
                      ·
                        rfl

theorem cell23_3207872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 5].length) (baseStart_3207872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207872 prefixEnd_3207872 := by exact prefixLift 3207872
  have htrace : WordTrace (prefixWord ++ tailWord_3207872) baseStart_3207872 baseEnd_3207872 := by
    simpa [prefixWord, tailWord_3207872, baseEnd_3207872] using wordTrace_append hprefix tailTrace_3207872
  have hstable : (prefixWord ++ tailWord_3207872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207872).length < 2 ^ (prefixWord ++ tailWord_3207872).sum := by decide
  have hdescent : baseEnd_3207872 < baseStart_3207872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207926 : List Nat := [5, 1, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_3207926 : Nat := 118140960795 + 3207926 * 2 ^ 59
def prefixEnd_3207926 : Nat := 4983230072969 + 3 ^ 40 * 3207926 * 2
def baseEnd_3207926 : Nat := 549069314018373736157341

theorem tailTrace_3207926 : CollatzResearch.WordTrace tailWord_3207926 prefixEnd_3207926 549069314018373736157341 := by
  unfold tailWord_3207926
  simp only [CollatzResearch.WordTrace]
  refine ⟨7312667086014965436733727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78001782250826297991826421 7312667086014965436733727)
  ·
    refine ⟨10969000629022448155100591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7312667086014965436733727 10969000629022448155100591)
    ·
      refine ⟨16453500943533672232650887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10969000629022448155100591 16453500943533672232650887)
      ·
        refine ⟨24680251415300508348976331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16453500943533672232650887 24680251415300508348976331)
        ·
          refine ⟨37020377122950762523464497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24680251415300508348976331 37020377122950762523464497)
          ·
            refine ⟨27765282842213071892598373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37020377122950762523464497 27765282842213071892598373)
            ·
              refine ⟨5205990532914950979862195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27765282842213071892598373 5205990532914950979862195)
              ·
                refine ⟨7808985799372426469793293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5205990532914950979862195 7808985799372426469793293)
                ·
                  refine ⟨2928369674764659926172485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7808985799372426469793293 2928369674764659926172485)
                  ·
                    refine ⟨549069314018373736157341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2928369674764659926172485 549069314018373736157341)
                    ·
                      rfl

theorem cell23_3207926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_3207926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207926 prefixEnd_3207926 := by exact prefixLift 3207926
  have htrace : WordTrace (prefixWord ++ tailWord_3207926) baseStart_3207926 baseEnd_3207926 := by
    simpa [prefixWord, tailWord_3207926, baseEnd_3207926] using wordTrace_append hprefix tailTrace_3207926
  have hstable : (prefixWord ++ tailWord_3207926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207926).length < 2 ^ (prefixWord ++ tailWord_3207926).sum := by decide
  have hdescent : baseEnd_3207926 < baseStart_3207926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207969 : List Nat := [1, 2, 3, 2, 1, 2, 1, 5, 1, 5]
def baseStart_3207969 : Nat := 118140960795 + 3207969 * 2 ^ 59
def prefixEnd_3207969 : Nat := 4983230072969 + 3 ^ 40 * 3207969 * 2
def baseEnd_3207969 : Nat := 549076673907754846744775

theorem tailTrace_3207969 : CollatzResearch.WordTrace tailWord_3207969 prefixEnd_3207969 549076673907754846744775 := by
  unfold tailWord_3207969
  simp only [CollatzResearch.WordTrace]
  refine ⟨117004241715083665331554961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78002827810055776887703307 117004241715083665331554961)
  ·
    refine ⟨87753181286312748998666221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117004241715083665331554961 87753181286312748998666221)
    ·
      refine ⟨32907442982367280874499833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87753181286312748998666221 32907442982367280874499833)
      ·
        refine ⟨24680582236775460655874875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32907442982367280874499833 24680582236775460655874875)
        ·
          refine ⟨37020873355163190983812313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24680582236775460655874875 37020873355163190983812313)
          ·
            refine ⟨27765655016372393237859235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37020873355163190983812313 27765655016372393237859235)
            ·
              refine ⟨41648482524558589856788853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27765655016372393237859235 41648482524558589856788853)
              ·
                refine ⟨3904545236677367799073955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41648482524558589856788853 3904545236677367799073955)
                ·
                  refine ⟨5856817855016051698610933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3904545236677367799073955 5856817855016051698610933)
                  ·
                    refine ⟨549076673907754846744775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5856817855016051698610933 549076673907754846744775)
                    ·
                      rfl

theorem cell23_3207969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 5].length) (baseStart_3207969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207969 prefixEnd_3207969 := by exact prefixLift 3207969
  have htrace : WordTrace (prefixWord ++ tailWord_3207969) baseStart_3207969 baseEnd_3207969 := by
    simpa [prefixWord, tailWord_3207969, baseEnd_3207969] using wordTrace_append hprefix tailTrace_3207969
  have hstable : (prefixWord ++ tailWord_3207969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207969).length < 2 ^ (prefixWord ++ tailWord_3207969).sum := by decide
  have hdescent : baseEnd_3207969 < baseStart_3207969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3207990 : List Nat := [5, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_3207990 : Nat := 118140960795 + 3207990 * 2 ^ 59
def prefixEnd_3207990 : Nat := 4983230072969 + 3 ^ 40 * 3207990 * 2
def baseEnd_3207990 : Nat := 183026756090778773119081

theorem tailTrace_3207990 : CollatzResearch.WordTrace tailWord_3207990 prefixEnd_3207990 183026756090778773119081 := by
  unfold tailWord_3207990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7312812978000474119879339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78003338432005057278712949 7312812978000474119879339)
  ·
    refine ⟨10969219467000711179819009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7312812978000474119879339 10969219467000711179819009)
    ·
      refine ⟨8226914600250533384864257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10969219467000711179819009 8226914600250533384864257)
      ·
        refine ⟨6170185950187900038648193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8226914600250533384864257 6170185950187900038648193)
        ·
          refine ⟨4627639462640925028986145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6170185950187900038648193 4627639462640925028986145)
          ·
            refine ⟨3470729596980693771739609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4627639462640925028986145 3470729596980693771739609)
            ·
              refine ⟨2603047197735520328804707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3470729596980693771739609 2603047197735520328804707)
              ·
                refine ⟨3904570796603280493207061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603047197735520328804707 3904570796603280493207061)
                ·
                  refine ⟨183026756090778773119081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3904570796603280493207061 183026756090778773119081)
                  ·
                    rfl

theorem cell23_3207990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_3207990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3207990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3207990 prefixEnd_3207990 := by exact prefixLift 3207990
  have htrace : WordTrace (prefixWord ++ tailWord_3207990) baseStart_3207990 baseEnd_3207990 := by
    simpa [prefixWord, tailWord_3207990, baseEnd_3207990] using wordTrace_append hprefix tailTrace_3207990
  have hstable : (prefixWord ++ tailWord_3207990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3207990).length < 2 ^ (prefixWord ++ tailWord_3207990).sum := by decide
  have hdescent : baseEnd_3207990 < baseStart_3207990 := by decide
  rcases family_descends (prefixWord ++ tailWord_3207990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208023 : List Nat := [1, 1, 3, 2, 4, 2, 3, 1, 1, 1, 4]
def baseStart_3208023 : Nat := 118140960795 + 3208023 * 2 ^ 59
def prefixEnd_3208023 : Nat := 4983230072969 + 3 ^ 40 * 3208023 * 2
def baseEnd_3208023 : Nat := 1647257749678607328959077

theorem tailTrace_3208023 : CollatzResearch.WordTrace tailWord_3208023 prefixEnd_3208023 1647257749678607328959077 := by
  unfold tailWord_3208023
  simp only [CollatzResearch.WordTrace]
  refine ⟨117006211256888032554020723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78004140837925355036013815 117006211256888032554020723)
  ·
    refine ⟨175509316885332048831031085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117006211256888032554020723 175509316885332048831031085)
    ·
      refine ⟨65815993831999518311636657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175509316885332048831031085 65815993831999518311636657)
      ·
        refine ⟨49361995373999638733727493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65815993831999518311636657 49361995373999638733727493)
        ·
          refine ⟨9255374132624932262573905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 49361995373999638733727493 9255374132624932262573905)
          ·
            refine ⟨6941530599468699196930429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9255374132624932262573905 6941530599468699196930429)
            ·
              refine ⟨2603073974800762198848911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6941530599468699196930429 2603073974800762198848911)
              ·
                refine ⟨3904610962201143298273367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603073974800762198848911 3904610962201143298273367)
                ·
                  refine ⟨5856916443301714947410051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3904610962201143298273367 5856916443301714947410051)
                  ·
                    refine ⟨8785374664952572421115077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5856916443301714947410051 8785374664952572421115077)
                    ·
                      refine ⟨1647257749678607328959077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8785374664952572421115077 1647257749678607328959077)
                      ·
                        rfl

theorem cell23_3208023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_3208023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208023 prefixEnd_3208023 := by exact prefixLift 3208023
  have htrace : WordTrace (prefixWord ++ tailWord_3208023) baseStart_3208023 baseEnd_3208023 := by
    simpa [prefixWord, tailWord_3208023, baseEnd_3208023] using wordTrace_append hprefix tailTrace_3208023
  have hstable : (prefixWord ++ tailWord_3208023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208023).length < 2 ^ (prefixWord ++ tailWord_3208023).sum := by decide
  have hdescent : baseEnd_3208023 < baseStart_3208023 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208026 : List Nat := [3, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5]
def baseStart_3208026 : Nat := 118140960795 + 3208026 * 2 ^ 59
def prefixEnd_3208026 : Nat := 4983230072969 + 3 ^ 40 * 3208026 * 2
def baseEnd_3208026 : Nat := 1647259290120570817221563

theorem tailTrace_3208026 : CollatzResearch.WordTrace tailWord_3208026 prefixEnd_3208026 1647259290120570817221563 := by
  unfold tailWord_3208026
  simp only [CollatzResearch.WordTrace]
  refine ⟨29251580168969291016594983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78004213783918109377586621 29251580168969291016594983)
  ·
    refine ⟨43877370253453936524892475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29251580168969291016594983 43877370253453936524892475)
    ·
      refine ⟨65816055380180904787338713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43877370253453936524892475 65816055380180904787338713)
      ·
        refine ⟨49362041535135678590504035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65816055380180904787338713 49362041535135678590504035)
        ·
          refine ⟨74043062302703517885756053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49362041535135678590504035 74043062302703517885756053)
          ·
            refine ⟨3470768545439227400894815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 74043062302703517885756053 3470768545439227400894815)
            ·
              refine ⟨5206152818158841101342223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3470768545439227400894815 5206152818158841101342223)
              ·
                refine ⟨7809229227238261652013335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206152818158841101342223 7809229227238261652013335)
                ·
                  refine ⟨11713843840857392478020003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7809229227238261652013335 11713843840857392478020003)
                  ·
                    refine ⟨17570765761286088717030005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11713843840857392478020003 17570765761286088717030005)
                    ·
                      refine ⟨1647259290120570817221563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17570765761286088717030005 1647259290120570817221563)
                      ·
                        rfl

theorem cell23_3208026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 1, 1, 1, 1, 5].length) (baseStart_3208026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208026 prefixEnd_3208026 := by exact prefixLift 3208026
  have htrace : WordTrace (prefixWord ++ tailWord_3208026) baseStart_3208026 baseEnd_3208026 := by
    simpa [prefixWord, tailWord_3208026, baseEnd_3208026] using wordTrace_append hprefix tailTrace_3208026
  have hstable : (prefixWord ++ tailWord_3208026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208026).length < 2 ^ (prefixWord ++ tailWord_3208026).sum := by decide
  have hdescent : baseEnd_3208026 < baseStart_3208026 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208034 : List Nat := [3, 3, 2, 1, 3, 2, 2, 2, 1, 1, 3]
def baseStart_3208034 : Nat := 118140960795 + 3208034 * 2 ^ 59
def prefixEnd_3208034 : Nat := 4983230072969 + 3 ^ 40 * 3208034 * 2
def baseEnd_3208034 : Nat := 1647263397965806785921527

theorem tailTrace_3208034 : CollatzResearch.WordTrace tailWord_3208034 prefixEnd_3208034 1647263397965806785921527 := by
  unfold tailWord_3208034
  simp only [CollatzResearch.WordTrace]
  refine ⟨29251653114962045358167789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78004408306565454288447437 29251653114962045358167789)
  ·
    refine ⟨10969369918110767009312921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29251653114962045358167789 10969369918110767009312921)
    ·
      refine ⟨8227027438583075256984691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10969369918110767009312921 8227027438583075256984691)
      ·
        refine ⟨12340541157874612885477037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8227027438583075256984691 12340541157874612885477037)
        ·
          refine ⟨4627702934202979832053889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12340541157874612885477037 4627702934202979832053889)
          ·
            refine ⟨3470777200652234874040417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4627702934202979832053889 3470777200652234874040417)
            ·
              refine ⟨2603082900489176155530313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3470777200652234874040417 2603082900489176155530313)
              ·
                refine ⟨1952312175366882116647735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2603082900489176155530313 1952312175366882116647735)
                ·
                  refine ⟨2928468263050323174971603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1952312175366882116647735 2928468263050323174971603)
                  ·
                    refine ⟨4392702394575484762457405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2928468263050323174971603 4392702394575484762457405)
                    ·
                      refine ⟨1647263397965806785921527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4392702394575484762457405 1647263397965806785921527)
                      ·
                        rfl

theorem cell23_3208034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_3208034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208034 prefixEnd_3208034 := by exact prefixLift 3208034
  have htrace : WordTrace (prefixWord ++ tailWord_3208034) baseStart_3208034 baseEnd_3208034 := by
    simpa [prefixWord, tailWord_3208034, baseEnd_3208034] using wordTrace_append hprefix tailTrace_3208034
  have hstable : (prefixWord ++ tailWord_3208034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208034).length < 2 ^ (prefixWord ++ tailWord_3208034).sum := by decide
  have hdescent : baseEnd_3208034 < baseStart_3208034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208096 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 3, 4, 2]
def baseStart_3208096 : Nat := 118140960795 + 3208096 * 2 ^ 59
def prefixEnd_3208096 : Nat := 4983230072969 + 3 ^ 40 * 3208096 * 2
def baseEnd_3208096 : Nat := 1647295233766385543346241

theorem tailTrace_3208096 : CollatzResearch.WordTrace tailWord_3208096 prefixEnd_3208096 1647295233766385543346241 := by
  unfold tailWord_3208096
  simp only [CollatzResearch.WordTrace]
  refine ⟨58504436892811783010714071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78005915857082377347618761 58504436892811783010714071)
  ·
    refine ⟨87756655339217674516071107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58504436892811783010714071 87756655339217674516071107)
    ·
      refine ⟨131634983008826511774106661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87756655339217674516071107 131634983008826511774106661)
      ·
        refine ⟨24681559314154970957644999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131634983008826511774106661 24681559314154970957644999)
        ·
          refine ⟨37022338971232456436467499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24681559314154970957644999 37022338971232456436467499)
          ·
            refine ⟨55533508456848684654701249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37022338971232456436467499 55533508456848684654701249)
            ·
              refine ⟨41650131342636513491025937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55533508456848684654701249 41650131342636513491025937)
              ·
                refine ⟨31237598506977385118269453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41650131342636513491025937 31237598506977385118269453)
                ·
                  refine ⟨11714099440116519419351045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31237598506977385118269453 11714099440116519419351045)
                  ·
                    refine ⟨2196393645021847391128321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11714099440116519419351045 2196393645021847391128321)
                    ·
                      refine ⟨1647295233766385543346241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2196393645021847391128321 1647295233766385543346241)
                      ·
                        rfl

theorem cell23_3208096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 3, 4, 2].length) (baseStart_3208096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208096 prefixEnd_3208096 := by exact prefixLift 3208096
  have htrace : WordTrace (prefixWord ++ tailWord_3208096) baseStart_3208096 baseEnd_3208096 := by
    simpa [prefixWord, tailWord_3208096, baseEnd_3208096] using wordTrace_append hprefix tailTrace_3208096
  have hstable : (prefixWord ++ tailWord_3208096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208096).length < 2 ^ (prefixWord ++ tailWord_3208096).sum := by decide
  have hdescent : baseEnd_3208096 < baseStart_3208096 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208099 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 3]
def baseStart_3208099 : Nat := 118140960795 + 3208099 * 2 ^ 59
def prefixEnd_3208099 : Nat := 4983230072969 + 3 ^ 40 * 3208099 * 2
def baseEnd_3208099 : Nat := 1647296774208349031608727

theorem tailTrace_3208099 : CollatzResearch.WordTrace tailWord_3208099 prefixEnd_3208099 1647296774208349031608727 := by
  unfold tailWord_3208099
  simp only [CollatzResearch.WordTrace]
  refine ⟨117008983204612697533787351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78005988803075131689191567 117008983204612697533787351)
  ·
    refine ⟨175513474806919046300681027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117008983204612697533787351 175513474806919046300681027)
    ·
      refine ⟨263270212210378569451021541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175513474806919046300681027 263270212210378569451021541)
      ·
        refine ⟨49363164789445981772066539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 263270212210378569451021541 49363164789445981772066539)
        ·
          refine ⟨74044747184168972658099809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49363164789445981772066539 74044747184168972658099809)
          ·
            refine ⟨55533560388126729493574857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74044747184168972658099809 55533560388126729493574857)
            ·
              refine ⟨41650170291095047120181143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55533560388126729493574857 41650170291095047120181143)
              ·
                refine ⟨62475255436642570680271715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41650170291095047120181143 62475255436642570680271715)
                ·
                  refine ⟨93712883154963856020407573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 62475255436642570680271715 93712883154963856020407573)
                  ·
                    refine ⟨4392791397888930750956605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 93712883154963856020407573 4392791397888930750956605)
                    ·
                      refine ⟨1647296774208349031608727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4392791397888930750956605 1647296774208349031608727)
                      ·
                        rfl

theorem cell23_3208099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 1, 6, 3].length) (baseStart_3208099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208099 prefixEnd_3208099 := by exact prefixLift 3208099
  have htrace : WordTrace (prefixWord ++ tailWord_3208099) baseStart_3208099 baseEnd_3208099 := by
    simpa [prefixWord, tailWord_3208099, baseEnd_3208099] using wordTrace_append hprefix tailTrace_3208099
  have hstable : (prefixWord ++ tailWord_3208099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208099).length < 2 ^ (prefixWord ++ tailWord_3208099).sum := by decide
  have hdescent : baseEnd_3208099 < baseStart_3208099 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208119 : List Nat := [1, 1, 3, 1, 3, 1, 4, 2, 7]
def baseStart_3208119 : Nat := 118140960795 + 3208119 * 2 ^ 59
def prefixEnd_3208119 : Nat := 4983230072969 + 3 ^ 40 * 3208119 * 2
def baseEnd_3208119 : Nat := 183034115980159883706515

theorem tailTrace_3208119 : CollatzResearch.WordTrace tailWord_3208119 prefixEnd_3208119 183034115980159883706515 := by
  unfold tailWord_3208119
  simp only [CollatzResearch.WordTrace]
  refine ⟨117009712664540240949515411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78006475109693493966343607 117009712664540240949515411)
  ·
    refine ⟨175514568996810361424273117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117009712664540240949515411 175514568996810361424273117)
    ·
      refine ⟨65817963373803885534102419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175514568996810361424273117 65817963373803885534102419)
      ·
        refine ⟨98726945060705828301153629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65817963373803885534102419 98726945060705828301153629)
        ·
          refine ⟨37022604397764685612932611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 98726945060705828301153629 37022604397764685612932611)
          ·
            refine ⟨55533906596647028419398917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37022604397764685612932611 55533906596647028419398917)
            ·
              refine ⟨10412607486871317828637297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 55533906596647028419398917 10412607486871317828637297)
              ·
                refine ⟨7809455615153488371477973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10412607486871317828637297 7809455615153488371477973)
                ·
                  refine ⟨183034115980159883706515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7809455615153488371477973 183034115980159883706515)
                  ·
                    rfl

theorem cell23_3208119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 2, 7].length) (baseStart_3208119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208119 prefixEnd_3208119 := by exact prefixLift 3208119
  have htrace : WordTrace (prefixWord ++ tailWord_3208119) baseStart_3208119 baseEnd_3208119 := by
    simpa [prefixWord, tailWord_3208119, baseEnd_3208119] using wordTrace_append hprefix tailTrace_3208119
  have hstable : (prefixWord ++ tailWord_3208119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208119).length < 2 ^ (prefixWord ++ tailWord_3208119).sum := by decide
  have hdescent : baseEnd_3208119 < baseStart_3208119 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208209 : List Nat := [1, 2, 2, 1, 1, 2, 1, 5, 8]
def baseStart_3208209 : Nat := 118140960795 + 3208209 * 2 ^ 59
def prefixEnd_3208209 : Nat := 4983230072969 + 3 ^ 40 * 3208209 * 2
def baseEnd_3208209 : Nat := 183039250786704844581469

theorem tailTrace_3208209 : CollatzResearch.WordTrace tailWord_3208209 prefixEnd_3208209 183039250786704844581469 := by
  unfold tailWord_3208209
  simp only [CollatzResearch.WordTrace]
  refine ⟨117012995234214186320291681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78008663489476124213527787 117012995234214186320291681)
  ·
    refine ⟨87759746425660639740218761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117012995234214186320291681 87759746425660639740218761)
    ·
      refine ⟨65819809819245479805164071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87759746425660639740218761 65819809819245479805164071)
      ·
        refine ⟨98729714728868219707746107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65819809819245479805164071 98729714728868219707746107)
        ·
          refine ⟨148094572093302329561619161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98729714728868219707746107 148094572093302329561619161)
          ·
            refine ⟨111070929069976747171214371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148094572093302329561619161 111070929069976747171214371)
            ·
              refine ⟨166606393604965120756821557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111070929069976747171214371 166606393604965120756821557)
              ·
                refine ⟨15619349400465480070952021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166606393604965120756821557 15619349400465480070952021)
                ·
                  refine ⟨183039250786704844581469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15619349400465480070952021 183039250786704844581469)
                  ·
                    rfl

theorem cell23_3208209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 5, 8].length) (baseStart_3208209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208209 prefixEnd_3208209 := by exact prefixLift 3208209
  have htrace : WordTrace (prefixWord ++ tailWord_3208209) baseStart_3208209 baseEnd_3208209 := by
    simpa [prefixWord, tailWord_3208209, baseEnd_3208209] using wordTrace_append hprefix tailTrace_3208209
  have hstable : (prefixWord ++ tailWord_3208209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208209).length < 2 ^ (prefixWord ++ tailWord_3208209).sum := by decide
  have hdescent : baseEnd_3208209 < baseStart_3208209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208220 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 2, 4, 2]
def baseStart_3208220 : Nat := 118140960795 + 3208220 * 2 ^ 59
def prefixEnd_3208220 : Nat := 4983230072969 + 3 ^ 40 * 3208220 * 2
def baseEnd_3208220 : Nat := 1647358905367543058195671

theorem tailTrace_3208220 : CollatzResearch.WordTrace tailWord_3208220 prefixEnd_3208220 1647358905367543058195671 := by
  unfold tailWord_3208220
  simp only [CollatzResearch.WordTrace]
  refine ⟨58506698218587167599471057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78008930958116223465961409 58506698218587167599471057)
  ·
    refine ⟨43880023663940375699603293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58506698218587167599471057 43880023663940375699603293)
    ·
      refine ⟨16455008873977640887351235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43880023663940375699603293 16455008873977640887351235)
      ·
        refine ⟨24682513310966461331026853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16455008873977640887351235 24682513310966461331026853)
        ·
          refine ⟨4627971245806211499567535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24682513310966461331026853 4627971245806211499567535)
          ·
            refine ⟨6941956868709317249351303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4627971245806211499567535 6941956868709317249351303)
            ·
              refine ⟨10412935303063975874026955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6941956868709317249351303 10412935303063975874026955)
              ·
                refine ⟨15619402954595963811040433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10412935303063975874026955 15619402954595963811040433)
                ·
                  refine ⟨11714552215946972858280325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15619402954595963811040433 11714552215946972858280325)
                  ·
                    refine ⟨2196478540490057410927561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11714552215946972858280325 2196478540490057410927561)
                    ·
                      refine ⟨1647358905367543058195671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2196478540490057410927561 1647358905367543058195671)
                      ·
                        rfl

theorem cell23_3208220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 2, 4, 2].length) (baseStart_3208220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208220 prefixEnd_3208220 := by exact prefixLift 3208220
  have htrace : WordTrace (prefixWord ++ tailWord_3208220) baseStart_3208220 baseEnd_3208220 := by
    simpa [prefixWord, tailWord_3208220, baseEnd_3208220] using wordTrace_append hprefix tailTrace_3208220
  have hstable : (prefixWord ++ tailWord_3208220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208220).length < 2 ^ (prefixWord ++ tailWord_3208220).sum := by decide
  have hdescent : baseEnd_3208220 < baseStart_3208220 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208270 : List Nat := [4, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3]
def baseStart_3208270 : Nat := 118140960795 + 3208270 * 2 ^ 59
def prefixEnd_3208270 : Nat := 4983230072969 + 3 ^ 40 * 3208270 * 2
def baseEnd_3208270 : Nat := 1647384579400267862570441

theorem tailTrace_3208270 : CollatzResearch.WordTrace tailWord_3208270 prefixEnd_3208270 1647384579400267862570441 := by
  unfold tailWord_3208270
  simp only [CollatzResearch.WordTrace]
  refine ⟨14626902510874149217282783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78010146724662129158841509 14626902510874149217282783)
  ·
    refine ⟨21940353766311223825924175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14626902510874149217282783 21940353766311223825924175)
    ·
      refine ⟨32910530649466835738886263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21940353766311223825924175 32910530649466835738886263)
      ·
        refine ⟨49365795974200253608329395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32910530649466835738886263 49365795974200253608329395)
        ·
          refine ⟨74048693961300380412494093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49365795974200253608329395 74048693961300380412494093)
          ·
            refine ⟨27768260235487642654685285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74048693961300380412494093 27768260235487642654685285)
            ·
              refine ⟨5206548794153932997753491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27768260235487642654685285 5206548794153932997753491)
              ·
                refine ⟨7809823191230899496630237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5206548794153932997753491 7809823191230899496630237)
                ·
                  refine ⟨2928683696711587311236339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7809823191230899496630237 2928683696711587311236339)
                  ·
                    refine ⟨4393025545067380966854509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2928683696711587311236339 4393025545067380966854509)
                    ·
                      refine ⟨1647384579400267862570441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4393025545067380966854509 1647384579400267862570441)
                      ·
                        rfl

theorem cell23_3208270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 4, 1, 3, 1, 3].length) (baseStart_3208270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208270 prefixEnd_3208270 := by exact prefixLift 3208270
  have htrace : WordTrace (prefixWord ++ tailWord_3208270) baseStart_3208270 baseEnd_3208270 := by
    simpa [prefixWord, tailWord_3208270, baseEnd_3208270] using wordTrace_append hprefix tailTrace_3208270
  have hstable : (prefixWord ++ tailWord_3208270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208270).length < 2 ^ (prefixWord ++ tailWord_3208270).sum := by decide
  have hdescent : baseEnd_3208270 < baseStart_3208270 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208290 : List Nat := [3, 3, 2, 2, 1, 1, 1, 4, 1, 5]
def baseStart_3208290 : Nat := 118140960795 + 3208290 * 2 ^ 59
def prefixEnd_3208290 : Nat := 4983230072969 + 3 ^ 40 * 3208290 * 2
def baseEnd_3208290 : Nat := 549131616337785928106783

theorem tailTrace_3208290 : CollatzResearch.WordTrace tailWord_3208290 prefixEnd_3208290 549131616337785928106783 := by
  unfold tailWord_3208290
  simp only [CollatzResearch.WordTrace]
  refine ⟨29253987386730184288497581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78010633031280491435993549 29253987386730184288497581)
  ·
    refine ⟨10970245270023819108186593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29253987386730184288497581 10970245270023819108186593)
    ·
      refine ⟨8227683952517864331139945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10970245270023819108186593 8227683952517864331139945)
      ·
        refine ⟨6170762964388398248354959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8227683952517864331139945 6170762964388398248354959)
        ·
          refine ⟨9256144446582597372532439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6170762964388398248354959 9256144446582597372532439)
          ·
            refine ⟨13884216669873896058798659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9256144446582597372532439 13884216669873896058798659)
            ·
              refine ⟨20826325004810844088197989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13884216669873896058798659 20826325004810844088197989)
              ·
                refine ⟨3904935938402033266537123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20826325004810844088197989 3904935938402033266537123)
                ·
                  refine ⟨5857403907603049899805685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3904935938402033266537123 5857403907603049899805685)
                  ·
                    refine ⟨549131616337785928106783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5857403907603049899805685 549131616337785928106783)
                    ·
                      rfl

theorem cell23_3208290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 4, 1, 5].length) (baseStart_3208290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208290 prefixEnd_3208290 := by exact prefixLift 3208290
  have htrace : WordTrace (prefixWord ++ tailWord_3208290) baseStart_3208290 baseEnd_3208290 := by
    simpa [prefixWord, tailWord_3208290, baseEnd_3208290] using wordTrace_append hprefix tailTrace_3208290
  have hstable : (prefixWord ++ tailWord_3208290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208290).length < 2 ^ (prefixWord ++ tailWord_3208290).sum := by decide
  have hdescent : baseEnd_3208290 < baseStart_3208290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208293 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 2, 6, 2]
def baseStart_3208293 : Nat := 118140960795 + 3208293 * 2 ^ 59
def prefixEnd_3208293 : Nat := 4983230072969 + 3 ^ 40 * 3208293 * 2
def baseEnd_3208293 : Nat := 1647396389455321272582835

theorem tailTrace_3208293 : CollatzResearch.WordTrace tailWord_3208293 prefixEnd_3208293 1647396389455321272582835 := by
  unfold tailWord_3208293
  simp only [CollatzResearch.WordTrace]
  refine ⟨117016058965909868666349533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78010705977273245777566355 117016058965909868666349533)
  ·
    refine ⟨43881022112216200749881075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117016058965909868666349533 43881022112216200749881075)
    ·
      refine ⟨65821533168324301124821613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43881022112216200749881075 65821533168324301124821613)
      ·
        refine ⟨24683074938121612921808105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65821533168324301124821613 24683074938121612921808105)
        ·
          refine ⟨18512306203591209691356079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24683074938121612921808105 18512306203591209691356079)
          ·
            refine ⟨27768459305386814537034119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18512306203591209691356079 27768459305386814537034119)
            ·
              refine ⟨41652688958080221805551179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27768459305386814537034119 41652688958080221805551179)
              ·
                refine ⟨62479033437120332708326769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41652688958080221805551179 62479033437120332708326769)
                ·
                  refine ⟨46859275077840249531245077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62479033437120332708326769 46859275077840249531245077)
                  ·
                    refine ⟨2196528519273761696777113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 46859275077840249531245077 2196528519273761696777113)
                    ·
                      refine ⟨1647396389455321272582835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2196528519273761696777113 1647396389455321272582835)
                      ·
                        rfl

theorem cell23_3208293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 6, 2].length) (baseStart_3208293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208293 prefixEnd_3208293 := by exact prefixLift 3208293
  have htrace : WordTrace (prefixWord ++ tailWord_3208293) baseStart_3208293 baseEnd_3208293 := by
    simpa [prefixWord, tailWord_3208293, baseEnd_3208293] using wordTrace_append hprefix tailTrace_3208293
  have hstable : (prefixWord ++ tailWord_3208293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208293).length < 2 ^ (prefixWord ++ tailWord_3208293).sum := by decide
  have hdescent : baseEnd_3208293 < baseStart_3208293 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208310 : List Nat := [5, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_3208310 : Nat := 118140960795 + 3208310 * 2 ^ 59
def prefixEnd_3208310 : Nat := 4983230072969 + 3 ^ 40 * 3208310 * 2
def baseEnd_3208310 : Nat := 1647405118626447706070257

theorem tailTrace_3208310 : CollatzResearch.WordTrace tailWord_3208310 prefixEnd_3208310 1647405118626447706070257 := by
  unfold tailWord_3208310
  simp only [CollatzResearch.WordTrace]
  refine ⟨7313542437928017535607399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78011119337898853713145589 7313542437928017535607399)
  ·
    refine ⟨10970313656892026303411099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7313542437928017535607399 10970313656892026303411099)
    ·
      refine ⟨16455470485338039455116649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10970313656892026303411099 16455470485338039455116649)
      ·
        refine ⟨12341602864003529591337487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16455470485338039455116649 12341602864003529591337487)
        ·
          refine ⟨18512404296005294387006231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12341602864003529591337487 18512404296005294387006231)
          ·
            refine ⟨27768606444007941580509347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18512404296005294387006231 27768606444007941580509347)
            ·
              refine ⟨41652909666011912370764021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27768606444007941580509347 41652909666011912370764021)
              ·
                refine ⟨3904960281188616784759127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 41652909666011912370764021 3904960281188616784759127)
                ·
                  refine ⟨5857440421782925177138691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3904960281188616784759127 5857440421782925177138691)
                  ·
                    refine ⟨8786160632674387765708037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5857440421782925177138691 8786160632674387765708037)
                    ·
                      refine ⟨1647405118626447706070257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8786160632674387765708037 1647405118626447706070257)
                      ·
                        rfl

theorem cell23_3208310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_3208310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208310 prefixEnd_3208310 := by exact prefixLift 3208310
  have htrace : WordTrace (prefixWord ++ tailWord_3208310) baseStart_3208310 baseEnd_3208310 := by
    simpa [prefixWord, tailWord_3208310, baseEnd_3208310] using wordTrace_append hprefix tailTrace_3208310
  have hstable : (prefixWord ++ tailWord_3208310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208310).length < 2 ^ (prefixWord ++ tailWord_3208310).sum := by decide
  have hdescent : baseEnd_3208310 < baseStart_3208310 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208377 : List Nat := [1, 2, 1, 4, 1, 4, 2, 2, 2, 1, 3]
def baseStart_3208377 : Nat := 118140960795 + 3208377 * 2 ^ 59
def prefixEnd_3208377 : Nat := 4983230072969 + 3 ^ 40 * 3208377 * 2
def baseEnd_3208377 : Nat := 1647439521830298943932449

theorem tailTrace_3208377 : CollatzResearch.WordTrace tailWord_3208377 prefixEnd_3208377 1647439521830298943932449 := by
  unfold tailWord_3208377
  simp only [CollatzResearch.WordTrace]
  refine ⟨117019122697605551012407385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78012748465070367341604923 117019122697605551012407385)
  ·
    refine ⟨87764342023204163259305539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117019122697605551012407385 87764342023204163259305539)
    ·
      refine ⟨131646513034806244888958309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87764342023204163259305539 131646513034806244888958309)
      ·
        refine ⟨24683721194026170916679683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131646513034806244888958309 24683721194026170916679683)
        ·
          refine ⟨37025581791039256375019525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24683721194026170916679683 37025581791039256375019525)
          ·
            refine ⟨6942296585819860570316161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37025581791039256375019525 6942296585819860570316161)
            ·
              refine ⟨5206722439364895427737121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6942296585819860570316161 5206722439364895427737121)
              ·
                refine ⟨3905041829523671570802841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5206722439364895427737121 3905041829523671570802841)
                ·
                  refine ⟨2928781372142753678102131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3905041829523671570802841 2928781372142753678102131)
                  ·
                    refine ⟨4393172058214130517153197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2928781372142753678102131 4393172058214130517153197)
                    ·
                      refine ⟨1647439521830298943932449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4393172058214130517153197 1647439521830298943932449)
                      ·
                        rfl

theorem cell23_3208377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 2, 2, 1, 3].length) (baseStart_3208377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208377 prefixEnd_3208377 := by exact prefixLift 3208377
  have htrace : WordTrace (prefixWord ++ tailWord_3208377) baseStart_3208377 baseEnd_3208377 := by
    simpa [prefixWord, tailWord_3208377, baseEnd_3208377] using wordTrace_append hprefix tailTrace_3208377
  have hstable : (prefixWord ++ tailWord_3208377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208377).length < 2 ^ (prefixWord ++ tailWord_3208377).sum := by decide
  have hdescent : baseEnd_3208377 < baseStart_3208377 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208421 : List Nat := [1, 3, 1, 4, 3, 2, 2, 1, 1, 3, 2]
def baseStart_3208421 : Nat := 118140960795 + 3208421 * 2 ^ 59
def prefixEnd_3208421 : Nat := 4983230072969 + 3 ^ 40 * 3208421 * 2
def baseEnd_3208421 : Nat := 1647462114979096771782247

theorem tailTrace_3208421 : CollatzResearch.WordTrace tailWord_3208421 prefixEnd_3208421 1647462114979096771782247 := by
  unfold tailWord_3208421
  simp only [CollatzResearch.WordTrace]
  refine ⟨117020727509446146527009117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78013818339630764351339411 117020727509446146527009117)
  ·
    refine ⟨43882772816042304947628419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117020727509446146527009117 43882772816042304947628419)
    ·
      refine ⟨65824159224063457421442629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43882772816042304947628419 65824159224063457421442629)
      ·
        refine ⟨12342029854511898266520493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65824159224063457421442629 12342029854511898266520493)
        ·
          refine ⟨4628261195441961849945185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12342029854511898266520493 4628261195441961849945185)
          ·
            refine ⟨3471195896581471387458889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4628261195441961849945185 3471195896581471387458889)
            ·
              refine ⟨2603396922436103540594167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3471195896581471387458889 2603396922436103540594167)
              ·
                refine ⟨3905095383654155310891251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603396922436103540594167 3905095383654155310891251)
                ·
                  refine ⟨5857643075481232966336877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3905095383654155310891251 5857643075481232966336877)
                  ·
                    refine ⟨2196616153305462362376329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5857643075481232966336877 2196616153305462362376329)
                    ·
                      refine ⟨1647462114979096771782247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2196616153305462362376329 1647462114979096771782247)
                      ·
                        rfl

theorem cell23_3208421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_3208421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208421 prefixEnd_3208421 := by exact prefixLift 3208421
  have htrace : WordTrace (prefixWord ++ tailWord_3208421) baseStart_3208421 baseEnd_3208421 := by
    simpa [prefixWord, tailWord_3208421, baseEnd_3208421] using wordTrace_append hprefix tailTrace_3208421
  have hstable : (prefixWord ++ tailWord_3208421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208421).length < 2 ^ (prefixWord ++ tailWord_3208421).sum := by decide
  have hdescent : baseEnd_3208421 < baseStart_3208421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208434 : List Nat := [3, 2, 1, 3, 3, 1, 1, 1, 4, 2, 2]
def baseStart_3208434 : Nat := 118140960795 + 3208434 * 2 ^ 59
def prefixEnd_3208434 : Nat := 4983230072969 + 3 ^ 40 * 3208434 * 2
def baseEnd_3208434 : Nat := 1647468790227605220919687

theorem tailTrace_3208434 : CollatzResearch.WordTrace tailWord_3208434 prefixEnd_3208434 1647468790227605220919687 := by
  unfold tailWord_3208434
  simp only [CollatzResearch.WordTrace]
  refine ⟨29255300414599762436808089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78014134438932699831488237 29255300414599762436808089)
  ·
    refine ⟨21941475310949821827606067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29255300414599762436808089 21941475310949821827606067)
    ·
      refine ⟨32912212966424732741409101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21941475310949821827606067 32912212966424732741409101)
      ·
        refine ⟨12342079862409274778028413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32912212966424732741409101 12342079862409274778028413)
        ·
          refine ⟨4628279948403478041760655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12342079862409274778028413 4628279948403478041760655)
          ·
            refine ⟨6942419922605217062640983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4628279948403478041760655 6942419922605217062640983)
            ·
              refine ⟨10413629883907825593961475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6942419922605217062640983 10413629883907825593961475)
              ·
                refine ⟨15620444825861738390942213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10413629883907825593961475 15620444825861738390942213)
                ·
                  refine ⟨2928833404849075948301665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15620444825861738390942213 2928833404849075948301665)
                  ·
                    refine ⟨2196625053636806961226249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2928833404849075948301665 2196625053636806961226249)
                    ·
                      refine ⟨1647468790227605220919687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2196625053636806961226249 1647468790227605220919687)
                      ·
                        rfl

theorem cell23_3208434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_3208434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208434 prefixEnd_3208434 := by exact prefixLift 3208434
  have htrace : WordTrace (prefixWord ++ tailWord_3208434) baseStart_3208434 baseEnd_3208434 := by
    simpa [prefixWord, tailWord_3208434, baseEnd_3208434] using wordTrace_append hprefix tailTrace_3208434
  have hstable : (prefixWord ++ tailWord_3208434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208434).length < 2 ^ (prefixWord ++ tailWord_3208434).sum := by decide
  have hdescent : baseEnd_3208434 < baseStart_3208434 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208473 : List Nat := [1, 2, 1, 2, 1, 1, 1, 1, 8, 1, 4]
def baseStart_3208473 : Nat := 118140960795 + 3208473 * 2 ^ 59
def prefixEnd_3208473 : Nat := 4983230072969 + 3 ^ 40 * 3208473 * 2
def baseEnd_3208473 : Nat := 1647488815973130568332007

theorem tailTrace_3208473 : CollatzResearch.WordTrace tailWord_3208473 prefixEnd_3208473 1647488815973130568332007 := by
  unfold tailWord_3208473
  simp only [CollatzResearch.WordTrace]
  refine ⟨117022624105257759407902073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78015082736838506271934715 117022624105257759407902073)
  ·
    refine ⟨87766968078943319555926555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117022624105257759407902073 87766968078943319555926555)
    ·
      refine ⟨131650452118414979333889833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87766968078943319555926555 131650452118414979333889833)
      ·
        refine ⟨98737839088811234500417375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131650452118414979333889833 98737839088811234500417375)
        ·
          refine ⟨148106758633216851750626063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98737839088811234500417375 148106758633216851750626063)
          ·
            refine ⟨222160137949825277625939095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148106758633216851750626063 222160137949825277625939095)
            ·
              refine ⟨333240206924737916438908643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222160137949825277625939095 333240206924737916438908643)
              ·
                refine ⟨499860310387106874658362965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333240206924737916438908643 499860310387106874658362965)
                ·
                  refine ⟨5857738012348908687402691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 499860310387106874658362965 5857738012348908687402691)
                  ·
                    refine ⟨8786607018523363031104037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5857738012348908687402691 8786607018523363031104037)
                    ·
                      refine ⟨1647488815973130568332007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8786607018523363031104037 1647488815973130568332007)
                      ·
                        rfl

theorem cell23_3208473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 1, 4].length) (baseStart_3208473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208473 prefixEnd_3208473 := by exact prefixLift 3208473
  have htrace : WordTrace (prefixWord ++ tailWord_3208473) baseStart_3208473 baseEnd_3208473 := by
    simpa [prefixWord, tailWord_3208473, baseEnd_3208473] using wordTrace_append hprefix tailTrace_3208473
  have hstable : (prefixWord ++ tailWord_3208473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208473).length < 2 ^ (prefixWord ++ tailWord_3208473).sum := by decide
  have hdescent : baseEnd_3208473 < baseStart_3208473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208502 : List Nat := [5, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_3208502 : Nat := 118140960795 + 3208502 * 2 ^ 59
def prefixEnd_3208502 : Nat := 4983230072969 + 3 ^ 40 * 3208502 * 2
def baseEnd_3208502 : Nat := 1647503706912110954869375

theorem tailTrace_3208502 : CollatzResearch.WordTrace tailWord_3208502 prefixEnd_3208502 1647503706912110954869375 := by
  unfold tailWord_3208502
  simp only [CollatzResearch.WordTrace]
  refine ⟨7313980113884543585044235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78015787881435131573805173 7313980113884543585044235)
  ·
    refine ⟨10970970170826815377566353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7313980113884543585044235 10970970170826815377566353)
    ·
      refine ⟨8228227628120111533174765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10970970170826815377566353 8228227628120111533174765)
      ·
        refine ⟨3085585360545041824940537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8228227628120111533174765 3085585360545041824940537)
        ·
          refine ⟨2314189020408781368705403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3085585360545041824940537 2314189020408781368705403)
          ·
            refine ⟨3471283530613172053058105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314189020408781368705403 3471283530613172053058105)
            ·
              refine ⟨2603462647959879039793579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3471283530613172053058105 2603462647959879039793579)
              ·
                refine ⟨3905193971939818559690369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603462647959879039793579 3905193971939818559690369)
                ·
                  refine ⟨2928895478954863919767777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3905193971939818559690369 2928895478954863919767777)
                  ·
                    refine ⟨2196671609216147939825833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2928895478954863919767777 2196671609216147939825833)
                    ·
                      refine ⟨1647503706912110954869375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2196671609216147939825833 1647503706912110954869375)
                      ·
                        rfl

theorem cell23_3208502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_3208502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208502 prefixEnd_3208502 := by exact prefixLift 3208502
  have htrace : WordTrace (prefixWord ++ tailWord_3208502) baseStart_3208502 baseEnd_3208502 := by
    simpa [prefixWord, tailWord_3208502, baseEnd_3208502] using wordTrace_append hprefix tailTrace_3208502
  have hstable : (prefixWord ++ tailWord_3208502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208502).length < 2 ^ (prefixWord ++ tailWord_3208502).sum := by decide
  have hdescent : baseEnd_3208502 < baseStart_3208502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208563 : List Nat := [1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 4]
def baseStart_3208563 : Nat := 118140960795 + 3208563 * 2 ^ 59
def prefixEnd_3208563 : Nat := 4983230072969 + 3 ^ 40 * 3208563 * 2
def baseEnd_3208563 : Nat := 1647535029232035216206593

theorem tailTrace_3208563 : CollatzResearch.WordTrace tailWord_3208563 prefixEnd_3208563 1647535029232035216206593 := by
  unfold tailWord_3208563
  simp only [CollatzResearch.WordTrace]
  refine ⟨117025906674931704778678343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78017271116621136519118895 117025906674931704778678343)
  ·
    refine ⟨175538860012397557168017515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117025906674931704778678343 175538860012397557168017515)
    ·
      refine ⟨263308290018596335752026273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175538860012397557168017515 263308290018596335752026273)
      ·
        refine ⟨197481217513947251814019705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263308290018596335752026273 197481217513947251814019705)
        ·
          refine ⟨148110913135460438860514779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197481217513947251814019705 148110913135460438860514779)
          ·
            refine ⟨222166369703190658290772169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148110913135460438860514779 222166369703190658290772169)
            ·
              refine ⟨166624777277392993718079127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222166369703190658290772169 166624777277392993718079127)
              ·
                refine ⟨249937165916089490577118691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166624777277392993718079127 249937165916089490577118691)
                ·
                  refine ⟨374905748874134235865678037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 249937165916089490577118691 374905748874134235865678037)
                  ·
                    refine ⟨8786853489237521153101829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 374905748874134235865678037 8786853489237521153101829)
                    ·
                      refine ⟨1647535029232035216206593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8786853489237521153101829 1647535029232035216206593)
                      ·
                        rfl

theorem cell23_3208563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_3208563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208563 prefixEnd_3208563 := by exact prefixLift 3208563
  have htrace : WordTrace (prefixWord ++ tailWord_3208563) baseStart_3208563 baseEnd_3208563 := by
    simpa [prefixWord, tailWord_3208563, baseEnd_3208563] using wordTrace_append hprefix tailTrace_3208563
  have hstable : (prefixWord ++ tailWord_3208563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208563).length < 2 ^ (prefixWord ++ tailWord_3208563).sum := by decide
  have hdescent : baseEnd_3208563 < baseStart_3208563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208584 : List Nat := [2, 1, 3, 3, 1, 2, 3, 1, 2, 3, 2]
def baseStart_3208584 : Nat := 118140960795 + 3208584 * 2 ^ 59
def prefixEnd_3208584 : Nat := 4983230072969 + 3 ^ 40 * 3208584 * 2
def baseEnd_3208584 : Nat := 1647545812325779634043997

theorem tailTrace_3208584 : CollatzResearch.WordTrace tailWord_3208584 prefixEnd_3208584 1647545812325779634043997 := by
  unfold tailWord_3208584
  simp only [CollatzResearch.WordTrace]
  refine ⟨58513336303927812682596403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78017781738570416910128537 58513336303927812682596403)
  ·
    refine ⟨87770004455891719023894605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58513336303927812682596403 87770004455891719023894605)
    ·
      refine ⟨32913751670959394633960477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87770004455891719023894605 32913751670959394633960477)
      ·
        refine ⟨12342656876609772987735179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32913751670959394633960477 12342656876609772987735179)
        ·
          refine ⟨18513985314914659481602769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12342656876609772987735179 18513985314914659481602769)
          ·
            refine ⟨13885488986185994611202077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18513985314914659481602769 13885488986185994611202077)
            ·
              refine ⟨5207058369819747979200779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13885488986185994611202077 5207058369819747979200779)
              ·
                refine ⟨7810587554729621968801169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5207058369819747979200779 7810587554729621968801169)
                ·
                  refine ⟨5857940666047216476600877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7810587554729621968801169 5857940666047216476600877)
                  ·
                    refine ⟨2196727749767706178725329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5857940666047216476600877 2196727749767706178725329)
                    ·
                      refine ⟨1647545812325779634043997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2196727749767706178725329 1647545812325779634043997)
                      ·
                        rfl

theorem cell23_3208584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 3, 1, 2, 3, 2].length) (baseStart_3208584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208584 prefixEnd_3208584 := by exact prefixLift 3208584
  have htrace : WordTrace (prefixWord ++ tailWord_3208584) baseStart_3208584 baseEnd_3208584 := by
    simpa [prefixWord, tailWord_3208584, baseEnd_3208584] using wordTrace_append hprefix tailTrace_3208584
  have hstable : (prefixWord ++ tailWord_3208584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208584).length < 2 ^ (prefixWord ++ tailWord_3208584).sum := by decide
  have hdescent : baseEnd_3208584 < baseStart_3208584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208607 : List Nat := [1, 1, 2, 5, 1, 3, 1, 1, 4, 4]
def baseStart_3208607 : Nat := 118140960795 + 3208607 * 2 ^ 59
def prefixEnd_3208607 : Nat := 4983230072969 + 3 ^ 40 * 3208607 * 2
def baseEnd_3208607 : Nat := 549185874126944348018797

theorem tailTrace_3208607 : CollatzResearch.WordTrace tailWord_3208607 prefixEnd_3208607 549185874126944348018797 := by
  unfold tailWord_3208607
  simp only [CollatzResearch.WordTrace]
  refine ⟨117027511486772300293280075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78018340991181533528853383 117027511486772300293280075)
  ·
    refine ⟨175541267230158450439920113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117027511486772300293280075 175541267230158450439920113)
    ·
      refine ⟨131655950422618837829940085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175541267230158450439920113 131655950422618837829940085)
      ·
        refine ⟨12342745352120516046556883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131655950422618837829940085 12342745352120516046556883)
        ·
          refine ⟨18514118028180774069835325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12342745352120516046556883 18514118028180774069835325)
          ·
            refine ⟨6942794260567790276188247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18514118028180774069835325 6942794260567790276188247)
            ·
              refine ⟨10414191390851685414282371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6942794260567790276188247 10414191390851685414282371)
              ·
                refine ⟨15621287086277528121423557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10414191390851685414282371 15621287086277528121423557)
                ·
                  refine ⟨2928991328677036522766917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15621287086277528121423557 2928991328677036522766917)
                  ·
                    refine ⟨549185874126944348018797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2928991328677036522766917 549185874126944348018797)
                    ·
                      rfl

theorem cell23_3208607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 1, 4, 4].length) (baseStart_3208607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208607 prefixEnd_3208607 := by exact prefixLift 3208607
  have htrace : WordTrace (prefixWord ++ tailWord_3208607) baseStart_3208607 baseEnd_3208607 := by
    simpa [prefixWord, tailWord_3208607, baseEnd_3208607] using wordTrace_append hprefix tailTrace_3208607
  have hstable : (prefixWord ++ tailWord_3208607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208607).length < 2 ^ (prefixWord ++ tailWord_3208607).sum := by decide
  have hdescent : baseEnd_3208607 < baseStart_3208607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208647 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 6, 1, 3]
def baseStart_3208647 : Nat := 118140960795 + 3208647 * 2 ^ 59
def prefixEnd_3208647 : Nat := 4983230072969 + 3 ^ 40 * 3208647 * 2
def baseEnd_3208647 : Nat := 1647578161607012887556207

theorem tailTrace_3208647 : CollatzResearch.WordTrace tailWord_3208647 prefixEnd_3208647 1647578161607012887556207 := by
  unfold tailWord_3208647
  simp only [CollatzResearch.WordTrace]
  refine ⟨117028970406627387124736195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78019313604418258083157463 117028970406627387124736195)
  ·
    refine ⟨175543455609941080687104293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117028970406627387124736195 175543455609941080687104293)
    ·
      refine ⟨32914397926863952628832055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175543455609941080687104293 32914397926863952628832055)
      ·
        refine ⟨49371596890295928943248083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32914397926863952628832055 49371596890295928943248083)
        ·
          refine ⟨74057395335443893414872125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49371596890295928943248083 74057395335443893414872125)
          ·
            refine ⟨27771523250791460030577047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74057395335443893414872125 27771523250791460030577047)
            ·
              refine ⟨41657284876187190045865571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27771523250791460030577047 41657284876187190045865571)
              ·
                refine ⟨62485927314280785068798357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41657284876187190045865571 62485927314280785068798357)
                ·
                  refine ⟨2929027842856911800099923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 62485927314280785068798357 2929027842856911800099923)
                  ·
                    refine ⟨4393541764285367700149885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2929027842856911800099923 4393541764285367700149885)
                    ·
                      refine ⟨1647578161607012887556207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4393541764285367700149885 1647578161607012887556207)
                      ·
                        rfl

theorem cell23_3208647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 6, 1, 3].length) (baseStart_3208647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208647 prefixEnd_3208647 := by exact prefixLift 3208647
  have htrace : WordTrace (prefixWord ++ tailWord_3208647) baseStart_3208647 baseEnd_3208647 := by
    simpa [prefixWord, tailWord_3208647, baseEnd_3208647] using wordTrace_append hprefix tailTrace_3208647
  have hstable : (prefixWord ++ tailWord_3208647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208647).length < 2 ^ (prefixWord ++ tailWord_3208647).sum := by decide
  have hdescent : baseEnd_3208647 < baseStart_3208647 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208657 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 7, 3, 2]
def baseStart_3208657 : Nat := 118140960795 + 3208657 * 2 ^ 59
def prefixEnd_3208657 : Nat := 4983230072969 + 3 ^ 40 * 3208657 * 2
def baseEnd_3208657 : Nat := 1647583296413557848431161

theorem tailTrace_3208657 : CollatzResearch.WordTrace tailWord_3208657 prefixEnd_3208657 1647583296413557848431161 := by
  unfold tailWord_3208657
  simp only [CollatzResearch.WordTrace]
  refine ⟨117029335136591158832600225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78019556757727439221733483 117029335136591158832600225)
  ·
    refine ⟨87772001352443369124450169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117029335136591158832600225 87772001352443369124450169)
    ·
      refine ⟨65829001014332526843337627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87772001352443369124450169 65829001014332526843337627)
      ·
        refine ⟨98743501521498790265006441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65829001014332526843337627 98743501521498790265006441)
        ·
          refine ⟨74057626141124092698754831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98743501521498790265006441 74057626141124092698754831)
          ·
            refine ⟨111086439211686139048132247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74057626141124092698754831 111086439211686139048132247)
            ·
              refine ⟨166629658817529208572198371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111086439211686139048132247 166629658817529208572198371)
              ·
                refine ⟨249944488226293812858297557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 166629658817529208572198371 249944488226293812858297557)
                ·
                  refine ⟨5858073942803761238866349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 249944488226293812858297557 5858073942803761238866349)
                  ·
                    refine ⟨2196777728551410464574881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5858073942803761238866349 2196777728551410464574881)
                    ·
                      refine ⟨1647583296413557848431161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2196777728551410464574881 1647583296413557848431161)
                      ·
                        rfl

theorem cell23_3208657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 7, 3, 2].length) (baseStart_3208657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208657 prefixEnd_3208657 := by exact prefixLift 3208657
  have htrace : WordTrace (prefixWord ++ tailWord_3208657) baseStart_3208657 baseEnd_3208657 := by
    simpa [prefixWord, tailWord_3208657, baseEnd_3208657] using wordTrace_append hprefix tailTrace_3208657
  have hstable : (prefixWord ++ tailWord_3208657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208657).length < 2 ^ (prefixWord ++ tailWord_3208657).sum := by decide
  have hdescent : baseEnd_3208657 < baseStart_3208657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208680 : List Nat := [2, 1, 4, 1, 1, 2, 2, 1, 1, 8]
def baseStart_3208680 : Nat := 118140960795 + 3208680 * 2 ^ 59
def prefixEnd_3208680 : Nat := 4983230072969 + 3 ^ 40 * 3208680 * 2
def baseEnd_3208680 : Nat := 549198368822870419481185

theorem tailTrace_3208680 : CollatzResearch.WordTrace tailWord_3208680 prefixEnd_3208680 549198368822870419481185 := by
  unfold tailWord_3208680
  simp only [CollatzResearch.WordTrace]
  refine ⟨58515087007753916880343747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78020116010338555840458329 58515087007753916880343747)
  ·
    refine ⟨87772630511630875320515621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58515087007753916880343747 87772630511630875320515621)
    ·
      refine ⟨16457368220930789122596679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87772630511630875320515621 16457368220930789122596679)
      ·
        refine ⟨24686052331396183683895019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16457368220930789122596679 24686052331396183683895019)
        ·
          refine ⟨37029078497094275525842529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24686052331396183683895019 37029078497094275525842529)
          ·
            refine ⟨27771808872820706644381897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37029078497094275525842529 27771808872820706644381897)
            ·
              refine ⟨20828856654615529983286423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27771808872820706644381897 20828856654615529983286423)
              ·
                refine ⟨31243284981923294974929635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20828856654615529983286423 31243284981923294974929635)
                ·
                  refine ⟨46864927472884942462394453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31243284981923294974929635 46864927472884942462394453)
                  ·
                    refine ⟨549198368822870419481185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46864927472884942462394453 549198368822870419481185)
                    ·
                      rfl

theorem cell23_3208680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 1, 8].length) (baseStart_3208680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208680 prefixEnd_3208680 := by exact prefixLift 3208680
  have htrace : WordTrace (prefixWord ++ tailWord_3208680) baseStart_3208680 baseEnd_3208680 := by
    simpa [prefixWord, tailWord_3208680, baseEnd_3208680] using wordTrace_append hprefix tailTrace_3208680
  have hstable : (prefixWord ++ tailWord_3208680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208680).length < 2 ^ (prefixWord ++ tailWord_3208680).sum := by decide
  have hdescent : baseEnd_3208680 < baseStart_3208680 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208721 : List Nat := [1, 2, 2, 1, 1, 2, 6, 2, 2, 2, 2]
def baseStart_3208721 : Nat := 118140960795 + 3208721 * 2 ^ 59
def prefixEnd_3208721 : Nat := 4983230072969 + 3 ^ 40 * 3208721 * 2
def baseEnd_3208721 : Nat := 1647616159175445598030867

theorem tailTrace_3208721 : CollatzResearch.WordTrace tailWord_3208721 prefixEnd_3208721 1647616159175445598030867 := by
  unfold tailWord_3208721
  simp only [CollatzResearch.WordTrace]
  refine ⟨117031669408359297762930017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78021112938906198508620011 117031669408359297762930017)
  ·
    refine ⟨87773752056269473322197513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117031669408359297762930017 87773752056269473322197513)
    ·
      refine ⟨65830314042202104991648135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87773752056269473322197513 65830314042202104991648135)
      ·
        refine ⟨98745471063303157487472203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65830314042202104991648135 98745471063303157487472203)
        ·
          refine ⟨148118206594954736231208305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98745471063303157487472203 148118206594954736231208305)
          ·
            refine ⟨111088654946216052173406229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148118206594954736231208305 111088654946216052173406229)
            ·
              refine ⟨5207280700603877445628417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111088654946216052173406229 5207280700603877445628417)
              ·
                refine ⟨3905460525452908084221313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5207280700603877445628417 3905460525452908084221313)
                ·
                  refine ⟨2929095394089681063165985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3905460525452908084221313 2929095394089681063165985)
                  ·
                    refine ⟨2196821545567260797374489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2929095394089681063165985 2196821545567260797374489)
                    ·
                      refine ⟨1647616159175445598030867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2196821545567260797374489 1647616159175445598030867)
                      ·
                        rfl

theorem cell23_3208721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 2, 2].length) (baseStart_3208721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208721 prefixEnd_3208721 := by exact prefixLift 3208721
  have htrace : WordTrace (prefixWord ++ tailWord_3208721) baseStart_3208721 baseEnd_3208721 := by
    simpa [prefixWord, tailWord_3208721, baseEnd_3208721] using wordTrace_append hprefix tailTrace_3208721
  have hstable : (prefixWord ++ tailWord_3208721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208721).length < 2 ^ (prefixWord ++ tailWord_3208721).sum := by decide
  have hdescent : baseEnd_3208721 < baseStart_3208721 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208730 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8]
def baseStart_3208730 : Nat := 118140960795 + 3208730 * 2 ^ 59
def prefixEnd_3208730 : Nat := 4983230072969 + 3 ^ 40 * 3208730 * 2
def baseEnd_3208730 : Nat := 1647620780501336062818325

theorem tailTrace_3208730 : CollatzResearch.WordTrace tailWord_3208730 prefixEnd_3208730 1647620780501336062818325 := by
  unfold tailWord_3208730
  simp only [CollatzResearch.WordTrace]
  refine ⟨29257999416331673075001911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78021331776884461533338429 29257999416331673075001911)
  ·
    refine ⟨43886999124497509612502867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29257999416331673075001911 43886999124497509612502867)
    ·
      refine ⟨65830498686746264418754301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43886999124497509612502867 65830498686746264418754301)
      ·
        refine ⟨24686437007529849157032863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65830498686746264418754301 24686437007529849157032863)
        ·
          refine ⟨37029655511294773735549295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24686437007529849157032863 37029655511294773735549295)
          ·
            refine ⟨55544483266942160603323943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37029655511294773735549295 55544483266942160603323943)
            ·
              refine ⟨83316724900413240904985915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55544483266942160603323943 83316724900413240904985915)
              ·
                refine ⟨124975087350619861357478873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83316724900413240904985915 124975087350619861357478873)
                ·
                  refine ⟨93731315512964896018109155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 124975087350619861357478873 93731315512964896018109155)
                  ·
                    refine ⟨140596973269447344027163733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 93731315512964896018109155 140596973269447344027163733)
                    ·
                      refine ⟨1647620780501336062818325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 140596973269447344027163733 1647620780501336062818325)
                      ·
                        rfl

theorem cell23_3208730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_3208730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208730 prefixEnd_3208730 := by exact prefixLift 3208730
  have htrace : WordTrace (prefixWord ++ tailWord_3208730) baseStart_3208730 baseEnd_3208730 := by
    simpa [prefixWord, tailWord_3208730, baseEnd_3208730] using wordTrace_append hprefix tailTrace_3208730
  have hstable : (prefixWord ++ tailWord_3208730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208730).length < 2 ^ (prefixWord ++ tailWord_3208730).sum := by decide
  have hdescent : baseEnd_3208730 < baseStart_3208730 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208737 : List Nat := [1, 2, 3, 2, 2, 2, 1, 1, 1, 5, 3]
def baseStart_3208737 : Nat := 118140960795 + 3208737 * 2 ^ 59
def prefixEnd_3208737 : Nat := 4983230072969 + 3 ^ 40 * 3208737 * 2
def baseEnd_3208737 : Nat := 1647624374865917535430793

theorem tailTrace_3208737 : CollatzResearch.WordTrace tailWord_3208737 prefixEnd_3208737 1647624374865917535430793 := by
  unfold tailWord_3208737
  simp only [CollatzResearch.WordTrace]
  refine ⟨117032252976301332495512465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78021501984200888330341643 117032252976301332495512465)
  ·
    refine ⟨87774189732225999371634349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117032252976301332495512465 87774189732225999371634349)
    ·
      refine ⟨32915321149584749764362881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87774189732225999371634349 32915321149584749764362881)
      ·
        refine ⟨24686490862188562323272161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32915321149584749764362881 24686490862188562323272161)
        ·
          refine ⟨18514868146641421742454121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24686490862188562323272161 18514868146641421742454121)
          ·
            refine ⟨13886151109981066306840591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18514868146641421742454121 13886151109981066306840591)
            ·
              refine ⟨20829226664971599460260887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13886151109981066306840591 20829226664971599460260887)
              ·
                refine ⟨31243839997457399190391331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20829226664971599460260887 31243839997457399190391331)
                ·
                  refine ⟨46865759996186098785586997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31243839997457399190391331 46865759996186098785586997)
                  ·
                    refine ⟨4393664999642446761148781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46865759996186098785586997 4393664999642446761148781)
                    ·
                      refine ⟨1647624374865917535430793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4393664999642446761148781 1647624374865917535430793)
                      ·
                        rfl

theorem cell23_3208737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 5, 3].length) (baseStart_3208737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208737 prefixEnd_3208737 := by exact prefixLift 3208737
  have htrace : WordTrace (prefixWord ++ tailWord_3208737) baseStart_3208737 baseEnd_3208737 := by
    simpa [prefixWord, tailWord_3208737, baseEnd_3208737] using wordTrace_append hprefix tailTrace_3208737
  have hstable : (prefixWord ++ tailWord_3208737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208737).length < 2 ^ (prefixWord ++ tailWord_3208737).sum := by decide
  have hdescent : baseEnd_3208737 < baseStart_3208737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208744 : List Nat := [2, 1, 5, 2, 2, 1, 1, 2, 7]
def baseStart_3208744 : Nat := 118140960795 + 3208744 * 2 ^ 59
def prefixEnd_3208744 : Nat := 4983230072969 + 3 ^ 40 * 3208744 * 2
def baseEnd_3208744 : Nat := 183069774358944334227029

theorem tailTrace_3208744 : CollatzResearch.WordTrace tailWord_3208744 prefixEnd_3208744 183069774358944334227029 := by
  unfold tailWord_3208744
  simp only [CollatzResearch.WordTrace]
  refine ⟨58516254143637986345508643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78021672191517315127344857 58516254143637986345508643)
  ·
    refine ⟨87774381215456979518262965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58516254143637986345508643 87774381215456979518262965)
    ·
      refine ⟨8228848238949091829837153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87774381215456979518262965 8228848238949091829837153)
      ·
        refine ⟨6171636179211818872377865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8228848238949091829837153 6171636179211818872377865)
        ·
          refine ⟨4628727134408864154283399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6171636179211818872377865 4628727134408864154283399)
          ·
            refine ⟨6943090701613296231425099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4628727134408864154283399 6943090701613296231425099)
            ·
              refine ⟨10414636052419944347137649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6943090701613296231425099 10414636052419944347137649)
              ·
                refine ⟨7810977039314958260353237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10414636052419944347137649 7810977039314958260353237)
                ·
                  refine ⟨183069774358944334227029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7810977039314958260353237 183069774358944334227029)
                  ·
                    rfl

theorem cell23_3208744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 2, 7].length) (baseStart_3208744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208744 prefixEnd_3208744 := by exact prefixLift 3208744
  have htrace : WordTrace (prefixWord ++ tailWord_3208744) baseStart_3208744 baseEnd_3208744 := by
    simpa [prefixWord, tailWord_3208744, baseEnd_3208744] using wordTrace_append hprefix tailTrace_3208744
  have hstable : (prefixWord ++ tailWord_3208744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208744).length < 2 ^ (prefixWord ++ tailWord_3208744).sum := by decide
  have hdescent : baseEnd_3208744 < baseStart_3208744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208757 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 1, 7]
def baseStart_3208757 : Nat := 118140960795 + 3208757 * 2 ^ 59
def prefixEnd_3208757 : Nat := 4983230072969 + 3 ^ 40 * 3208757 * 2
def baseEnd_3208757 : Nat := 549211548159669152393567

theorem tailTrace_3208757 : CollatzResearch.WordTrace tailWord_3208757 prefixEnd_3208757 549211548159669152393567 := by
  unfold tailWord_3208757
  simp only [CollatzResearch.WordTrace]
  refine ⟨117032982436228875911240525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78021988290819250607493683 117032982436228875911240525)
  ·
    refine ⟨43887368413585828466715197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117032982436228875911240525 43887368413585828466715197)
    ·
      refine ⟨16457763155094685675018199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43887368413585828466715197 16457763155094685675018199)
      ·
        refine ⟨24686644732642028512527299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16457763155094685675018199 24686644732642028512527299)
        ·
          refine ⟨37029967098963042768790949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24686644732642028512527299 37029967098963042768790949)
          ·
            refine ⟨6943118831055570519148303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37029967098963042768790949 6943118831055570519148303)
            ·
              refine ⟨10414678246583355778722455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6943118831055570519148303 10414678246583355778722455)
              ·
                refine ⟨15622017369875033668083683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10414678246583355778722455 15622017369875033668083683)
                ·
                  refine ⟨23433026054812550502125525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15622017369875033668083683 23433026054812550502125525)
                  ·
                    refine ⟨549211548159669152393567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 23433026054812550502125525 549211548159669152393567)
                    ·
                      rfl

theorem cell23_3208757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 7].length) (baseStart_3208757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208757 prefixEnd_3208757 := by exact prefixLift 3208757
  have htrace : WordTrace (prefixWord ++ tailWord_3208757) baseStart_3208757 baseEnd_3208757 := by
    simpa [prefixWord, tailWord_3208757, baseEnd_3208757] using wordTrace_append hprefix tailTrace_3208757
  have hstable : (prefixWord ++ tailWord_3208757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208757).length < 2 ^ (prefixWord ++ tailWord_3208757).sum := by decide
  have hdescent : baseEnd_3208757 < baseStart_3208757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208777 : List Nat := [1, 2, 1, 1, 2, 2, 1, 6, 2, 1, 4]
def baseStart_3208777 : Nat := 118140960795 + 3208777 * 2 ^ 59
def prefixEnd_3208777 : Nat := 4983230072969 + 3 ^ 40 * 3208777 * 2
def baseEnd_3208777 : Nat := 1647644914092097378930609

theorem tailTrace_3208777 : CollatzResearch.WordTrace tailWord_3208777 prefixEnd_3208777 1647644914092097378930609 := by
  unfold tailWord_3208777
  simp only [CollatzResearch.WordTrace]
  refine ⟨117033711896156419326968585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78022474597437612884645723 117033711896156419326968585)
  ·
    refine ⟨87775283922117314495226439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117033711896156419326968585 87775283922117314495226439)
    ·
      refine ⟨131662925883175971742839659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87775283922117314495226439 131662925883175971742839659)
      ·
        refine ⟨197494388824763957614259489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131662925883175971742839659 197494388824763957614259489)
        ·
          refine ⟨148120791618572968210694617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197494388824763957614259489 148120791618572968210694617)
          ·
            refine ⟨111090593713929726158020963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148120791618572968210694617 111090593713929726158020963)
            ·
              refine ⟨166635890570894589237031445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111090593713929726158020963 166635890570894589237031445)
              ·
                refine ⟨7811057370510683870485849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166635890570894589237031445 7811057370510683870485849)
                ·
                  refine ⟨5858293027883012902864387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7811057370510683870485849 5858293027883012902864387)
                  ·
                    refine ⟨8787439541824519354296581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5858293027883012902864387 8787439541824519354296581)
                    ·
                      refine ⟨1647644914092097378930609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8787439541824519354296581 1647644914092097378930609)
                      ·
                        rfl

theorem cell23_3208777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 1, 4].length) (baseStart_3208777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208777 prefixEnd_3208777 := by exact prefixLift 3208777
  have htrace : WordTrace (prefixWord ++ tailWord_3208777) baseStart_3208777 baseEnd_3208777 := by
    simpa [prefixWord, tailWord_3208777, baseEnd_3208777] using wordTrace_append hprefix tailTrace_3208777
  have hstable : (prefixWord ++ tailWord_3208777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208777).length < 2 ^ (prefixWord ++ tailWord_3208777).sum := by decide
  have hdescent : baseEnd_3208777 < baseStart_3208777 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208804 : List Nat := [2, 3, 1, 1, 2, 3, 2, 2, 3, 4]
def baseStart_3208804 : Nat := 118140960795 + 3208804 * 2 ^ 59
def prefixEnd_3208804 : Nat := 4983230072969 + 3 ^ 40 * 3208804 * 2
def baseEnd_3208804 : Nat := 549219592689922924430995

theorem tailTrace_3208804 : CollatzResearch.WordTrace tailWord_3208804 prefixEnd_3208804 549219592689922924430995 := by
  unfold tailWord_3208804
  simp only [CollatzResearch.WordTrace]
  refine ⟨58517348333529301469100733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78023131111372401958800977 58517348333529301469100733)
  ·
    refine ⟨21944005625073488050912775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58517348333529301469100733 21944005625073488050912775)
    ·
      refine ⟨32916008437610232076369163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21944005625073488050912775 32916008437610232076369163)
      ·
        refine ⟨49374012656415348114553745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32916008437610232076369163 49374012656415348114553745)
        ·
          refine ⟨37030509492311511085915309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49374012656415348114553745 37030509492311511085915309)
          ·
            refine ⟨13886441059616816657218241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37030509492311511085915309 13886441059616816657218241)
            ·
              refine ⟨10414830794712612492913681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13886441059616816657218241 10414830794712612492913681)
              ·
                refine ⟨7811123096034459369685261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10414830794712612492913681 7811123096034459369685261)
                ·
                  refine ⟨2929171161012922263631973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7811123096034459369685261 2929171161012922263631973)
                  ·
                    refine ⟨549219592689922924430995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2929171161012922263631973 549219592689922924430995)
                    ·
                      rfl

theorem cell23_3208804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_3208804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208804 prefixEnd_3208804 := by exact prefixLift 3208804
  have htrace : WordTrace (prefixWord ++ tailWord_3208804) baseStart_3208804 baseEnd_3208804 := by
    simpa [prefixWord, tailWord_3208804, baseEnd_3208804] using wordTrace_append hprefix tailTrace_3208804
  have hstable : (prefixWord ++ tailWord_3208804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208804).length < 2 ^ (prefixWord ++ tailWord_3208804).sum := by decide
  have hdescent : baseEnd_3208804 < baseStart_3208804 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208864 : List Nat := [2, 1, 1, 4, 3, 2, 1, 1, 3, 5]
def baseStart_3208864 : Nat := 118140960795 + 3208864 * 2 ^ 59
def prefixEnd_3208864 : Nat := 4983230072969 + 3 ^ 40 * 3208864 * 2
def baseEnd_3208864 : Nat := 549229862303012846180903

theorem tailTrace_3208864 : CollatzResearch.WordTrace tailWord_3208864 prefixEnd_3208864 549229862303012846180903 := by
  unfold tailWord_3208864
  simp only [CollatzResearch.WordTrace]
  refine ⟨58518442523420616592692823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78024590031227488790257097 58518442523420616592692823)
  ·
    refine ⟨87777663785130924889039235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58518442523420616592692823 87777663785130924889039235)
    ·
      refine ⟨131666495677696387333558853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87777663785130924889039235 131666495677696387333558853)
      ·
        refine ⟨24687467939568072625042285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131666495677696387333558853 24687467939568072625042285)
        ·
          refine ⟨9257800477338027234390857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24687467939568072625042285 9257800477338027234390857)
          ·
            refine ⟨6943350358003520425793143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9257800477338027234390857 6943350358003520425793143)
            ·
              refine ⟨10415025537005280638689715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6943350358003520425793143 10415025537005280638689715)
              ·
                refine ⟨15622538305507920958034573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10415025537005280638689715 15622538305507920958034573)
                ·
                  refine ⟨5858451864565470359262965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15622538305507920958034573 5858451864565470359262965)
                  ·
                    refine ⟨549229862303012846180903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5858451864565470359262965 549229862303012846180903)
                    ·
                      rfl

theorem cell23_3208864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 1, 1, 3, 5].length) (baseStart_3208864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208864 prefixEnd_3208864 := by exact prefixLift 3208864
  have htrace : WordTrace (prefixWord ++ tailWord_3208864) baseStart_3208864 baseEnd_3208864 := by
    simpa [prefixWord, tailWord_3208864, baseEnd_3208864] using wordTrace_append hprefix tailTrace_3208864
  have hstable : (prefixWord ++ tailWord_3208864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208864).length < 2 ^ (prefixWord ++ tailWord_3208864).sum := by decide
  have hdescent : baseEnd_3208864 < baseStart_3208864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208904 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 5, 2, 3]
def baseStart_3208904 : Nat := 118140960795 + 3208904 * 2 ^ 59
def prefixEnd_3208904 : Nat := 4983230072969 + 3 ^ 40 * 3208904 * 2
def baseEnd_3208904 : Nat := 1647710126135218382042525

theorem tailTrace_3208904 : CollatzResearch.WordTrace tailWord_3208904 prefixEnd_3208904 1647710126135218382042525 := by
  unfold tailWord_3208904
  simp only [CollatzResearch.WordTrace]
  refine ⟨58519171983348160008420883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78025562644464213344561177 58519171983348160008420883)
  ·
    refine ⟨87778757975022240012631325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58519171983348160008420883 87778757975022240012631325)
    ·
      refine ⟨32917034240633340004736747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87778757975022240012631325 32917034240633340004736747)
      ·
        refine ⟨49375551360950010007105121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32917034240633340004736747 49375551360950010007105121)
        ·
          refine ⟨37031663520712507505328841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49375551360950010007105121 37031663520712507505328841)
          ·
            refine ⟨27773747640534380628996631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37031663520712507505328841 27773747640534380628996631)
            ·
              refine ⟨41660621460801570943494947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27773747640534380628996631 41660621460801570943494947)
              ·
                refine ⟨62490932191202356415242421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41660621460801570943494947 62490932191202356415242421)
                ·
                  refine ⟨5858524892925220913928977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62490932191202356415242421 5858524892925220913928977)
                  ·
                    refine ⟨4393893669693915685446733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5858524892925220913928977 4393893669693915685446733)
                    ·
                      refine ⟨1647710126135218382042525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4393893669693915685446733 1647710126135218382042525)
                      ·
                        rfl

theorem cell23_3208904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 5, 2, 3].length) (baseStart_3208904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208904 prefixEnd_3208904 := by exact prefixLift 3208904
  have htrace : WordTrace (prefixWord ++ tailWord_3208904) baseStart_3208904 baseEnd_3208904 := by
    simpa [prefixWord, tailWord_3208904, baseEnd_3208904] using wordTrace_append hprefix tailTrace_3208904
  have hstable : (prefixWord ++ tailWord_3208904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208904).length < 2 ^ (prefixWord ++ tailWord_3208904).sum := by decide
  have hdescent : baseEnd_3208904 < baseStart_3208904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208938 : List Nat := [3, 1, 3, 1, 1, 1, 6, 1, 1, 2, 3]
def baseStart_3208938 : Nat := 118140960795 + 3208938 * 2 ^ 59
def prefixEnd_3208938 : Nat := 4983230072969 + 3 ^ 40 * 3208938 * 2
def baseEnd_3208938 : Nat := 1647727584477471249017369

theorem tailTrace_3208938 : CollatzResearch.WordTrace tailWord_3208938 prefixEnd_3208938 1647727584477471249017369 := by
  unfold tailWord_3208938
  simp only [CollatzResearch.WordTrace]
  refine ⟨29259896012143285955894867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78026389365715429215719645 29259896012143285955894867)
  ·
    refine ⟨43889844018214928933842301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29259896012143285955894867 43889844018214928933842301)
    ·
      refine ⟨16458691506830598350190863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43889844018214928933842301 16458691506830598350190863)
      ·
        refine ⟨24688037260245897525286295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16458691506830598350190863 24688037260245897525286295)
        ·
          refine ⟨37032055890368846287929443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24688037260245897525286295 37032055890368846287929443)
          ·
            refine ⟨55548083835553269431894165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37032055890368846287929443 55548083835553269431894165)
            ·
              refine ⟨2603816429791559504620039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 55548083835553269431894165 2603816429791559504620039)
              ·
                refine ⟨3905724644687339256930059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2603816429791559504620039 3905724644687339256930059)
                ·
                  refine ⟨5858586967031008885395089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3905724644687339256930059 5858586967031008885395089)
                  ·
                    refine ⟨4393940225273256664046317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5858586967031008885395089 4393940225273256664046317)
                    ·
                      refine ⟨1647727584477471249017369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4393940225273256664046317 1647727584477471249017369)
                      ·
                        rfl

theorem cell23_3208938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 6, 1, 1, 2, 3].length) (baseStart_3208938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208938 prefixEnd_3208938 := by exact prefixLift 3208938
  have htrace : WordTrace (prefixWord ++ tailWord_3208938) baseStart_3208938 baseEnd_3208938 := by
    simpa [prefixWord, tailWord_3208938, baseEnd_3208938] using wordTrace_append hprefix tailTrace_3208938
  have hstable : (prefixWord ++ tailWord_3208938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208938).length < 2 ^ (prefixWord ++ tailWord_3208938).sum := by decide
  have hdescent : baseEnd_3208938 < baseStart_3208938 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208961 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 5, 3, 2]
def baseStart_3208961 : Nat := 118140960795 + 3208961 * 2 ^ 59
def prefixEnd_3208961 : Nat := 4983230072969 + 3 ^ 40 * 3208961 * 2
def baseEnd_3208961 : Nat := 1647739394532524659029763

theorem tailTrace_3208961 : CollatzResearch.WordTrace tailWord_3208961 prefixEnd_3208961 1647739394532524659029763 := by
  unfold tailWord_3208961
  simp only [CollatzResearch.WordTrace]
  refine ⟨117040422927489818751666737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78026948618326545834444491 117040422927489818751666737)
  ·
    refine ⟨87780317195617364063750053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117040422927489818751666737 87780317195617364063750053)
    ·
      refine ⟨16458809474178255761953135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87780317195617364063750053 16458809474178255761953135)
      ·
        refine ⟨24688214211267383642929703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16458809474178255761953135 24688214211267383642929703)
        ·
          refine ⟨37032321316901075464394555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24688214211267383642929703 37032321316901075464394555)
          ·
            refine ⟨55548481975351613196591833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37032321316901075464394555 55548481975351613196591833)
            ·
              refine ⟨41661361481513709897443875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55548481975351613196591833 41661361481513709897443875)
              ·
                refine ⟨62492042222270564846165813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41661361481513709897443875 62492042222270564846165813)
                ·
                  refine ⟨5858628958337865454328045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 62492042222270564846165813 5858628958337865454328045)
                  ·
                    refine ⟨2196985859376699545373017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5858628958337865454328045 2196985859376699545373017)
                    ·
                      refine ⟨1647739394532524659029763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2196985859376699545373017 1647739394532524659029763)
                      ·
                        rfl

theorem cell23_3208961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 3, 2].length) (baseStart_3208961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208961 prefixEnd_3208961 := by exact prefixLift 3208961
  have htrace : WordTrace (prefixWord ++ tailWord_3208961) baseStart_3208961 baseEnd_3208961 := by
    simpa [prefixWord, tailWord_3208961, baseEnd_3208961] using wordTrace_append hprefix tailTrace_3208961
  have hstable : (prefixWord ++ tailWord_3208961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208961).length < 2 ^ (prefixWord ++ tailWord_3208961).sum := by decide
  have hdescent : baseEnd_3208961 < baseStart_3208961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208974 : List Nat := [4, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4]
def baseStart_3208974 : Nat := 118140960795 + 3208974 * 2 ^ 59
def prefixEnd_3208974 : Nat := 4983230072969 + 3 ^ 40 * 3208974 * 2
def baseEnd_3208974 : Nat := 1647746069781033108167203

theorem tailTrace_3208974 : CollatzResearch.WordTrace tailWord_3208974 prefixEnd_3208974 1647746069781033108167203 := by
  unfold tailWord_3208974
  simp only [CollatzResearch.WordTrace]
  refine ⟨14630112134555340246486247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78027264717628481314593317 14630112134555340246486247)
  ·
    refine ⟨21945168201833010369729371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14630112134555340246486247 21945168201833010369729371)
    ·
      refine ⟨32917752302749515554594057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21945168201833010369729371 32917752302749515554594057)
      ·
        refine ⟨24688314227062136665945543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32917752302749515554594057 24688314227062136665945543)
        ·
          refine ⟨37032471340593204998918315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24688314227062136665945543 37032471340593204998918315)
          ·
            refine ⟨55548707010889807498377473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37032471340593204998918315 55548707010889807498377473)
            ·
              refine ⟨41661530258167355623783105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55548707010889807498377473 41661530258167355623783105)
              ·
                refine ⟨31246147693625516717837329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41661530258167355623783105 31246147693625516717837329)
                ·
                  refine ⟨23434610770219137538377997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31246147693625516717837329 23434610770219137538377997)
                  ·
                    refine ⟨8787979038832176576891749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23434610770219137538377997 8787979038832176576891749)
                    ·
                      refine ⟨1647746069781033108167203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8787979038832176576891749 1647746069781033108167203)
                      ·
                        rfl

theorem cell23_3208974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_3208974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208974 prefixEnd_3208974 := by exact prefixLift 3208974
  have htrace : WordTrace (prefixWord ++ tailWord_3208974) baseStart_3208974 baseEnd_3208974 := by
    simpa [prefixWord, tailWord_3208974, baseEnd_3208974] using wordTrace_append hprefix tailTrace_3208974
  have hstable : (prefixWord ++ tailWord_3208974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208974).length < 2 ^ (prefixWord ++ tailWord_3208974).sum := by decide
  have hdescent : baseEnd_3208974 < baseStart_3208974 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3208991 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 3, 4, 2]
def baseStart_3208991 : Nat := 118140960795 + 3208991 * 2 ^ 59
def prefixEnd_3208991 : Nat := 4983230072969 + 3 ^ 40 * 3208991 * 2
def baseEnd_3208991 : Nat := 1647754798952159541654625

theorem tailTrace_3208991 : CollatzResearch.WordTrace tailWord_3208991 prefixEnd_3208991 1647754798952159541654625 := by
  unfold tailWord_3208991
  simp only [CollatzResearch.WordTrace]
  refine ⟨117041517117381133875258827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78027678078254089250172551 117041517117381133875258827)
  ·
    refine ⟨175562275676071700812888241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117041517117381133875258827 175562275676071700812888241)
    ·
      refine ⟨131671706757053775609666181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175562275676071700812888241 131671706757053775609666181)
      ·
        refine ⟨24688445016947582926812409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131671706757053775609666181 24688445016947582926812409)
        ·
          refine ⟨18516333762710687195109307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24688445016947582926812409 18516333762710687195109307)
          ·
            refine ⟨27774500644066030792663961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18516333762710687195109307 27774500644066030792663961)
            ·
              refine ⟨20830875483049523094497971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27774500644066030792663961 20830875483049523094497971)
              ·
                refine ⟨31246313224574284641746957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20830875483049523094497971 31246313224574284641746957)
                ·
                  refine ⟨11717367459215356740655109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31246313224574284641746957 11717367459215356740655109)
                  ·
                    refine ⟨2197006398602879388872833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11717367459215356740655109 2197006398602879388872833)
                    ·
                      refine ⟨1647754798952159541654625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2197006398602879388872833 1647754798952159541654625)
                      ·
                        rfl

theorem cell23_3208991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 3, 4, 2].length) (baseStart_3208991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3208991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3208991 prefixEnd_3208991 := by exact prefixLift 3208991
  have htrace : WordTrace (prefixWord ++ tailWord_3208991) baseStart_3208991 baseEnd_3208991 := by
    simpa [prefixWord, tailWord_3208991, baseEnd_3208991] using wordTrace_append hprefix tailTrace_3208991
  have hstable : (prefixWord ++ tailWord_3208991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3208991).length < 2 ^ (prefixWord ++ tailWord_3208991).sum := by decide
  have hdescent : baseEnd_3208991 < baseStart_3208991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3208991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209074 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 2, 8]
def baseStart_3209074 : Nat := 118140960795 + 3209074 * 2 ^ 59
def prefixEnd_3209074 : Nat := 4983230072969 + 3 ^ 40 * 3209074 * 2
def baseEnd_3209074 : Nat := 549265805948827572305581

theorem tailTrace_3209074 : CollatzResearch.WordTrace tailWord_3209074 prefixEnd_3209074 549265805948827572305581 := by
  unfold tailWord_3209074
  simp only [CollatzResearch.WordTrace]
  refine ⟨29261136094020109762632569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78029696250720292700353517 29261136094020109762632569)
  ·
    refine ⟨21945852070515082321974427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29261136094020109762632569 21945852070515082321974427)
    ·
      refine ⟨32918778105772623482961641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21945852070515082321974427 32918778105772623482961641)
      ·
        refine ⟨24689083579329467612221231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32918778105772623482961641 24689083579329467612221231)
        ·
          refine ⟨37033625368994201418331847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24689083579329467612221231 37033625368994201418331847)
          ·
            refine ⟨55550438053491302127497771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37033625368994201418331847 55550438053491302127497771)
            ·
              refine ⟨83325657080236953191246657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55550438053491302127497771 83325657080236953191246657)
              ·
                refine ⟨62494242810177714893434993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83325657080236953191246657 62494242810177714893434993)
                ·
                  refine ⟨46870682107633286170076245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62494242810177714893434993 46870682107633286170076245)
                  ·
                    refine ⟨549265805948827572305581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 46870682107633286170076245 549265805948827572305581)
                    ·
                      rfl

theorem cell23_3209074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_3209074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209074 prefixEnd_3209074 := by exact prefixLift 3209074
  have htrace : WordTrace (prefixWord ++ tailWord_3209074) baseStart_3209074 baseEnd_3209074 := by
    simpa [prefixWord, tailWord_3209074, baseEnd_3209074] using wordTrace_append hprefix tailTrace_3209074
  have hstable : (prefixWord ++ tailWord_3209074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209074).length < 2 ^ (prefixWord ++ tailWord_3209074).sum := by decide
  have hdescent : baseEnd_3209074 < baseStart_3209074 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209091 : List Nat := [1, 1, 1, 3, 4, 2, 1, 1, 5, 4]
def baseStart_3209091 : Nat := 118140960795 + 3209091 * 2 ^ 59
def prefixEnd_3209091 : Nat := 4983230072969 + 3 ^ 40 * 3209091 * 2
def baseEnd_3209091 : Nat := 549268715672536383468055

theorem tailTrace_3209091 : CollatzResearch.WordTrace tailWord_3209091 prefixEnd_3209091 549268715672536383468055 := by
  unfold tailWord_3209091
  simp only [CollatzResearch.WordTrace]
  refine ⟨117045164417018850953899127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78030109611345900635932751 117045164417018850953899127)
  ·
    refine ⟨175567746625528276430848691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117045164417018850953899127 175567746625528276430848691)
    ·
      refine ⟨263351619938292414646273037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175567746625528276430848691 263351619938292414646273037)
      ·
        refine ⟨98756857476859655492352389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263351619938292414646273037 98756857476859655492352389)
        ·
          refine ⟨18516910776911185404816073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98756857476859655492352389 18516910776911185404816073)
          ·
            refine ⟨13887683082683389053612055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18516910776911185404816073 13887683082683389053612055)
            ·
              refine ⟨20831524624025083580418083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13887683082683389053612055 20831524624025083580418083)
              ·
                refine ⟨31247286936037625370627125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20831524624025083580418083 31247286936037625370627125)
                ·
                  refine ⟨2929433150253527378496293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31247286936037625370627125 2929433150253527378496293)
                  ·
                    refine ⟨549268715672536383468055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2929433150253527378496293 549268715672536383468055)
                    ·
                      rfl

theorem cell23_3209091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 1, 1, 5, 4].length) (baseStart_3209091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209091 prefixEnd_3209091 := by exact prefixLift 3209091
  have htrace : WordTrace (prefixWord ++ tailWord_3209091) baseStart_3209091 baseEnd_3209091 := by
    simpa [prefixWord, tailWord_3209091, baseEnd_3209091] using wordTrace_append hprefix tailTrace_3209091
  have hstable : (prefixWord ++ tailWord_3209091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209091).length < 2 ^ (prefixWord ++ tailWord_3209091).sum := by decide
  have hdescent : baseEnd_3209091 < baseStart_3209091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209095 : List Nat := [1, 1, 4, 2, 5, 1, 1, 1, 2, 5]
def baseStart_3209095 : Nat := 118140960795 + 3209095 * 2 ^ 59
def prefixEnd_3209095 : Nat := 4983230072969 + 3 ^ 40 * 3209095 * 2
def baseEnd_3209095 : Nat := 549269400313409044918049

theorem tailTrace_3209095 : CollatzResearch.WordTrace tailWord_3209095 prefixEnd_3209095 549269400313409044918049 := by
  unfold tailWord_3209095
  simp only [CollatzResearch.WordTrace]
  refine ⟨117045310309004359637044739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78030206872669573091363159 117045310309004359637044739)
  ·
    refine ⟨175567965463506539455567109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117045310309004359637044739 175567965463506539455567109)
    ·
      refine ⟨32918993524407476147918833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 175567965463506539455567109 32918993524407476147918833)
      ·
        refine ⟨24689245143305607110939125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32918993524407476147918833 24689245143305607110939125)
        ·
          refine ⟨2314616732184900666650543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24689245143305607110939125 2314616732184900666650543)
          ·
            refine ⟨3471925098277350999975815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2314616732184900666650543 3471925098277350999975815)
            ·
              refine ⟨5207887647416026499963723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3471925098277350999975815 5207887647416026499963723)
              ·
                refine ⟨7811831471124039749945585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5207887647416026499963723 7811831471124039749945585)
                ·
                  refine ⟨5858873603343029812459189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7811831471124039749945585 5858873603343029812459189)
                  ·
                    refine ⟨549269400313409044918049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5858873603343029812459189 549269400313409044918049)
                    ·
                      rfl

theorem cell23_3209095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_3209095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209095 prefixEnd_3209095 := by exact prefixLift 3209095
  have htrace : WordTrace (prefixWord ++ tailWord_3209095) baseStart_3209095 baseEnd_3209095 := by
    simpa [prefixWord, tailWord_3209095, baseEnd_3209095] using wordTrace_append hprefix tailTrace_3209095
  have hstable : (prefixWord ++ tailWord_3209095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209095).length < 2 ^ (prefixWord ++ tailWord_3209095).sum := by decide
  have hdescent : baseEnd_3209095 < baseStart_3209095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209098 : List Nat := [3, 1, 2, 4, 2, 1, 1, 1, 1, 3, 4]
def baseStart_3209098 : Nat := 118140960795 + 3209098 * 2 ^ 59
def prefixEnd_3209098 : Nat := 4983230072969 + 3 ^ 40 * 3209098 * 2
def baseEnd_3209098 : Nat := 1647809741382190623016633

theorem tailTrace_3209098 : CollatzResearch.WordTrace tailWord_3209098 prefixEnd_3209098 1647809741382190623016633 := by
  unfold tailWord_3209098
  simp only [CollatzResearch.WordTrace]
  refine ⟨29261354931998372787350987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78030279818662327432935965 29261354931998372787350987)
  ·
    refine ⟨43892032397997559181026481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29261354931998372787350987 43892032397997559181026481)
    ·
      refine ⟨32919024298498169385769861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43892032397997559181026481 32919024298498169385769861)
      ·
        refine ⟨6172317055968406759831849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32919024298498169385769861 6172317055968406759831849)
        ·
          refine ⟨4629237791976305069873887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6172317055968406759831849 4629237791976305069873887)
          ·
            refine ⟨6943856687964457604810831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4629237791976305069873887 6943856687964457604810831)
            ·
              refine ⟨10415785031946686407216247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6943856687964457604810831 10415785031946686407216247)
              ·
                refine ⟨15623677547920029610824371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10415785031946686407216247 15623677547920029610824371)
                ·
                  refine ⟨23435516321880044416236557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15623677547920029610824371 23435516321880044416236557)
                  ·
                    refine ⟨8788318620705016656088709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23435516321880044416236557 8788318620705016656088709)
                    ·
                      refine ⟨1647809741382190623016633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8788318620705016656088709 1647809741382190623016633)
                      ·
                        rfl

theorem cell23_3209098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_3209098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209098 prefixEnd_3209098 := by exact prefixLift 3209098
  have htrace : WordTrace (prefixWord ++ tailWord_3209098) baseStart_3209098 baseEnd_3209098 := by
    simpa [prefixWord, tailWord_3209098, baseEnd_3209098] using wordTrace_append hprefix tailTrace_3209098
  have hstable : (prefixWord ++ tailWord_3209098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209098).length < 2 ^ (prefixWord ++ tailWord_3209098).sum := by decide
  have hdescent : baseEnd_3209098 < baseStart_3209098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209265 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 3, 3, 2]
def baseStart_3209265 : Nat := 118140960795 + 3209265 * 2 ^ 59
def prefixEnd_3209265 : Nat := 4983230072969 + 3 ^ 40 * 3209265 * 2
def baseEnd_3209265 : Nat := 1647895492651491469628365

theorem tailTrace_3209265 : CollatzResearch.WordTrace tailWord_3209265 prefixEnd_3209265 1647895492651491469628365 := by
  unfold tailWord_3209265
  simp only [CollatzResearch.WordTrace]
  refine ⟨117051510718388478670733249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78034340478925652447155499 117051510718388478670733249)
  ·
    refine ⟨87788633038791359003049937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117051510718388478670733249 87788633038791359003049937)
    ·
      refine ⟨65841474779093519252287453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87788633038791359003049937 65841474779093519252287453)
      ·
        refine ⟨24690553042160069719607795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 65841474779093519252287453 24690553042160069719607795)
        ·
          refine ⟨37035829563240104579411693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24690553042160069719607795 37035829563240104579411693)
          ·
            refine ⟨13888436086215039217279385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37035829563240104579411693 13888436086215039217279385)
            ·
              refine ⟨10416327064661279412959539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13888436086215039217279385 10416327064661279412959539)
              ·
                refine ⟨15624490596991919119439309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10416327064661279412959539 15624490596991919119439309)
                ·
                  refine ⟨5859183973871969669789741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15624490596991919119439309 5859183973871969669789741)
                  ·
                    refine ⟨2197193990201988626171153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5859183973871969669789741 2197193990201988626171153)
                    ·
                      refine ⟨1647895492651491469628365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2197193990201988626171153 1647895492651491469628365)
                      ·
                        rfl

theorem cell23_3209265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_3209265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209265 prefixEnd_3209265 := by exact prefixLift 3209265
  have htrace : WordTrace (prefixWord ++ tailWord_3209265) baseStart_3209265 baseEnd_3209265 := by
    simpa [prefixWord, tailWord_3209265, baseEnd_3209265] using wordTrace_append hprefix tailTrace_3209265
  have hstable : (prefixWord ++ tailWord_3209265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209265).length < 2 ^ (prefixWord ++ tailWord_3209265).sum := by decide
  have hdescent : baseEnd_3209265 < baseStart_3209265 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209291 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 4]
def baseStart_3209291 : Nat := 118140960795 + 3209291 * 2 ^ 59
def prefixEnd_3209291 : Nat := 4983230072969 + 3 ^ 40 * 3209291 * 2
def baseEnd_3209291 : Nat := 1647908843148508367903245

theorem tailTrace_3209291 : CollatzResearch.WordTrace tailWord_3209291 prefixEnd_3209291 1647908843148508367903245 := by
  unfold tailWord_3209291
  simp only [CollatzResearch.WordTrace]
  refine ⟨117052459016294285111179727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78034972677529523407453151 117052459016294285111179727)
  ·
    refine ⟨175578688524441427666769591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117052459016294285111179727 175578688524441427666769591)
    ·
      refine ⟨263368032786662141500154387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175578688524441427666769591 263368032786662141500154387)
      ·
        refine ⟨395052049179993212250231581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263368032786662141500154387 395052049179993212250231581)
        ·
          refine ⟨148144518442497454593836843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395052049179993212250231581 148144518442497454593836843)
          ·
            refine ⟨222216777663746181890755265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148144518442497454593836843 222216777663746181890755265)
            ·
              refine ⟨166662583247809636418066449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222216777663746181890755265 166662583247809636418066449)
              ·
                refine ⟨124996937435857227313549837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166662583247809636418066449 124996937435857227313549837)
                ·
                  refine ⟨46873851538446460242581189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 124996937435857227313549837 46873851538446460242581189)
                  ·
                    refine ⟨8788847163458711295483973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46873851538446460242581189 8788847163458711295483973)
                    ·
                      refine ⟨1647908843148508367903245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8788847163458711295483973 1647908843148508367903245)
                      ·
                        rfl

theorem cell23_3209291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 4, 4].length) (baseStart_3209291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209291 prefixEnd_3209291 := by exact prefixLift 3209291
  have htrace : WordTrace (prefixWord ++ tailWord_3209291) baseStart_3209291 baseEnd_3209291 := by
    simpa [prefixWord, tailWord_3209291, baseEnd_3209291] using wordTrace_append hprefix tailTrace_3209291
  have hstable : (prefixWord ++ tailWord_3209291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209291).length < 2 ^ (prefixWord ++ tailWord_3209291).sum := by decide
  have hdescent : baseEnd_3209291 < baseStart_3209291 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209295 : List Nat := [1, 1, 2, 1, 1, 2, 2, 5, 4, 2, 2]
def baseStart_3209295 : Nat := 118140960795 + 3209295 * 2 ^ 59
def prefixEnd_3209295 : Nat := 4983230072969 + 3 ^ 40 * 3209295 * 2
def baseEnd_3209295 : Nat := 1647910897071126352253227

theorem tailTrace_3209295 : CollatzResearch.WordTrace tailWord_3209295 prefixEnd_3209295 1647910897071126352253227 := by
  unfold tailWord_3209295
  simp only [CollatzResearch.WordTrace]
  refine ⟨117052604908279793794325339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78035069938853195862883559 117052604908279793794325339)
  ·
    refine ⟨175578907362419690691488009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117052604908279793794325339 175578907362419690691488009)
    ·
      refine ⟨131684180521814768018616007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175578907362419690691488009 131684180521814768018616007)
      ·
        refine ⟨197526270782722152027924011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131684180521814768018616007 197526270782722152027924011)
        ·
          refine ⟨296289406174083228041886017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197526270782722152027924011 296289406174083228041886017)
          ·
            refine ⟨222217054630562421031414513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 296289406174083228041886017 222217054630562421031414513)
            ·
              refine ⟨166662790972921815773560885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222217054630562421031414513 166662790972921815773560885)
              ·
                refine ⟨15624636653711420228771333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 166662790972921815773560885 15624636653711420228771333)
                ·
                  refine ⟨2929619372570891292894625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15624636653711420228771333 2929619372570891292894625)
                  ·
                    refine ⟨2197214529428168469670969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2929619372570891292894625 2197214529428168469670969)
                    ·
                      refine ⟨1647910897071126352253227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2197214529428168469670969 1647910897071126352253227)
                      ·
                        rfl

theorem cell23_3209295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 2, 2].length) (baseStart_3209295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209295 prefixEnd_3209295 := by exact prefixLift 3209295
  have htrace : WordTrace (prefixWord ++ tailWord_3209295) baseStart_3209295 baseEnd_3209295 := by
    simpa [prefixWord, tailWord_3209295, baseEnd_3209295] using wordTrace_append hprefix tailTrace_3209295
  have hstable : (prefixWord ++ tailWord_3209295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209295).length < 2 ^ (prefixWord ++ tailWord_3209295).sum := by decide
  have hdescent : baseEnd_3209295 < baseStart_3209295 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209312 : List Nat := [2, 1, 1, 3, 2, 5, 1, 1, 1, 4, 2]
def baseStart_3209312 : Nat := 118140960795 + 3209312 * 2 ^ 59
def prefixEnd_3209312 : Nat := 4983230072969 + 3 ^ 40 * 3209312 * 2
def baseEnd_3209312 : Nat := 1647919626242252785740649

theorem tailTrace_3209312 : CollatzResearch.WordTrace tailWord_3209312 prefixEnd_3209312 1647919626242252785740649 := by
  unfold tailWord_3209312
  simp only [CollatzResearch.WordTrace]
  refine ⟨58526612474609102848847095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78035483299478803798462793 58526612474609102848847095)
  ·
    refine ⟨87789918711913654273270643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58526612474609102848847095 87789918711913654273270643)
    ·
      refine ⟨131684878067870481409905965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87789918711913654273270643 131684878067870481409905965)
      ·
        refine ⟨49381829275451430528714737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 131684878067870481409905965 49381829275451430528714737)
        ·
          refine ⟨37036371956588572896536053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49381829275451430528714737 37036371956588572896536053)
          ·
            refine ⟨3472159870930178709050255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37036371956588572896536053 3472159870930178709050255)
            ·
              refine ⟨5208239806395268063575383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3472159870930178709050255 5208239806395268063575383)
              ·
                refine ⟨7812359709592902095363075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5208239806395268063575383 7812359709592902095363075)
                ·
                  refine ⟨11718539564389353143044613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7812359709592902095363075 11718539564389353143044613)
                  ·
                    refine ⟨2197226168323003714320865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11718539564389353143044613 2197226168323003714320865)
                    ·
                      refine ⟨1647919626242252785740649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2197226168323003714320865 1647919626242252785740649)
                      ·
                        rfl

theorem cell23_3209312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 1, 1, 1, 4, 2].length) (baseStart_3209312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209312 prefixEnd_3209312 := by exact prefixLift 3209312
  have htrace : WordTrace (prefixWord ++ tailWord_3209312) baseStart_3209312 baseEnd_3209312 := by
    simpa [prefixWord, tailWord_3209312, baseEnd_3209312] using wordTrace_append hprefix tailTrace_3209312
  have hstable : (prefixWord ++ tailWord_3209312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209312).length < 2 ^ (prefixWord ++ tailWord_3209312).sum := by decide
  have hdescent : baseEnd_3209312 < baseStart_3209312 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209335 : List Nat := [1, 1, 3, 1, 1, 5, 3, 3, 5]
def baseStart_3209335 : Nat := 118140960795 + 3209335 * 2 ^ 59
def prefixEnd_3209335 : Nat := 4983230072969 + 3 ^ 40 * 3209335 * 2
def baseEnd_3209335 : Nat := 183103492921922910639227

theorem tailTrace_3209335 : CollatzResearch.WordTrace tailWord_3209335 prefixEnd_3209335 183103492921922910639227 := by
  unfold tailWord_3209335
  simp only [CollatzResearch.WordTrace]
  refine ⟨117054063828134880625781459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78036042552089920417187639 117054063828134880625781459)
  ·
    refine ⟨175581095742202320938672189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117054063828134880625781459 175581095742202320938672189)
    ·
      refine ⟨65842910903325870352002071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 175581095742202320938672189 65842910903325870352002071)
      ·
        refine ⟨98764366354988805528003107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65842910903325870352002071 98764366354988805528003107)
        ·
          refine ⟨148146549532483208292004661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98764366354988805528003107 148146549532483208292004661)
          ·
            refine ⟨13888739018670300777375437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 148146549532483208292004661 13888739018670300777375437)
            ·
              refine ⟨5208277132001362791515789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13888739018670300777375437 5208277132001362791515789)
              ·
                refine ⟨1953103924500511046818421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5208277132001362791515789 1953103924500511046818421)
                ·
                  refine ⟨183103492921922910639227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1953103924500511046818421 183103492921922910639227)
                  ·
                    rfl

theorem cell23_3209335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 3, 3, 5].length) (baseStart_3209335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209335 prefixEnd_3209335 := by exact prefixLift 3209335
  have htrace : WordTrace (prefixWord ++ tailWord_3209335) baseStart_3209335 baseEnd_3209335 := by
    simpa [prefixWord, tailWord_3209335, baseEnd_3209335] using wordTrace_append hprefix tailTrace_3209335
  have hstable : (prefixWord ++ tailWord_3209335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209335).length < 2 ^ (prefixWord ++ tailWord_3209335).sum := by decide
  have hdescent : baseEnd_3209335 < baseStart_3209335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209388 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 3]
def baseStart_3209388 : Nat := 118140960795 + 3209388 * 2 ^ 59
def prefixEnd_3209388 : Nat := 4983230072969 + 3 ^ 40 * 3209388 * 2
def baseEnd_3209388 : Nat := 1647958650771994488390299

theorem tailTrace_3209388 : CollatzResearch.WordTrace tailWord_3209388 prefixEnd_3209388 1647958650771994488390299 := by
  unfold tailWord_3209388
  simp only [CollatzResearch.WordTrace]
  refine ⟨58527998448471435338730409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78037331264628580451640545 58527998448471435338730409)
  ·
    refine ⟨43895998836353576504047807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58527998448471435338730409 43895998836353576504047807)
    ·
      refine ⟨65843998254530364756071711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43895998836353576504047807 65843998254530364756071711)
      ·
        refine ⟨98765997381795547134107567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65843998254530364756071711 98765997381795547134107567)
        ·
          refine ⟨148148996072693320701161351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98765997381795547134107567 148148996072693320701161351)
          ·
            refine ⟨222223494109039981051742027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148148996072693320701161351 222223494109039981051742027)
            ·
              refine ⟨333335241163559971577613041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222223494109039981051742027 333335241163559971577613041)
              ·
                refine ⟨250001430872669978683209781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333335241163559971577613041 250001430872669978683209781)
                ·
                  refine ⟨23437634144312810501550917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 250001430872669978683209781 23437634144312810501550917)
                  ·
                    refine ⟨4394556402058651969040797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23437634144312810501550917 4394556402058651969040797)
                    ·
                      refine ⟨1647958650771994488390299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4394556402058651969040797 1647958650771994488390299)
                      ·
                        rfl

theorem cell23_3209388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_3209388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209388 prefixEnd_3209388 := by exact prefixLift 3209388
  have htrace : WordTrace (prefixWord ++ tailWord_3209388) baseStart_3209388 baseEnd_3209388 := by
    simpa [prefixWord, tailWord_3209388, baseEnd_3209388] using wordTrace_append hprefix tailTrace_3209388
  have hstable : (prefixWord ++ tailWord_3209388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209388).length < 2 ^ (prefixWord ++ tailWord_3209388).sum := by decide
  have hdescent : baseEnd_3209388 < baseStart_3209388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209435 : List Nat := [1, 1, 1, 1, 1, 1, 1, 7, 5, 1, 3]
def baseStart_3209435 : Nat := 118140960795 + 3209435 * 2 ^ 59
def prefixEnd_3209435 : Nat := 4983230072969 + 3 ^ 40 * 3209435 * 2
def baseEnd_3209435 : Nat := 1647982784362755804502583

theorem tailTrace_3209435 : CollatzResearch.WordTrace tailWord_3209435 prefixEnd_3209435 1647982784362755804502583 := by
  unfold tailWord_3209435
  simp only [CollatzResearch.WordTrace]
  refine ⟨117057711127772597704421759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78038474085181731802947839 117057711127772597704421759)
  ·
    refine ⟨175586566691658896556632639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117057711127772597704421759 175586566691658896556632639)
    ·
      refine ⟨263379850037488344834948959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175586566691658896556632639 263379850037488344834948959)
      ·
        refine ⟨395069775056232517252423439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263379850037488344834948959 395069775056232517252423439)
        ·
          refine ⟨592604662584348775878635159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395069775056232517252423439 592604662584348775878635159)
          ·
            refine ⟨888906993876523163817952739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 592604662584348775878635159 888906993876523163817952739)
            ·
              refine ⟨1333360490814784745726929109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 888906993876523163817952739 1333360490814784745726929109)
              ·
                refine ⟨31250636503471517477974901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1333360490814784745726929109 31250636503471517477974901)
                ·
                  refine ⟨2929747172200454763560147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31250636503471517477974901 2929747172200454763560147)
                  ·
                    refine ⟨4394620758300682145340221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2929747172200454763560147 4394620758300682145340221)
                    ·
                      refine ⟨1647982784362755804502583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4394620758300682145340221 1647982784362755804502583)
                      ·
                        rfl

theorem cell23_3209435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 7, 5, 1, 3].length) (baseStart_3209435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209435 prefixEnd_3209435 := by exact prefixLift 3209435
  have htrace : WordTrace (prefixWord ++ tailWord_3209435) baseStart_3209435 baseEnd_3209435 := by
    simpa [prefixWord, tailWord_3209435, baseEnd_3209435] using wordTrace_append hprefix tailTrace_3209435
  have hstable : (prefixWord ++ tailWord_3209435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209435).length < 2 ^ (prefixWord ++ tailWord_3209435).sum := by decide
  have hdescent : baseEnd_3209435 < baseStart_3209435 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209436 : List Nat := [2, 2, 5, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_3209436 : Nat := 118140960795 + 3209436 * 2 ^ 59
def prefixEnd_3209436 : Nat := 4983230072969 + 3 ^ 40 * 3209436 * 2
def baseEnd_3209436 : Nat := 1647983297843410300590079

theorem tailTrace_3209436 : CollatzResearch.WordTrace tailWord_3209436 prefixEnd_3209436 1647983297843410300590079 := by
  unfold tailWord_3209436
  simp only [CollatzResearch.WordTrace]
  refine ⟨58528873800384487437604081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78038498400512649916805441 58528873800384487437604081)
  ·
    refine ⟨43896655350288365578203061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58528873800384487437604081 43896655350288365578203061)
    ·
      refine ⟨4115311439089534272956537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43896655350288365578203061 4115311439089534272956537)
      ·
        refine ⟨3086483579317150704717403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4115311439089534272956537 3086483579317150704717403)
        ·
          refine ⟨4629725368975726057076105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3086483579317150704717403 4629725368975726057076105)
          ·
            refine ⟨3472294026731794542807079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4629725368975726057076105 3472294026731794542807079)
            ·
              refine ⟨5208441040097691814210619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3472294026731794542807079 5208441040097691814210619)
              ·
                refine ⟨7812661560146537721315929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5208441040097691814210619 7812661560146537721315929)
                ·
                  refine ⟨5859496170109903290986947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7812661560146537721315929 5859496170109903290986947)
                  ·
                    refine ⟨8789244255164854936480421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5859496170109903290986947 8789244255164854936480421)
                    ·
                      refine ⟨1647983297843410300590079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8789244255164854936480421 1647983297843410300590079)
                      ·
                        rfl

theorem cell23_3209436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_3209436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209436 prefixEnd_3209436 := by exact prefixLift 3209436
  have htrace : WordTrace (prefixWord ++ tailWord_3209436) baseStart_3209436 baseEnd_3209436 := by
    simpa [prefixWord, tailWord_3209436, baseEnd_3209436] using wordTrace_append hprefix tailTrace_3209436
  have hstable : (prefixWord ++ tailWord_3209436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209436).length < 2 ^ (prefixWord ++ tailWord_3209436).sum := by decide
  have hdescent : baseEnd_3209436 < baseStart_3209436 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209505 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 1, 2, 4]
def baseStart_3209505 : Nat := 118140960795 + 3209505 * 2 ^ 59
def prefixEnd_3209505 : Nat := 4983230072969 + 3 ^ 40 * 3209505 * 2
def baseEnd_3209505 : Nat := 1648018728008570530627261

theorem tailTrace_3209505 : CollatzResearch.WordTrace tailWord_3209505 prefixEnd_3209505 1648018728008570530627261 := by
  unfold tailWord_3209505
  simp only [CollatzResearch.WordTrace]
  refine ⟨117060264237518999659469969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78040176158345999772979979 117060264237518999659469969)
  ·
    refine ⟨87795198178139249744602477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117060264237518999659469969 87795198178139249744602477)
    ·
      refine ⟨32923199316802218654225929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87795198178139249744602477 32923199316802218654225929)
      ·
        refine ⟨24692399487601663990669447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32923199316802218654225929 24692399487601663990669447)
        ·
          refine ⟨37038599231402495986004171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24692399487601663990669447 37038599231402495986004171)
          ·
            refine ⟨55557898847103743979006257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37038599231402495986004171 55557898847103743979006257)
            ·
              refine ⟨41668424135327807984254693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55557898847103743979006257 41668424135327807984254693)
              ·
                refine ⟨7812829525373963997047755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41668424135327807984254693 7812829525373963997047755)
                ·
                  refine ⟨11719244288060945995571633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7812829525373963997047755 11719244288060945995571633)
                  ·
                    refine ⟨8789433216045709496678725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11719244288060945995571633 8789433216045709496678725)
                    ·
                      refine ⟨1648018728008570530627261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8789433216045709496678725 1648018728008570530627261)
                      ·
                        rfl

theorem cell23_3209505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_3209505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209505 prefixEnd_3209505 := by exact prefixLift 3209505
  have htrace : WordTrace (prefixWord ++ tailWord_3209505) baseStart_3209505 baseEnd_3209505 := by
    simpa [prefixWord, tailWord_3209505, baseEnd_3209505] using wordTrace_append hprefix tailTrace_3209505
  have hstable : (prefixWord ++ tailWord_3209505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209505).length < 2 ^ (prefixWord ++ tailWord_3209505).sum := by decide
  have hdescent : baseEnd_3209505 < baseStart_3209505 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209566 : List Nat := [4, 4, 2, 1, 1, 11]
def baseStart_3209566 : Nat := 118140960795 + 3209566 * 2 ^ 59
def prefixEnd_3209566 : Nat := 4983230072969 + 3 ^ 40 * 3209566 * 2
def baseEnd_3209566 : Nat := 6782098972545246057467

theorem tailTrace_3209566 : CollatzResearch.WordTrace tailWord_3209566 prefixEnd_3209566 6782098972545246057467 := by
  unfold tailWord_3209566
  simp only [CollatzResearch.WordTrace]
  refine ⟨14632811136287250884680069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78041659393532004718293701 14632811136287250884680069)
  ·
    refine ⟨2743652088053859540877513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14632811136287250884680069 2743652088053859540877513)
    ·
      refine ⟨2057739066040394655658135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2743652088053859540877513 2057739066040394655658135)
      ·
        refine ⟨3086608599060591983487203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2057739066040394655658135 3086608599060591983487203)
        ·
          refine ⟨4629912898590887975230805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3086608599060591983487203 4629912898590887975230805)
          ·
            refine ⟨6782098972545246057467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4629912898590887975230805 6782098972545246057467)
            ·
              rfl

theorem cell23_3209566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 11].length) (baseStart_3209566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209566 prefixEnd_3209566 := by exact prefixLift 3209566
  have htrace : WordTrace (prefixWord ++ tailWord_3209566) baseStart_3209566 baseEnd_3209566 := by
    simpa [prefixWord, tailWord_3209566, baseEnd_3209566] using wordTrace_append hprefix tailTrace_3209566
  have hstable : (prefixWord ++ tailWord_3209566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209566).length < 2 ^ (prefixWord ++ tailWord_3209566).sum := by decide
  have hdescent : baseEnd_3209566 < baseStart_3209566 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209576 : List Nat := [2, 1, 4, 2, 2, 2, 2, 2, 2, 1, 3]
def baseStart_3209576 : Nat := 118140960795 + 3209576 * 2 ^ 59
def prefixEnd_3209576 : Nat := 4983230072969 + 3 ^ 40 * 3209576 * 2
def baseEnd_3209576 : Nat := 1648055185135039752839435

theorem tailTrace_3209576 : CollatzResearch.WordTrace tailWord_3209576 prefixEnd_3209576 1648055185135039752839435 := by
  unfold tailWord_3209576
  simp only [CollatzResearch.WordTrace]
  refine ⟨58531426910130889392652291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78041902546841185856869721 58531426910130889392652291)
  ·
    refine ⟨87797140365196334088978437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58531426910130889392652291 87797140365196334088978437)
    ·
      refine ⟨16461963818474312641683457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 87797140365196334088978437 16461963818474312641683457)
      ·
        refine ⟨12346472863855734481262593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16461963818474312641683457 12346472863855734481262593)
        ·
          refine ⟨9259854647891800860946945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12346472863855734481262593 9259854647891800860946945)
          ·
            refine ⟨6944890985918850645710209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9259854647891800860946945 6944890985918850645710209)
            ·
              refine ⟨5208668239439137984282657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6944890985918850645710209 5208668239439137984282657)
              ·
                refine ⟨3906501179579353488211993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5208668239439137984282657 3906501179579353488211993)
                ·
                  refine ⟨2929875884684515116158995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3906501179579353488211993 2929875884684515116158995)
                  ·
                    refine ⟨4394813827026772674238493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2929875884684515116158995 4394813827026772674238493)
                    ·
                      refine ⟨1648055185135039752839435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4394813827026772674238493 1648055185135039752839435)
                      ·
                        rfl

theorem cell23_3209576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_3209576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209576 prefixEnd_3209576 := by exact prefixLift 3209576
  have htrace : WordTrace (prefixWord ++ tailWord_3209576) baseStart_3209576 baseEnd_3209576 := by
    simpa [prefixWord, tailWord_3209576, baseEnd_3209576] using wordTrace_append hprefix tailTrace_3209576
  have hstable : (prefixWord ++ tailWord_3209576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209576).length < 2 ^ (prefixWord ++ tailWord_3209576).sum := by decide
  have hdescent : baseEnd_3209576 < baseStart_3209576 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209595 : List Nat := [1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 4]
def baseStart_3209595 : Nat := 118140960795 + 3209595 * 2 ^ 59
def prefixEnd_3209595 : Nat := 4983230072969 + 3 ^ 40 * 3209595 * 2
def baseEnd_3209595 : Nat := 1648064941267475178501847

theorem tailTrace_3209595 : CollatzResearch.WordTrace tailWord_3209595 prefixEnd_3209595 1648064941267475178501847 := by
  unfold tailWord_3209595
  simp only [CollatzResearch.WordTrace]
  refine ⟨117063546807192945030246239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78042364538128630020164159 117063546807192945030246239)
  ·
    refine ⟨175595320210789417545369359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117063546807192945030246239 175595320210789417545369359)
    ·
      refine ⟨263392980316184126318054039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175595320210789417545369359 263392980316184126318054039)
      ·
        refine ⟨395089470474276189477081059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263392980316184126318054039 395089470474276189477081059)
        ·
          refine ⟨592634205711414284215621589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395089470474276189477081059 592634205711414284215621589)
          ·
            refine ⟨13889864196361272286303631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 592634205711414284215621589 13889864196361272286303631)
            ·
              refine ⟨20834796294541908429455447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13889864196361272286303631 20834796294541908429455447)
              ·
                refine ⟨31252194441812862644183171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20834796294541908429455447 31252194441812862644183171)
                ·
                  refine ⟨46878291662719293966274757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31252194441812862644183171 46878291662719293966274757)
                  ·
                    refine ⟨8789679686759867618676517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46878291662719293966274757 8789679686759867618676517)
                    ·
                      refine ⟨1648064941267475178501847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8789679686759867618676517 1648064941267475178501847)
                      ·
                        rfl

theorem cell23_3209595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 4].length) (baseStart_3209595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209595 prefixEnd_3209595 := by exact prefixLift 3209595
  have htrace : WordTrace (prefixWord ++ tailWord_3209595) baseStart_3209595 baseEnd_3209595 := by
    simpa [prefixWord, tailWord_3209595, baseEnd_3209595] using wordTrace_append hprefix tailTrace_3209595
  have hstable : (prefixWord ++ tailWord_3209595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209595).length < 2 ^ (prefixWord ++ tailWord_3209595).sum := by decide
  have hdescent : baseEnd_3209595 < baseStart_3209595 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209620 : List Nat := [2, 4, 2, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_3209620 : Nat := 118140960795 + 3209620 * 2 ^ 59
def prefixEnd_3209620 : Nat := 4983230072969 + 3 ^ 40 * 3209620 * 2
def baseEnd_3209620 : Nat := 1648077778283837580689233

theorem tailTrace_3209620 : CollatzResearch.WordTrace tailWord_3209620 prefixEnd_3209620 1648077778283837580689233 := by
  unfold tailWord_3209620
  simp only [CollatzResearch.WordTrace]
  refine ⟨58532229316051187149953157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78042972421401582866604209 58532229316051187149953157)
  ·
    refine ⟨10974792996759597590616217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 58532229316051187149953157 10974792996759597590616217)
    ·
      refine ⟨8231094747569698192962163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10974792996759597590616217 8231094747569698192962163)
      ·
        refine ⟨12346642121354547289443245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8231094747569698192962163 12346642121354547289443245)
        ·
          refine ⟨4629990795507955233541217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12346642121354547289443245 4629990795507955233541217)
          ·
            refine ⟨3472493096630966425155913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4629990795507955233541217 3472493096630966425155913)
            ·
              refine ⟨2604369822473224818866935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3472493096630966425155913 2604369822473224818866935)
              ·
                refine ⟨3906554733709837228300403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2604369822473224818866935 3906554733709837228300403)
                ·
                  refine ⟨5859832100564755842450605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906554733709837228300403 5859832100564755842450605)
                  ·
                    refine ⟨2197437037711783440918977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5859832100564755842450605 2197437037711783440918977)
                    ·
                      refine ⟨1648077778283837580689233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2197437037711783440918977 1648077778283837580689233)
                      ·
                        rfl

theorem cell23_3209620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_3209620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209620 prefixEnd_3209620 := by exact prefixLift 3209620
  have htrace : WordTrace (prefixWord ++ tailWord_3209620) baseStart_3209620 baseEnd_3209620 := by
    simpa [prefixWord, tailWord_3209620, baseEnd_3209620] using wordTrace_append hprefix tailTrace_3209620
  have hstable : (prefixWord ++ tailWord_3209620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209620).length < 2 ^ (prefixWord ++ tailWord_3209620).sum := by decide
  have hdescent : baseEnd_3209620 < baseStart_3209620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209632 : List Nat := [2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 3]
def baseStart_3209632 : Nat := 118140960795 + 3209632 * 2 ^ 59
def prefixEnd_3209632 : Nat := 4983230072969 + 3 ^ 40 * 3209632 * 2
def baseEnd_3209632 : Nat := 1648083940051691533739177

theorem tailTrace_3209632 : CollatzResearch.WordTrace tailWord_3209632 prefixEnd_3209632 1648083940051691533739177 := by
  unfold tailWord_3209632
  simp only [CollatzResearch.WordTrace]
  refine ⟨58532448154029450174671575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78043264205372600232895433 58532448154029450174671575)
  ·
    refine ⟨87798672231044175262007363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58532448154029450174671575 87798672231044175262007363)
    ·
      refine ⟨131698008346566262893011045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87798672231044175262007363 131698008346566262893011045)
      ·
        refine ⟨24693376564981174292439571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131698008346566262893011045 24693376564981174292439571)
        ·
          refine ⟨37040064847471761438659357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24693376564981174292439571 37040064847471761438659357)
          ·
            refine ⟨13890024317801910539497259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37040064847471761438659357 13890024317801910539497259)
            ·
              refine ⟨20835036476702865809245889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13890024317801910539497259 20835036476702865809245889)
              ·
                refine ⟨15626277357527149356934417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20835036476702865809245889 15626277357527149356934417)
                ·
                  refine ⟨11719708018145362017700813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15626277357527149356934417 11719708018145362017700813)
                  ·
                    refine ⟨4394890506804510756637805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11719708018145362017700813 4394890506804510756637805)
                    ·
                      refine ⟨1648083940051691533739177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4394890506804510756637805 1648083940051691533739177)
                      ·
                        rfl

theorem cell23_3209632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 3].length) (baseStart_3209632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209632 prefixEnd_3209632 := by exact prefixLift 3209632
  have htrace : WordTrace (prefixWord ++ tailWord_3209632) baseStart_3209632 baseEnd_3209632 := by
    simpa [prefixWord, tailWord_3209632, baseEnd_3209632] using wordTrace_append hprefix tailTrace_3209632
  have hstable : (prefixWord ++ tailWord_3209632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209632).length < 2 ^ (prefixWord ++ tailWord_3209632).sum := by decide
  have hdescent : baseEnd_3209632 < baseStart_3209632 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209633 : List Nat := [1, 2, 3, 5, 1, 1, 1, 1, 4, 2, 2]
def baseStart_3209633 : Nat := 118140960795 + 3209633 * 2 ^ 59
def prefixEnd_3209633 : Nat := 4983230072969 + 3 ^ 40 * 3209633 * 2
def baseEnd_3209633 : Nat := 1648084453532346029826673

theorem tailTrace_3209633 : CollatzResearch.WordTrace tailWord_3209633 prefixEnd_3209633 1648084453532346029826673 := by
  unfold tailWord_3209633
  simp only [CollatzResearch.WordTrace]
  refine ⟨117064932781055277520129553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78043288520703518346753035 117064932781055277520129553)
  ·
    refine ⟨87798699585791458140097165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117064932781055277520129553 87798699585791458140097165)
    ·
      refine ⟨32924512344671796802536437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87798699585791458140097165 32924512344671796802536437)
      ·
        refine ⟨3086673032312980950237791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32924512344671796802536437 3086673032312980950237791)
        ·
          refine ⟨4630009548469471425356687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3086673032312980950237791 4630009548469471425356687)
          ·
            refine ⟨6945014322704207138035031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4630009548469471425356687 6945014322704207138035031)
            ·
              refine ⟨10417521484056310707052547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6945014322704207138035031 10417521484056310707052547)
              ·
                refine ⟨15626282226084466060578821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10417521484056310707052547 15626282226084466060578821)
                ·
                  refine ⟨2929927917390837386358529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15626282226084466060578821 2929927917390837386358529)
                  ·
                    refine ⟨2197445938043128039768897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2929927917390837386358529 2197445938043128039768897)
                    ·
                      refine ⟨1648084453532346029826673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2197445938043128039768897 1648084453532346029826673)
                      ·
                        rfl

theorem cell23_3209633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_3209633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209633 prefixEnd_3209633 := by exact prefixLift 3209633
  have htrace : WordTrace (prefixWord ++ tailWord_3209633) baseStart_3209633 baseEnd_3209633 := by
    simpa [prefixWord, tailWord_3209633, baseEnd_3209633] using wordTrace_append hprefix tailTrace_3209633
  have hstable : (prefixWord ++ tailWord_3209633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209633).length < 2 ^ (prefixWord ++ tailWord_3209633).sum := by decide
  have hdescent : baseEnd_3209633 < baseStart_3209633 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209639 : List Nat := [1, 1, 6, 1, 1, 2, 2, 4, 5]
def baseStart_3209639 : Nat := 118140960795 + 3209639 * 2 ^ 59
def prefixEnd_3209639 : Nat := 4983230072969 + 3 ^ 40 * 3209639 * 2
def baseEnd_3209639 : Nat := 183120837157363667372405

theorem tailTrace_3209639 : CollatzResearch.WordTrace tailWord_3209639 prefixEnd_3209639 183120837157363667372405 := by
  unfold tailWord_3209639
  simp only [CollatzResearch.WordTrace]
  refine ⟨117065151619033540544847971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78043434412689027029898647 117065151619033540544847971)
  ·
    refine ⟨175597727428550310817271957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117065151619033540544847971 175597727428550310817271957)
    ·
      refine ⟨8231143473213295819559623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 175597727428550310817271957 8231143473213295819559623)
      ·
        refine ⟨12346715209819943729339435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8231143473213295819559623 12346715209819943729339435)
        ·
          refine ⟨18520072814729915594009153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12346715209819943729339435 18520072814729915594009153)
          ·
            refine ⟨13890054611047436695506865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18520072814729915594009153 13890054611047436695506865)
            ·
              refine ⟨10417540958285577521630149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13890054611047436695506865 10417540958285577521630149)
              ·
                refine ⟨1953288929678545785305653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10417540958285577521630149 1953288929678545785305653)
                ·
                  refine ⟨183120837157363667372405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1953288929678545785305653 183120837157363667372405)
                  ·
                    rfl

theorem cell23_3209639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 5].length) (baseStart_3209639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209639 prefixEnd_3209639 := by exact prefixLift 3209639
  have htrace : WordTrace (prefixWord ++ tailWord_3209639) baseStart_3209639 baseEnd_3209639 := by
    simpa [prefixWord, tailWord_3209639, baseEnd_3209639] using wordTrace_append hprefix tailTrace_3209639
  have hstable : (prefixWord ++ tailWord_3209639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209639).length < 2 ^ (prefixWord ++ tailWord_3209639).sum := by decide
  have hdescent : baseEnd_3209639 < baseStart_3209639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209672 : List Nat := [2, 1, 3, 1, 3, 2, 2, 1, 1, 3, 4]
def baseStart_3209672 : Nat := 118140960795 + 3209672 * 2 ^ 59
def prefixEnd_3209672 : Nat := 4983230072969 + 3 ^ 40 * 3209672 * 2
def baseEnd_3209672 : Nat := 1648104479277871377238993

theorem tailTrace_3209672 : CollatzResearch.WordTrace tailWord_3209672 prefixEnd_3209672 1648104479277871377238993 := by
  unfold tailWord_3209672
  simp only [CollatzResearch.WordTrace]
  refine ⟨58533177613956993590399635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78044236818609324787199513 58533177613956993590399635)
  ·
    refine ⟨87799766420935490385599453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58533177613956993590399635 87799766420935490385599453)
    ·
      refine ⟨32924912407850808894599795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87799766420935490385599453 32924912407850808894599795)
      ·
        refine ⟨49387368611776213341899693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32924912407850808894599795 49387368611776213341899693)
        ·
          refine ⟨18520263229416080003212385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 49387368611776213341899693 18520263229416080003212385)
          ·
            refine ⟨13890197422062060002409289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18520263229416080003212385 13890197422062060002409289)
            ·
              refine ⟨10417648066546545001806967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13890197422062060002409289 10417648066546545001806967)
              ·
                refine ⟨15626472099819817502710451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10417648066546545001806967 15626472099819817502710451)
                ·
                  refine ⟨23439708149729726254065677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15626472099819817502710451 23439708149729726254065677)
                  ·
                    refine ⟨8789890556148647345274629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23439708149729726254065677 8789890556148647345274629)
                    ·
                      refine ⟨1648104479277871377238993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8789890556148647345274629 1648104479277871377238993)
                      ·
                        rfl

theorem cell23_3209672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_3209672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209672 prefixEnd_3209672 := by exact prefixLift 3209672
  have htrace : WordTrace (prefixWord ++ tailWord_3209672) baseStart_3209672 baseEnd_3209672 := by
    simpa [prefixWord, tailWord_3209672, baseEnd_3209672] using wordTrace_append hprefix tailTrace_3209672
  have hstable : (prefixWord ++ tailWord_3209672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209672).length < 2 ^ (prefixWord ++ tailWord_3209672).sum := by decide
  have hdescent : baseEnd_3209672 < baseStart_3209672 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209675 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 5]
def baseStart_3209675 : Nat := 118140960795 + 3209675 * 2 ^ 59
def prefixEnd_3209675 : Nat := 4983230072969 + 3 ^ 40 * 3209675 * 2
def baseEnd_3209675 : Nat := 1648106019719834865501479

theorem tailTrace_3209675 : CollatzResearch.WordTrace tailWord_3209675 prefixEnd_3209675 1648106019719834865501479 := by
  unfold tailWord_3209675
  simp only [CollatzResearch.WordTrace]
  refine ⟨117066464646903118693158479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78044309764602079128772319 117066464646903118693158479)
  ·
    refine ⟨175599696970354678039737719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117066464646903118693158479 175599696970354678039737719)
    ·
      refine ⟨263399545455532017059606579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175599696970354678039737719 263399545455532017059606579)
      ·
        refine ⟨395099318183298025589409869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263399545455532017059606579 395099318183298025589409869)
        ·
          refine ⟨148162244318736759596028701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395099318183298025589409869 148162244318736759596028701)
          ·
            refine ⟨55560841619526284848510763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148162244318736759596028701 55560841619526284848510763)
            ·
              refine ⟨83341262429289427272766145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55560841619526284848510763 83341262429289427272766145)
              ·
                refine ⟨62505946821967070454574609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83341262429289427272766145 62505946821967070454574609)
                ·
                  refine ⟨46879460116475302840930957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 62505946821967070454574609 46879460116475302840930957)
                  ·
                    refine ⟨17579797543678238565349109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46879460116475302840930957 17579797543678238565349109)
                    ·
                      refine ⟨1648106019719834865501479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17579797543678238565349109 1648106019719834865501479)
                      ·
                        rfl

theorem cell23_3209675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_3209675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209675 prefixEnd_3209675 := by exact prefixLift 3209675
  have htrace : WordTrace (prefixWord ++ tailWord_3209675) baseStart_3209675 baseEnd_3209675 := by
    simpa [prefixWord, tailWord_3209675, baseEnd_3209675] using wordTrace_append hprefix tailTrace_3209675
  have hstable : (prefixWord ++ tailWord_3209675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209675).length < 2 ^ (prefixWord ++ tailWord_3209675).sum := by decide
  have hdescent : baseEnd_3209675 < baseStart_3209675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209712 : List Nat := [2, 1, 1, 1, 3, 3, 3, 3, 6]
def baseStart_3209712 : Nat := 118140960795 + 3209712 * 2 ^ 59
def prefixEnd_3209712 : Nat := 4983230072969 + 3 ^ 40 * 3209712 * 2
def baseEnd_3209712 : Nat := 183125002056005691193201

theorem tailTrace_3209712 : CollatzResearch.WordTrace tailWord_3209712 prefixEnd_3209712 183125002056005691193201 := by
  unfold tailWord_3209712
  simp only [CollatzResearch.WordTrace]
  refine ⟨58533907073884537006127695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78045209431846049341503593 58533907073884537006127695)
  ·
    refine ⟨87800860610826805509191543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58533907073884537006127695 87800860610826805509191543)
    ·
      refine ⟨131701290916240208263787315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87800860610826805509191543 131701290916240208263787315)
      ·
        refine ⟨197551936374360312395680973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131701290916240208263787315 197551936374360312395680973)
        ·
          refine ⟨74081976140385117148380365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197551936374360312395680973 74081976140385117148380365)
          ·
            refine ⟨27780741052644418930642637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 74081976140385117148380365 27780741052644418930642637)
            ·
              refine ⟨10417777894741657098990989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27780741052644418930642637 10417777894741657098990989)
              ·
                refine ⟨3906666710528121412121621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10417777894741657098990989 3906666710528121412121621)
                ·
                  refine ⟨183125002056005691193201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3906666710528121412121621 183125002056005691193201)
                  ·
                    rfl

theorem cell23_3209712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 3, 3, 6].length) (baseStart_3209712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209712 prefixEnd_3209712 := by exact prefixLift 3209712
  have htrace : WordTrace (prefixWord ++ tailWord_3209712) baseStart_3209712 baseEnd_3209712 := by
    simpa [prefixWord, tailWord_3209712, baseEnd_3209712] using wordTrace_append hprefix tailTrace_3209712
  have hstable : (prefixWord ++ tailWord_3209712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209712).length < 2 ^ (prefixWord ++ tailWord_3209712).sum := by decide
  have hdescent : baseEnd_3209712 < baseStart_3209712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209779 : List Nat := [1, 1, 1, 2, 4, 2, 2, 4, 1, 1, 4]
def baseStart_3209779 : Nat := 118140960795 + 3209779 * 2 ^ 59
def prefixEnd_3209779 : Nat := 4983230072969 + 3 ^ 40 * 3209779 * 2
def baseEnd_3209779 : Nat := 1648159421707902458601001

theorem tailTrace_3209779 : CollatzResearch.WordTrace tailWord_3209779 prefixEnd_3209779 1648159421707902458601001 := by
  unfold tailWord_3209779
  simp only [CollatzResearch.WordTrace]
  refine ⟨117070257838526344454944391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78046838559017562969962927 117070257838526344454944391)
  ·
    refine ⟨175605386757789516682416587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117070257838526344454944391 175605386757789516682416587)
    ·
      refine ⟨263408080136684275023624881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175605386757789516682416587 263408080136684275023624881)
      ·
        refine ⟨197556060102513206267718661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263408080136684275023624881 197556060102513206267718661)
        ·
          refine ⟨37041761269221226175197249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 197556060102513206267718661 37041761269221226175197249)
          ·
            refine ⟨27781320951915919631397937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37041761269221226175197249 27781320951915919631397937)
            ·
              refine ⟨20835990713936939723548453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27781320951915919631397937 20835990713936939723548453)
              ·
                refine ⟨3906748258863176198165335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20835990713936939723548453 3906748258863176198165335)
                ·
                  refine ⟨5860122388294764297248003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906748258863176198165335 5860122388294764297248003)
                  ·
                    refine ⟨8790183582442146445872005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5860122388294764297248003 8790183582442146445872005)
                    ·
                      refine ⟨1648159421707902458601001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8790183582442146445872005 1648159421707902458601001)
                      ·
                        rfl

theorem cell23_3209779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 1, 4].length) (baseStart_3209779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209779 prefixEnd_3209779 := by exact prefixLift 3209779
  have htrace : WordTrace (prefixWord ++ tailWord_3209779) baseStart_3209779 baseEnd_3209779 := by
    simpa [prefixWord, tailWord_3209779, baseEnd_3209779] using wordTrace_append hprefix tailTrace_3209779
  have hstable : (prefixWord ++ tailWord_3209779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209779).length < 2 ^ (prefixWord ++ tailWord_3209779).sum := by decide
  have hdescent : baseEnd_3209779 < baseStart_3209779 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209789 : List Nat := [1, 4, 1, 3, 2, 1, 2, 2, 1, 6]
def baseStart_3209789 : Nat := 118140960795 + 3209789 * 2 ^ 59
def prefixEnd_3209789 : Nat := 4983230072969 + 3 ^ 40 * 3209789 * 2
def baseEnd_3209789 : Nat := 549388185504815806491985

theorem tailTrace_3209789 : CollatzResearch.WordTrace tailWord_3209789 prefixEnd_3209789 549388185504815806491985 := by
  unfold tailWord_3209789
  simp only [CollatzResearch.WordTrace]
  refine ⟨117070622568490116162808421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78047081712326744108538947 117070622568490116162808421)
  ·
    refine ⟨21950741731591896780526579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117070622568490116162808421 21950741731591896780526579)
    ·
      refine ⟨32926112597387845170789869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21950741731591896780526579 32926112597387845170789869)
      ·
        refine ⟨12347292224020441939046201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32926112597387845170789869 12347292224020441939046201)
        ·
          refine ⟨9260469168015331454284651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12347292224020441939046201 9260469168015331454284651)
          ·
            refine ⟨13890703752022997181426977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9260469168015331454284651 13890703752022997181426977)
            ·
              refine ⟨10418027814017247886070233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13890703752022997181426977 10418027814017247886070233)
              ·
                refine ⟨7813520860512935914552675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10418027814017247886070233 7813520860512935914552675)
                ·
                  refine ⟨11720281290769403871829013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7813520860512935914552675 11720281290769403871829013)
                  ·
                    refine ⟨549388185504815806491985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11720281290769403871829013 549388185504815806491985)
                    ·
                      rfl

theorem cell23_3209789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_3209789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209789 prefixEnd_3209789 := by exact prefixLift 3209789
  have htrace : WordTrace (prefixWord ++ tailWord_3209789) baseStart_3209789 baseEnd_3209789 := by
    simpa [prefixWord, tailWord_3209789, baseEnd_3209789] using wordTrace_append hprefix tailTrace_3209789
  have hstable : (prefixWord ++ tailWord_3209789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209789).length < 2 ^ (prefixWord ++ tailWord_3209789).sum := by decide
  have hdescent : baseEnd_3209789 < baseStart_3209789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209793 : List Nat := [1, 2, 5, 1, 1, 4, 2, 1, 1, 5]
def baseStart_3209793 : Nat := 118140960795 + 3209793 * 2 ^ 59
def prefixEnd_3209793 : Nat := 4983230072969 + 3 ^ 40 * 3209793 * 2
def baseEnd_3209793 : Nat := 549388870145688467941979

theorem tailTrace_3209793 : CollatzResearch.WordTrace tailWord_3209793 prefixEnd_3209793 549388870145688467941979 := by
  unfold tailWord_3209793
  simp only [CollatzResearch.WordTrace]
  refine ⟨117070768460475624845954033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78047178973650416563969355 117070768460475624845954033)
  ·
    refine ⟨87803076345356718634465525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117070768460475624845954033 87803076345356718634465525)
    ·
      refine ⟨8231538407377192371981143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 87803076345356718634465525 8231538407377192371981143)
      ·
        refine ⟨12347307611065788557971715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8231538407377192371981143 12347307611065788557971715)
        ·
          refine ⟨18520961416598682836957573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12347307611065788557971715 18520961416598682836957573)
          ·
            refine ⟨3472680265612253031929545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18520961416598682836957573 3472680265612253031929545)
            ·
              refine ⟨2604510199209189773947159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3472680265612253031929545 2604510199209189773947159)
              ·
                refine ⟨3906765298813784660920739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2604510199209189773947159 3906765298813784660920739)
                ·
                  refine ⟨5860147948220676991381109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3906765298813784660920739 5860147948220676991381109)
                  ·
                    refine ⟨549388870145688467941979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5860147948220676991381109 549388870145688467941979)
                    ·
                      rfl

theorem cell23_3209793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_3209793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209793 prefixEnd_3209793 := by exact prefixLift 3209793
  have htrace : WordTrace (prefixWord ++ tailWord_3209793) baseStart_3209793 baseEnd_3209793 := by
    simpa [prefixWord, tailWord_3209793, baseEnd_3209793] using wordTrace_append hprefix tailTrace_3209793
  have hstable : (prefixWord ++ tailWord_3209793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209793).length < 2 ^ (prefixWord ++ tailWord_3209793).sum := by decide
  have hdescent : baseEnd_3209793 < baseStart_3209793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209802 : List Nat := [3, 1, 2, 1, 1, 5, 10]
def baseStart_3209802 : Nat := 118140960795 + 3209802 * 2 ^ 59
def prefixEnd_3209802 : Nat := 4983230072969 + 3 ^ 40 * 3209802 * 2
def baseEnd_3209802 : Nat := 20347792984727850229795

theorem tailTrace_3209802 : CollatzResearch.WordTrace tailWord_3209802 prefixEnd_3209802 20347792984727850229795 := by
  unfold tailWord_3209802
  simp only [CollatzResearch.WordTrace]
  refine ⟨29267774179360754845757915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78047397811628679588687773 29267774179360754845757915)
  ·
    refine ⟨43901661269041132268636873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29267774179360754845757915 43901661269041132268636873)
    ·
      refine ⟨32926245951780849201477655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43901661269041132268636873 32926245951780849201477655)
      ·
        refine ⟨49389368927671273802216483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32926245951780849201477655 49389368927671273802216483)
        ·
          refine ⟨74084053391506910703324725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49389368927671273802216483 74084053391506910703324725)
          ·
            refine ⟨6945380005453772878436693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 74084053391506910703324725 6945380005453772878436693)
            ·
              refine ⟨20347792984727850229795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6945380005453772878436693 20347792984727850229795)
              ·
                rfl

theorem cell23_3209802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 10].length) (baseStart_3209802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209802 prefixEnd_3209802 := by exact prefixLift 3209802
  have htrace : WordTrace (prefixWord ++ tailWord_3209802) baseStart_3209802 baseEnd_3209802 := by
    simpa [prefixWord, tailWord_3209802, baseEnd_3209802] using wordTrace_append hprefix tailTrace_3209802
  have hstable : (prefixWord ++ tailWord_3209802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209802).length < 2 ^ (prefixWord ++ tailWord_3209802).sum := by decide
  have hdescent : baseEnd_3209802 < baseStart_3209802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209806 : List Nat := [4, 1, 1, 1, 1, 2, 5, 2, 2, 4]
def baseStart_3209806 : Nat := 118140960795 + 3209806 * 2 ^ 59
def prefixEnd_3209806 : Nat := 4983230072969 + 3 ^ 40 * 3209806 * 2
def baseEnd_3209806 : Nat := 549391095228524617654459

theorem tailTrace_3209806 : CollatzResearch.WordTrace tailWord_3209806 prefixEnd_3209806 549391095228524617654459 := by
  unfold tailWord_3209806
  simp only [CollatzResearch.WordTrace]
  refine ⟨14633905326178566008272159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78047495072952352044118181 14633905326178566008272159)
  ·
    refine ⟨21950857989267849012408239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14633905326178566008272159 21950857989267849012408239)
    ·
      refine ⟨32926286983901773518612359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21950857989267849012408239 32926286983901773518612359)
      ·
        refine ⟨49389430475852660277918539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32926286983901773518612359 49389430475852660277918539)
        ·
          refine ⟨74084145713778990416877809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49389430475852660277918539 74084145713778990416877809)
          ·
            refine ⟨55563109285334242812658357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74084145713778990416877809 55563109285334242812658357)
            ·
              refine ⟨5209041495500085263686721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 55563109285334242812658357 5209041495500085263686721)
              ·
                refine ⟨3906781121625063947765041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5209041495500085263686721 3906781121625063947765041)
                ·
                  refine ⟨2930085841218797960823781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3906781121625063947765041 2930085841218797960823781)
                  ·
                    refine ⟨549391095228524617654459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2930085841218797960823781 549391095228524617654459)
                    ·
                      rfl

theorem cell23_3209806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2, 2, 4].length) (baseStart_3209806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209806 prefixEnd_3209806 := by exact prefixLift 3209806
  have htrace : WordTrace (prefixWord ++ tailWord_3209806) baseStart_3209806 baseEnd_3209806 := by
    simpa [prefixWord, tailWord_3209806, baseEnd_3209806] using wordTrace_append hprefix tailTrace_3209806
  have hstable : (prefixWord ++ tailWord_3209806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209806).length < 2 ^ (prefixWord ++ tailWord_3209806).sum := by decide
  have hdescent : baseEnd_3209806 < baseStart_3209806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209920 : List Nat := [2, 1, 1, 2, 4, 3, 2, 2, 2, 2, 2]
def baseStart_3209920 : Nat := 118140960795 + 3209920 * 2 ^ 59
def prefixEnd_3209920 : Nat := 4983230072969 + 3 ^ 40 * 3209920 * 2
def baseEnd_3209920 : Nat := 1648231822480186406937853

theorem tailTrace_3209920 : CollatzResearch.WordTrace tailWord_3209920 prefixEnd_3209920 1648231822480186406937853 := by
  unfold tailWord_3209920
  simp only [CollatzResearch.WordTrace]
  refine ⟨58537700265507762767913607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78050267020677017023884809 58537700265507762767913607)
  ·
    refine ⟨87806550398261644151870411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58537700265507762767913607 87806550398261644151870411)
    ·
      refine ⟨131709825597392466227805617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87806550398261644151870411 131709825597392466227805617)
      ·
        refine ⟨98782369198044349670854213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131709825597392466227805617 98782369198044349670854213)
        ·
          refine ⟨18521694224633315563285165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98782369198044349670854213 18521694224633315563285165)
          ·
            refine ⟨6945635334237493336231937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18521694224633315563285165 6945635334237493336231937)
            ·
              refine ⟨5209226500678120002173953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6945635334237493336231937 5209226500678120002173953)
              ·
                refine ⟨3906919875508590001630465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5209226500678120002173953 3906919875508590001630465)
                ·
                  refine ⟨2930189906631442501222849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3906919875508590001630465 2930189906631442501222849)
                  ·
                    refine ⟨2197642429973581875917137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2930189906631442501222849 2197642429973581875917137)
                    ·
                      refine ⟨1648231822480186406937853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2197642429973581875917137 1648231822480186406937853)
                      ·
                        rfl

theorem cell23_3209920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 2, 2, 2, 2].length) (baseStart_3209920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209920 prefixEnd_3209920 := by exact prefixLift 3209920
  have htrace : WordTrace (prefixWord ++ tailWord_3209920) baseStart_3209920 baseEnd_3209920 := by
    simpa [prefixWord, tailWord_3209920, baseEnd_3209920] using wordTrace_append hprefix tailTrace_3209920
  have hstable : (prefixWord ++ tailWord_3209920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209920).length < 2 ^ (prefixWord ++ tailWord_3209920).sum := by decide
  have hdescent : baseEnd_3209920 < baseStart_3209920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209946 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2]
def baseStart_3209946 : Nat := 118140960795 + 3209946 * 2 ^ 59
def prefixEnd_3209946 : Nat := 4983230072969 + 3 ^ 40 * 3209946 * 2
def baseEnd_3209946 : Nat := 1648245172977203305212733

theorem tailTrace_3209946 : CollatzResearch.WordTrace tailWord_3209946 prefixEnd_3209946 1648245172977203305212733 := by
  unfold tailWord_3209946
  simp only [CollatzResearch.WordTrace]
  refine ⟨29269087207230332994068423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78050899219280887984182461 29269087207230332994068423)
  ·
    refine ⟨43903630810845499491102635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29269087207230332994068423 43903630810845499491102635)
    ·
      refine ⟨65855446216268249236653953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43903630810845499491102635 65855446216268249236653953)
      ·
        refine ⟨49391584662201186927490465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65855446216268249236653953 49391584662201186927490465)
        ·
          refine ⟨37043688496650890195617849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49391584662201186927490465 37043688496650890195617849)
          ·
            refine ⟨27782766372488167646713387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37043688496650890195617849 27782766372488167646713387)
            ·
              refine ⟨41674149558732251470070081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27782766372488167646713387 41674149558732251470070081)
              ·
                refine ⟨31255612169049188602552561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41674149558732251470070081 31255612169049188602552561)
                ·
                  refine ⟨23441709126786891451914421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31255612169049188602552561 23441709126786891451914421)
                  ·
                    refine ⟨2197660230636271073616977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 23441709126786891451914421 2197660230636271073616977)
                    ·
                      refine ⟨1648245172977203305212733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2197660230636271073616977 1648245172977203305212733)
                      ·
                        rfl

theorem cell23_3209946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_3209946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209946 prefixEnd_3209946 := by exact prefixLift 3209946
  have htrace : WordTrace (prefixWord ++ tailWord_3209946) baseStart_3209946 baseEnd_3209946 := by
    simpa [prefixWord, tailWord_3209946, baseEnd_3209946] using wordTrace_append hprefix tailTrace_3209946
  have hstable : (prefixWord ++ tailWord_3209946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209946).length < 2 ^ (prefixWord ++ tailWord_3209946).sum := by decide
  have hdescent : baseEnd_3209946 < baseStart_3209946 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209956 : List Nat := [2, 3, 1, 1, 1, 4, 3, 1, 2, 5]
def baseStart_3209956 : Nat := 118140960795 + 3209956 * 2 ^ 59
def prefixEnd_3209956 : Nat := 4983230072969 + 3 ^ 40 * 3209956 * 2
def baseEnd_3209956 : Nat := 549416769261249422029229

theorem tailTrace_3209956 : CollatzResearch.WordTrace tailWord_3209956 prefixEnd_3209956 549416769261249422029229 := by
  unfold tailWord_3209956
  simp only [CollatzResearch.WordTrace]
  refine ⟨58538356779442551842068861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78051142372590069122758481 58538356779442551842068861)
  ·
    refine ⟨21951883792290956940775823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58538356779442551842068861 21951883792290956940775823)
    ·
      refine ⟨32927825688436435411163735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21951883792290956940775823 32927825688436435411163735)
      ·
        refine ⟨49391738532654653116745603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32927825688436435411163735 49391738532654653116745603)
        ·
          refine ⟨74087607798981979675118405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49391738532654653116745603 74087607798981979675118405)
          ·
            refine ⟨13891426462309121189084701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74087607798981979675118405 13891426462309121189084701)
            ·
              refine ⟨5209284923365920445906763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13891426462309121189084701 5209284923365920445906763)
              ·
                refine ⟨7813927385048880668860145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209284923365920445906763 7813927385048880668860145)
                ·
                  refine ⟨5860445538786660501645109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7813927385048880668860145 5860445538786660501645109)
                  ·
                    refine ⟨549416769261249422029229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5860445538786660501645109 549416769261249422029229)
                    ·
                      rfl

theorem cell23_3209956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_3209956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209956 prefixEnd_3209956 := by exact prefixLift 3209956
  have htrace : WordTrace (prefixWord ++ tailWord_3209956) baseStart_3209956 baseEnd_3209956 := by
    simpa [prefixWord, tailWord_3209956, baseEnd_3209956] using wordTrace_append hprefix tailTrace_3209956
  have hstable : (prefixWord ++ tailWord_3209956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209956).length < 2 ^ (prefixWord ++ tailWord_3209956).sum := by decide
  have hdescent : baseEnd_3209956 < baseStart_3209956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3209976 : List Nat := [2, 1, 2, 1, 1, 2, 3, 1, 4, 4, 2]
def baseStart_3209976 : Nat := 118140960795 + 3209976 * 2 ^ 59
def prefixEnd_3209976 : Nat := 4983230072969 + 3 ^ 40 * 3209976 * 2
def baseEnd_3209976 : Nat := 1648260577396838187837595

theorem tailTrace_3209976 : CollatzResearch.WordTrace tailWord_3209976 prefixEnd_3209976 1648260577396838187837595 := by
  unfold tailWord_3209976
  simp only [CollatzResearch.WordTrace]
  refine ⟨58538721509406323549932891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78051628679208431399910521 58538721509406323549932891)
  ·
    refine ⟨87808082264109485324899337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58538721509406323549932891 87808082264109485324899337)
    ·
      refine ⟨65856061698082113993674503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87808082264109485324899337 65856061698082113993674503)
      ·
        refine ⟨98784092547123170990511755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65856061698082113993674503 98784092547123170990511755)
        ·
          refine ⟨148176138820684756485767633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98784092547123170990511755 148176138820684756485767633)
          ·
            refine ⟨111132104115513567364325725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148176138820684756485767633 111132104115513567364325725)
            ·
              refine ⟨41674539043317587761622147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 111132104115513567364325725 41674539043317587761622147)
              ·
                refine ⟨62511808564976381642433221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41674539043317587761622147 62511808564976381642433221)
                ·
                  refine ⟨11720964105933071557956229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62511808564976381642433221 11720964105933071557956229)
                  ·
                    refine ⟨2197680769862450917116793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11720964105933071557956229 2197680769862450917116793)
                    ·
                      refine ⟨1648260577396838187837595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2197680769862450917116793 1648260577396838187837595)
                      ·
                        rfl

theorem cell23_3209976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 1, 4, 4, 2].length) (baseStart_3209976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3209976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3209976 prefixEnd_3209976 := by exact prefixLift 3209976
  have htrace : WordTrace (prefixWord ++ tailWord_3209976) baseStart_3209976 baseEnd_3209976 := by
    simpa [prefixWord, tailWord_3209976, baseEnd_3209976] using wordTrace_append hprefix tailTrace_3209976
  have hstable : (prefixWord ++ tailWord_3209976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3209976).length < 2 ^ (prefixWord ++ tailWord_3209976).sum := by decide
  have hdescent : baseEnd_3209976 < baseStart_3209976 := by decide
  rcases family_descends (prefixWord ++ tailWord_3209976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210030 : List Nat := [4, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_3210030 : Nat := 118140960795 + 3210030 * 2 ^ 59
def prefixEnd_3210030 : Nat := 4983230072969 + 3 ^ 40 * 3210030 * 2
def baseEnd_3210030 : Nat := 1648288305352180976562347

theorem tailTrace_3210030 : CollatzResearch.WordTrace tailWord_3210030 prefixEnd_3210030 1648288305352180976562347 := by
  unfold tailWord_3210030
  simp only [CollatzResearch.WordTrace]
  refine ⟨14634926570077126790291443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78052941707078009548221029 14634926570077126790291443)
  ·
    refine ⟨21952389855115690185437165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14634926570077126790291443 21952389855115690185437165)
    ·
      refine ⟨8232146195668383819538937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21952389855115690185437165 8232146195668383819538937)
      ·
        refine ⟨6174109646751287864654203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8232146195668383819538937 6174109646751287864654203)
        ·
          refine ⟨9261164470126931796981305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6174109646751287864654203 9261164470126931796981305)
          ·
            refine ⟨6945873352595198847735979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9261164470126931796981305 6945873352595198847735979)
            ·
              refine ⟨10418810028892798271603969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6945873352595198847735979 10418810028892798271603969)
              ·
                refine ⟨7814107521669598703702977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10418810028892798271603969 7814107521669598703702977)
                ·
                  refine ⟨5860580641252199027777233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7814107521669598703702977 5860580641252199027777233)
                  ·
                    refine ⟨4395435480939149270832925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5860580641252199027777233 4395435480939149270832925)
                    ·
                      refine ⟨1648288305352180976562347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4395435480939149270832925 1648288305352180976562347)
                      ·
                        rfl

theorem cell23_3210030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_3210030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210030 prefixEnd_3210030 := by exact prefixLift 3210030
  have htrace : WordTrace (prefixWord ++ tailWord_3210030) baseStart_3210030 baseEnd_3210030 := by
    simpa [prefixWord, tailWord_3210030, baseEnd_3210030] using wordTrace_append hprefix tailTrace_3210030
  have hstable : (prefixWord ++ tailWord_3210030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210030).length < 2 ^ (prefixWord ++ tailWord_3210030).sum := by decide
  have hdescent : baseEnd_3210030 < baseStart_3210030 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210037 : List Nat := [1, 3, 3, 1, 3, 2, 3, 2, 1, 4]
def baseStart_3210037 : Nat := 118140960795 + 3210037 * 2 ^ 59
def prefixEnd_3210037 : Nat := 4983230072969 + 3 ^ 40 * 3210037 * 2
def baseEnd_3210037 : Nat := 549430633238920816391605

theorem tailTrace_3210037 : CollatzResearch.WordTrace tailWord_3210037 prefixEnd_3210037 549430633238920816391605 := by
  unfold tailWord_3210037
  simp only [CollatzResearch.WordTrace]
  refine ⟨117079667871591654517836365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78053111914394436345224243 117079667871591654517836365)
  ·
    refine ⟨43904875451846870444188637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117079667871591654517836365 43904875451846870444188637)
    ·
      refine ⟨16464328294442576416570739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43904875451846870444188637 16464328294442576416570739)
      ·
        refine ⟨24696492441663864624856109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16464328294442576416570739 24696492441663864624856109)
        ·
          refine ⟨9261184665623949234321041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24696492441663864624856109 9261184665623949234321041)
          ·
            refine ⟨6945888499217961925740781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9261184665623949234321041 6945888499217961925740781)
            ·
              refine ⟨2604708187206735722152793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6945888499217961925740781 2604708187206735722152793)
              ·
                refine ⟨1953531140405051791614595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2604708187206735722152793 1953531140405051791614595)
                ·
                  refine ⟨2930296710607577687421893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953531140405051791614595 2930296710607577687421893)
                  ·
                    refine ⟨549430633238920816391605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2930296710607577687421893 549430633238920816391605)
                    ·
                      rfl

theorem cell23_3210037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 3, 2, 1, 4].length) (baseStart_3210037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210037 prefixEnd_3210037 := by exact prefixLift 3210037
  have htrace : WordTrace (prefixWord ++ tailWord_3210037) baseStart_3210037 baseEnd_3210037 := by
    simpa [prefixWord, tailWord_3210037, baseEnd_3210037] using wordTrace_append hprefix tailTrace_3210037
  have hstable : (prefixWord ++ tailWord_3210037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210037).length < 2 ^ (prefixWord ++ tailWord_3210037).sum := by decide
  have hdescent : baseEnd_3210037 < baseStart_3210037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210059 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 7, 6]
def baseStart_3210059 : Nat := 118140960795 + 3210059 * 2 ^ 59
def prefixEnd_3210059 : Nat := 4983230072969 + 3 ^ 40 * 3210059 * 2
def baseEnd_3210059 : Nat := 549434398763720454366571

theorem tailTrace_3210059 : CollatzResearch.WordTrace tailWord_3210059 prefixEnd_3210059 549434398763720454366571 := by
  unfold tailWord_3210059
  simp only [CollatzResearch.WordTrace]
  refine ⟨117080470277511952275137231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78053646851674634850091487 117080470277511952275137231)
  ·
    refine ⟨175620705416267928412705847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117080470277511952275137231 175620705416267928412705847)
    ·
      refine ⟨263431058124401892619058771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175620705416267928412705847 263431058124401892619058771)
      ·
        refine ⟨395146587186602838928588157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263431058124401892619058771 395146587186602838928588157)
        ·
          refine ⟨148179970194976064598220559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 395146587186602838928588157 148179970194976064598220559)
          ·
            refine ⟨222269955292464096897330839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148179970194976064598220559 222269955292464096897330839)
            ·
              refine ⟨333404932938696145345996259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 222269955292464096897330839 333404932938696145345996259)
              ·
                refine ⟨500107399408044218018994389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 333404932938696145345996259 500107399408044218018994389)
                ·
                  refine ⟨11721267173626036359820181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 500107399408044218018994389 11721267173626036359820181)
                  ·
                    refine ⟨549434398763720454366571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11721267173626036359820181 549434398763720454366571)
                    ·
                      rfl

theorem cell23_3210059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 6].length) (baseStart_3210059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210059 prefixEnd_3210059 := by exact prefixLift 3210059
  have htrace : WordTrace (prefixWord ++ tailWord_3210059) baseStart_3210059 baseEnd_3210059 := by
    simpa [prefixWord, tailWord_3210059, baseEnd_3210059] using wordTrace_append hprefix tailTrace_3210059
  have hstable : (prefixWord ++ tailWord_3210059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210059).length < 2 ^ (prefixWord ++ tailWord_3210059).sum := by decide
  have hdescent : baseEnd_3210059 < baseStart_3210059 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210094 : List Nat := [4, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3]
def baseStart_3210094 : Nat := 118140960795 + 3210094 * 2 ^ 59
def prefixEnd_3210094 : Nat := 4983230072969 + 3 ^ 40 * 3210094 * 2
def baseEnd_3210094 : Nat := 1648321168114068726162053

theorem tailTrace_3210094 : CollatzResearch.WordTrace tailWord_3210094 prefixEnd_3210094 1648321168114068726162053 := by
  unfold tailWord_3210094
  simp only [CollatzResearch.WordTrace]
  refine ⟨14635218354048144156582667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78054497888256768835107557 14635218354048144156582667)
  ·
    refine ⟨21952827531072216234874001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14635218354048144156582667 21952827531072216234874001)
    ·
      refine ⟨16464620648304162176155501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21952827531072216234874001 16464620648304162176155501)
      ·
        refine ⟨6174232743114060816058313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16464620648304162176155501 6174232743114060816058313)
        ·
          refine ⟨4630674557335545612043735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6174232743114060816058313 4630674557335545612043735)
          ·
            refine ⟨6946011836003318418065603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4630674557335545612043735 6946011836003318418065603)
            ·
              refine ⟨10419017754004977627098405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946011836003318418065603 10419017754004977627098405)
              ·
                refine ⟨1953565828875933305080951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10419017754004977627098405 1953565828875933305080951)
                ·
                  refine ⟨2930348743313899957621427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953565828875933305080951 2930348743313899957621427)
                  ·
                    refine ⟨4395523114970849936432141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2930348743313899957621427 4395523114970849936432141)
                    ·
                      refine ⟨1648321168114068726162053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4395523114970849936432141 1648321168114068726162053)
                      ·
                        rfl

theorem cell23_3210094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_3210094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210094 prefixEnd_3210094 := by exact prefixLift 3210094
  have htrace : WordTrace (prefixWord ++ tailWord_3210094) baseStart_3210094 baseEnd_3210094 := by
    simpa [prefixWord, tailWord_3210094, baseEnd_3210094] using wordTrace_append hprefix tailTrace_3210094
  have hstable : (prefixWord ++ tailWord_3210094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210094).length < 2 ^ (prefixWord ++ tailWord_3210094).sum := by decide
  have hdescent : baseEnd_3210094 < baseStart_3210094 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210133 : List Nat := [1, 3, 2, 1, 1, 4, 2, 2, 1, 3, 3]
def baseStart_3210133 : Nat := 118140960795 + 3210133 * 2 ^ 59
def prefixEnd_3210133 : Nat := 4983230072969 + 3 ^ 40 * 3210133 * 2
def baseEnd_3210133 : Nat := 1648341193859594073574373

theorem tailTrace_3210133 : CollatzResearch.WordTrace tailWord_3210133 prefixEnd_3210133 1648341193859594073574373 := by
  unfold tailWord_3210133
  simp only [CollatzResearch.WordTrace]
  refine ⟨117083169279243862913331053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78055446186162575275554035 117083169279243862913331053)
  ·
    refine ⟨43906188479716448592499145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117083169279243862913331053 43906188479716448592499145)
    ·
      refine ⟨32929641359787336444374359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43906188479716448592499145 32929641359787336444374359)
      ·
        refine ⟨49394462039681004666561539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32929641359787336444374359 49394462039681004666561539)
        ·
          refine ⟨74091693059521506999842309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49394462039681004666561539 74091693059521506999842309)
          ·
            refine ⟨13892192448660282562470433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74091693059521506999842309 13892192448660282562470433)
            ·
              refine ⟨10419144336495211921852825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13892192448660282562470433 10419144336495211921852825)
              ·
                refine ⟨7814358252371408941389619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10419144336495211921852825 7814358252371408941389619)
                ·
                  refine ⟨11721537378557113412084429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7814358252371408941389619 11721537378557113412084429)
                  ·
                    refine ⟨4395576516958917529531661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11721537378557113412084429 4395576516958917529531661)
                    ·
                      refine ⟨1648341193859594073574373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4395576516958917529531661 1648341193859594073574373)
                      ·
                        rfl

theorem cell23_3210133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_3210133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210133 prefixEnd_3210133 := by exact prefixLift 3210133
  have htrace : WordTrace (prefixWord ++ tailWord_3210133) baseStart_3210133 baseEnd_3210133 := by
    simpa [prefixWord, tailWord_3210133, baseEnd_3210133] using wordTrace_append hprefix tailTrace_3210133
  have hstable : (prefixWord ++ tailWord_3210133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210133).length < 2 ^ (prefixWord ++ tailWord_3210133).sum := by decide
  have hdescent : baseEnd_3210133 < baseStart_3210133 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210134 : List Nat := [5, 3, 1, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_3210134 : Nat := 118140960795 + 3210134 * 2 ^ 59
def prefixEnd_3210134 : Nat := 4983230072969 + 3 ^ 40 * 3210134 * 2
def baseEnd_3210134 : Nat := 1648341707340248569661869

theorem tailTrace_3210134 : CollatzResearch.WordTrace tailWord_3210134 prefixEnd_3210134 1648341707340248569661869 := by
  unfold tailWord_3210134
  simp only [CollatzResearch.WordTrace]
  refine ⟨7317700359515015005257341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78055470501493493389411637 7317700359515015005257341)
  ·
    refine ⟨2744137634818130626971503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7317700359515015005257341 2744137634818130626971503)
    ·
      refine ⟨4116206452227195940457255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744137634818130626971503 4116206452227195940457255)
      ·
        refine ⟨6174309678340793910685883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4116206452227195940457255 6174309678340793910685883)
        ·
          refine ⟨9261464517511190866028825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6174309678340793910685883 9261464517511190866028825)
          ·
            refine ⟨6946098388133393149521619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9261464517511190866028825 6946098388133393149521619)
            ·
              refine ⟨10419147582200089724282429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946098388133393149521619 10419147582200089724282429)
              ·
                refine ⟨3907180343325033646605911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10419147582200089724282429 3907180343325033646605911)
                ·
                  refine ⟨5860770514987550469908867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3907180343325033646605911 5860770514987550469908867)
                  ·
                    refine ⟨8791155772481325704863301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5860770514987550469908867 8791155772481325704863301)
                    ·
                      refine ⟨1648341707340248569661869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8791155772481325704863301 1648341707340248569661869)
                      ·
                        rfl

theorem cell23_3210134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_3210134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210134 prefixEnd_3210134 := by exact prefixLift 3210134
  have htrace : WordTrace (prefixWord ++ tailWord_3210134) baseStart_3210134 baseEnd_3210134 := by
    simpa [prefixWord, tailWord_3210134, baseEnd_3210134] using wordTrace_append hprefix tailTrace_3210134
  have hstable : (prefixWord ++ tailWord_3210134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210134).length < 2 ^ (prefixWord ++ tailWord_3210134).sum := by decide
  have hdescent : baseEnd_3210134 < baseStart_3210134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210228 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 3, 3, 2]
def baseStart_3210228 : Nat := 118140960795 + 3210228 * 2 ^ 59
def prefixEnd_3210228 : Nat := 4983230072969 + 3 ^ 40 * 3210228 * 2
def baseEnd_3210228 : Nat := 1648389974521771201886437

theorem tailTrace_3210228 : CollatzResearch.WordTrace tailWord_3210228 prefixEnd_3210228 1648389974521771201886437 := by
  unfold tailWord_3210228
  simp only [CollatzResearch.WordTrace]
  refine ⟨58543317106949847069019669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78057756142599796092026225 58543317106949847069019669)
  ·
    refine ⟨2744217989388274081360297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 58543317106949847069019669 2744217989388274081360297)
    ·
      refine ⟨2058163492041205561020223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2744217989388274081360297 2058163492041205561020223)
      ·
        refine ⟨3087245238061808341530335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2058163492041205561020223 3087245238061808341530335)
        ·
          refine ⟨4630867857092712512295503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3087245238061808341530335 4630867857092712512295503)
          ·
            refine ⟨6946301785639068768443255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4630867857092712512295503 6946301785639068768443255)
            ·
              refine ⟨10419452678458603152664883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946301785639068768443255 10419452678458603152664883)
              ·
                refine ⟨15629179017687904728997325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10419452678458603152664883 15629179017687904728997325)
                ·
                  refine ⟨5860942131632964273373997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15629179017687904728997325 5860942131632964273373997)
                  ·
                    refine ⟨2197853299362361602515249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5860942131632964273373997 2197853299362361602515249)
                    ·
                      refine ⟨1648389974521771201886437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2197853299362361602515249 1648389974521771201886437)
                      ·
                        rfl

theorem cell23_3210228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 3, 3, 2].length) (baseStart_3210228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210228 prefixEnd_3210228 := by exact prefixLift 3210228
  have htrace : WordTrace (prefixWord ++ tailWord_3210228) baseStart_3210228 baseEnd_3210228 := by
    simpa [prefixWord, tailWord_3210228, baseEnd_3210228] using wordTrace_append hprefix tailTrace_3210228
  have hstable : (prefixWord ++ tailWord_3210228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210228).length < 2 ^ (prefixWord ++ tailWord_3210228).sum := by decide
  have hdescent : baseEnd_3210228 < baseStart_3210228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210283 : List Nat := [1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 3]
def baseStart_3210283 : Nat := 118140960795 + 3210283 * 2 ^ 59
def prefixEnd_3210283 : Nat := 4983230072969 + 3 ^ 40 * 3210283 * 2
def baseEnd_3210283 : Nat := 1648418215957768486698683

theorem tailTrace_3210283 : CollatzResearch.WordTrace tailWord_3210283 prefixEnd_3210283 1648418215957768486698683 := by
  unfold tailWord_3210283
  simp only [CollatzResearch.WordTrace]
  refine ⟨117088640228700438531291503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78059093485800292354194335 117088640228700438531291503)
  ·
    refine ⟨175632960343050657796937255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117088640228700438531291503 175632960343050657796937255)
    ·
      refine ⟨263449440514575986695405883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175632960343050657796937255 263449440514575986695405883)
      ·
        refine ⟨395174160771863980043108825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263449440514575986695405883 395174160771863980043108825)
        ·
          refine ⟨296380620578897985032331619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 395174160771863980043108825 296380620578897985032331619)
          ·
            refine ⟨444570930868346977548497429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296380620578897985032331619 444570930868346977548497429)
            ·
              refine ⟨20839262384453764572585817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 444570930868346977548497429 20839262384453764572585817)
              ·
                refine ⟨15629446788340323429439363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20839262384453764572585817 15629446788340323429439363)
                ·
                  refine ⟨23444170182510485144159045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15629446788340323429439363 23444170182510485144159045)
                  ·
                    refine ⟨4395781909220715964529821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23444170182510485144159045 4395781909220715964529821)
                    ·
                      refine ⟨1648418215957768486698683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4395781909220715964529821 1648418215957768486698683)
                      ·
                        rfl

theorem cell23_3210283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 3].length) (baseStart_3210283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210283 prefixEnd_3210283 := by exact prefixLift 3210283
  have htrace : WordTrace (prefixWord ++ tailWord_3210283) baseStart_3210283 baseEnd_3210283 := by
    simpa [prefixWord, tailWord_3210283, baseEnd_3210283] using wordTrace_append hprefix tailTrace_3210283
  have hstable : (prefixWord ++ tailWord_3210283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210283).length < 2 ^ (prefixWord ++ tailWord_3210283).sum := by decide
  have hdescent : baseEnd_3210283 < baseStart_3210283 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210290 : List Nat := [3, 2, 1, 1, 2, 2, 3, 2, 3, 4]
def baseStart_3210290 : Nat := 118140960795 + 3210290 * 2 ^ 59
def prefixEnd_3210290 : Nat := 4983230072969 + 3 ^ 40 * 3210290 * 2
def baseEnd_3210290 : Nat := 549473936774116653103717

theorem tailTrace_3210290 : CollatzResearch.WordTrace tailWord_3210290 prefixEnd_3210290 549473936774116653103717 := by
  unfold tailWord_3210290
  simp only [CollatzResearch.WordTrace]
  refine ⟨29272223884918769681699081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78059263693116719151197549 29272223884918769681699081)
  ·
    refine ⟨21954167913689077261274311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29272223884918769681699081 21954167913689077261274311)
    ·
      refine ⟨32931251870533615891911467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21954167913689077261274311 32931251870533615891911467)
      ·
        refine ⟨49396877805800423837867201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32931251870533615891911467 49396877805800423837867201)
        ·
          refine ⟨37047658354350317878400401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 49396877805800423837867201 37047658354350317878400401)
          ·
            refine ⟨27785743765762738408800301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37047658354350317878400401 27785743765762738408800301)
            ·
              refine ⟨10419653912161026903300113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27785743765762738408800301 10419653912161026903300113)
              ·
                refine ⟨7814740434120770177475085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10419653912161026903300113 7814740434120770177475085)
                ·
                  refine ⟨2930527662795288816553157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7814740434120770177475085 2930527662795288816553157)
                  ·
                    refine ⟨549473936774116653103717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2930527662795288816553157 549473936774116653103717)
                    ·
                      rfl

theorem cell23_3210290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_3210290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210290 prefixEnd_3210290 := by exact prefixLift 3210290
  have htrace : WordTrace (prefixWord ++ tailWord_3210290) baseStart_3210290 baseEnd_3210290 := by
    simpa [prefixWord, tailWord_3210290, baseEnd_3210290] using wordTrace_append hprefix tailTrace_3210290
  have hstable : (prefixWord ++ tailWord_3210290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210290).length < 2 ^ (prefixWord ++ tailWord_3210290).sum := by decide
  have hdescent : baseEnd_3210290 < baseStart_3210290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210297 : List Nat := [1, 2, 1, 5, 2, 3, 1, 1, 2, 1, 4]
def baseStart_3210297 : Nat := 118140960795 + 3210297 * 2 ^ 59
def prefixEnd_3210297 : Nat := 4983230072969 + 3 ^ 40 * 3210297 * 2
def baseEnd_3210297 : Nat := 1648425404686931431923619

theorem tailTrace_3210297 : CollatzResearch.WordTrace tailWord_3210297 prefixEnd_3210297 1648425404686931431923619 := by
  unfold tailWord_3210297
  simp only [CollatzResearch.WordTrace]
  refine ⟨117089150850649718922301145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78059433900433145948200763 117089150850649718922301145)
  ·
    refine ⟨87816863137987289191725859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117089150850649718922301145 87816863137987289191725859)
    ·
      refine ⟨131725294706980933787588789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87816863137987289191725859 131725294706980933787588789)
      ·
        refine ⟨12349246378779462542586449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 131725294706980933787588789 12349246378779462542586449)
        ·
          refine ⟨9261934784084596906939837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12349246378779462542586449 9261934784084596906939837)
          ·
            refine ⟨3473225544031723840102439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9261934784084596906939837 3473225544031723840102439)
            ·
              refine ⟨5209838316047585760153659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3473225544031723840102439 5209838316047585760153659)
              ·
                refine ⟨7814757474071378640230489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5209838316047585760153659 7814757474071378640230489)
                ·
                  refine ⟨5861068105553533980172867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7814757474071378640230489 5861068105553533980172867)
                  ·
                    refine ⟨8791602158330300970259301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5861068105553533980172867 8791602158330300970259301)
                    ·
                      refine ⟨1648425404686931431923619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8791602158330300970259301 1648425404686931431923619)
                      ·
                        rfl

theorem cell23_3210297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 1, 4].length) (baseStart_3210297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210297 prefixEnd_3210297 := by exact prefixLift 3210297
  have htrace : WordTrace (prefixWord ++ tailWord_3210297) baseStart_3210297 baseEnd_3210297 := by
    simpa [prefixWord, tailWord_3210297, baseEnd_3210297] using wordTrace_append hprefix tailTrace_3210297
  have hstable : (prefixWord ++ tailWord_3210297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210297).length < 2 ^ (prefixWord ++ tailWord_3210297).sum := by decide
  have hdescent : baseEnd_3210297 < baseStart_3210297 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210300 : List Nat := [2, 2, 2, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_3210300 : Nat := 118140960795 + 3210300 * 2 ^ 59
def prefixEnd_3210300 : Nat := 4983230072969 + 3 ^ 40 * 3210300 * 2
def baseEnd_3210300 : Nat := 1648426945128894920186105

theorem tailTrace_3210300 : CollatzResearch.WordTrace tailWord_3210300 prefixEnd_3210300 1648426945128894920186105 := by
  unfold tailWord_3210300
  simp only [CollatzResearch.WordTrace]
  refine ⟨58544630134819425217330177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78059506846425900289773569 58544630134819425217330177)
  ·
    refine ⟨43908472601114568912997633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58544630134819425217330177 43908472601114568912997633)
    ·
      refine ⟨32931354450835926684748225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43908472601114568912997633 32931354450835926684748225)
      ·
        refine ⟨24698515838126945013561169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32931354450835926684748225 24698515838126945013561169)
        ·
          refine ⟨18523886878595208760170877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24698515838126945013561169 18523886878595208760170877)
          ·
            refine ⟨6946457579473203285064079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18523886878595208760170877 6946457579473203285064079)
            ·
              refine ⟨10419686369209804927596119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946457579473203285064079 10419686369209804927596119)
              ·
                refine ⟨15629529553814707391394179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10419686369209804927596119 15629529553814707391394179)
                ·
                  refine ⟨23444294330722061087091269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15629529553814707391394179 23444294330722061087091269)
                  ·
                    refine ⟨4395805187010386453829613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23444294330722061087091269 4395805187010386453829613)
                    ·
                      refine ⟨1648426945128894920186105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4395805187010386453829613 1648426945128894920186105)
                      ·
                        rfl

theorem cell23_3210300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_3210300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210300 prefixEnd_3210300 := by exact prefixLift 3210300
  have htrace : WordTrace (prefixWord ++ tailWord_3210300) baseStart_3210300 baseEnd_3210300 := by
    simpa [prefixWord, tailWord_3210300, baseEnd_3210300] using wordTrace_append hprefix tailTrace_3210300
  have hstable : (prefixWord ++ tailWord_3210300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210300).length < 2 ^ (prefixWord ++ tailWord_3210300).sum := by decide
  have hdescent : baseEnd_3210300 < baseStart_3210300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210307 : List Nat := [1, 1, 1, 3, 1, 2, 6, 3, 1, 4]
def baseStart_3210307 : Nat := 118140960795 + 3210307 * 2 ^ 59
def prefixEnd_3210307 : Nat := 4983230072969 + 3 ^ 40 * 3210307 * 2
def baseEnd_3210307 : Nat := 549476846497825464266191

theorem tailTrace_3210307 : CollatzResearch.WordTrace tailWord_3210307 prefixEnd_3210307 549476846497825464266191 := by
  unfold tailWord_3210307
  simp only [CollatzResearch.WordTrace]
  refine ⟨117089515580613490630165175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78059677053742327086776783 117089515580613490630165175)
  ·
    refine ⟨175634273370920235945247763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117089515580613490630165175 175634273370920235945247763)
    ·
      refine ⟨263451410056380353917871645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175634273370920235945247763 263451410056380353917871645)
      ·
        refine ⟨98794278771142632719201867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263451410056380353917871645 98794278771142632719201867)
        ·
          refine ⟨148191418156713949078802801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98794278771142632719201867 148191418156713949078802801)
          ·
            refine ⟨111143563617535461809102101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148191418156713949078802801 111143563617535461809102101)
            ·
              refine ⟨5209854544571974772301661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111143563617535461809102101 5209854544571974772301661)
              ·
                refine ⟨1953695454214490539613123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5209854544571974772301661 1953695454214490539613123)
                ·
                  refine ⟨2930543181321735809419685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1953695454214490539613123 2930543181321735809419685)
                  ·
                    refine ⟨549476846497825464266191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2930543181321735809419685 549476846497825464266191)
                    ·
                      rfl

theorem cell23_3210307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 6, 3, 1, 4].length) (baseStart_3210307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210307 prefixEnd_3210307 := by exact prefixLift 3210307
  have htrace : WordTrace (prefixWord ++ tailWord_3210307) baseStart_3210307 baseEnd_3210307 := by
    simpa [prefixWord, tailWord_3210307, baseEnd_3210307] using wordTrace_append hprefix tailTrace_3210307
  have hstable : (prefixWord ++ tailWord_3210307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210307).length < 2 ^ (prefixWord ++ tailWord_3210307).sum := by decide
  have hdescent : baseEnd_3210307 < baseStart_3210307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210334 : List Nat := [4, 4, 1, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_3210334 : Nat := 118140960795 + 3210334 * 2 ^ 59
def prefixEnd_3210334 : Nat := 4983230072969 + 3 ^ 40 * 3210334 * 2
def baseEnd_3210334 : Nat := 1648444403471147787160949

theorem tailTrace_3210334 : CollatzResearch.WordTrace tailWord_3210334 prefixEnd_3210334 1648444403471147787160949 := by
  unfold tailWord_3210334
  simp only [CollatzResearch.WordTrace]
  refine ⟨14636312543939459280174757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78060333567677116160932037 14636312543939459280174757)
  ·
    refine ⟨2744308601988648615032767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14636312543939459280174757 2744308601988648615032767)
    ·
      refine ⟨4116462902982972922549151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2744308601988648615032767 4116462902982972922549151)
      ·
        refine ⟨6174694354474459383823727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4116462902982972922549151 6174694354474459383823727)
        ·
          refine ⟨9262041531711689075735591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6174694354474459383823727 9262041531711689075735591)
          ·
            refine ⟨13893062297567533613603387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9262041531711689075735591 13893062297567533613603387)
            ·
              refine ⟨20839593446351300420405081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13893062297567533613603387 20839593446351300420405081)
              ·
                refine ⟨15629695084763475315303811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20839593446351300420405081 15629695084763475315303811)
                ·
                  refine ⟨23444542627145212972955717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15629695084763475315303811 23444542627145212972955717)
                  ·
                    refine ⟨4395851742589727432429197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23444542627145212972955717 4395851742589727432429197)
                    ·
                      refine ⟨1648444403471147787160949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4395851742589727432429197 1648444403471147787160949)
                      ·
                        rfl

theorem cell23_3210334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_3210334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210334 prefixEnd_3210334 := by exact prefixLift 3210334
  have htrace : WordTrace (prefixWord ++ tailWord_3210334) baseStart_3210334 baseEnd_3210334 := by
    simpa [prefixWord, tailWord_3210334, baseEnd_3210334] using wordTrace_append hprefix tailTrace_3210334
  have hstable : (prefixWord ++ tailWord_3210334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210334).length < 2 ^ (prefixWord ++ tailWord_3210334).sum := by decide
  have hdescent : baseEnd_3210334 < baseStart_3210334 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210363 : List Nat := [1, 1, 1, 1, 1, 4, 1, 6, 1, 6]
def baseStart_3210363 : Nat := 118140960795 + 3210363 * 2 ^ 59
def prefixEnd_3210363 : Nat := 4983230072969 + 3 ^ 40 * 3210363 * 2
def baseEnd_3210363 : Nat := 549486431470042724566105

theorem tailTrace_3210363 : CollatzResearch.WordTrace tailWord_3210363 prefixEnd_3210363 549486431470042724566105 := by
  unfold tailWord_3210363
  simp only [CollatzResearch.WordTrace]
  refine ⟨117091558068410612194203743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78061038712273741462802495 117091558068410612194203743)
  ·
    refine ⟨175637337102615918291305615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117091558068410612194203743 175637337102615918291305615)
    ·
      refine ⟨263456005653923877436958423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175637337102615918291305615 263456005653923877436958423)
      ·
        refine ⟨395184008480885816155437635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263456005653923877436958423 395184008480885816155437635)
        ·
          refine ⟨592776012721328724233156453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395184008480885816155437635 592776012721328724233156453)
          ·
            refine ⟨111145502385249135793716835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 592776012721328724233156453 111145502385249135793716835)
            ·
              refine ⟨166718253577873703690575253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111145502385249135793716835 166718253577873703690575253)
              ·
                refine ⟨7814918136462829860495715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 166718253577873703690575253 7814918136462829860495715)
                ·
                  refine ⟨11722377204694244790743573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7814918136462829860495715 11722377204694244790743573)
                  ·
                    refine ⟨549486431470042724566105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11722377204694244790743573 549486431470042724566105)
                    ·
                      rfl

theorem cell23_3210363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 6, 1, 6].length) (baseStart_3210363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210363 prefixEnd_3210363 := by exact prefixLift 3210363
  have htrace : WordTrace (prefixWord ++ tailWord_3210363) baseStart_3210363 baseEnd_3210363 := by
    simpa [prefixWord, tailWord_3210363, baseEnd_3210363] using wordTrace_append hprefix tailTrace_3210363
  have hstable : (prefixWord ++ tailWord_3210363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210363).length < 2 ^ (prefixWord ++ tailWord_3210363).sum := by decide
  have hdescent : baseEnd_3210363 < baseStart_3210363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210397 : List Nat := [1, 4, 2, 1, 1, 2, 3, 3, 2, 4]
def baseStart_3210397 : Nat := 118140960795 + 3210397 * 2 ^ 59
def prefixEnd_3210397 : Nat := 4983230072969 + 3 ^ 40 * 3210397 * 2
def baseEnd_3210397 : Nat := 549492250917460346891053

theorem tailTrace_3210397 : CollatzResearch.WordTrace tailWord_3210397 prefixEnd_3210397 549492250917460346891053 := by
  unfold tailWord_3210397
  simp only [CollatzResearch.WordTrace]
  refine ⟨117092798150287436000941445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78061865433524957333960963 117092798150287436000941445)
  ·
    refine ⟨21954899653178894250176521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117092798150287436000941445 21954899653178894250176521)
    ·
      refine ⟨16466174739884170687632391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21954899653178894250176521 16466174739884170687632391)
      ·
        refine ⟨24699262109826256031448587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16466174739884170687632391 24699262109826256031448587)
        ·
          refine ⟨37048893164739384047172881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24699262109826256031448587 37048893164739384047172881)
          ·
            refine ⟨27786669873554538035379661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37048893164739384047172881 27786669873554538035379661)
            ·
              refine ⟨10420001202582951763267373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27786669873554538035379661 10420001202582951763267373)
              ·
                refine ⟨3907500450968606911225265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10420001202582951763267373 3907500450968606911225265)
                ·
                  refine ⟨2930625338226455183418949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3907500450968606911225265 2930625338226455183418949)
                  ·
                    refine ⟨549492250917460346891053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2930625338226455183418949 549492250917460346891053)
                    ·
                      rfl

theorem cell23_3210397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_3210397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210397 prefixEnd_3210397 := by exact prefixLift 3210397
  have htrace : WordTrace (prefixWord ++ tailWord_3210397) baseStart_3210397 baseEnd_3210397 := by
    simpa [prefixWord, tailWord_3210397, baseEnd_3210397] using wordTrace_append hprefix tailTrace_3210397
  have hstable : (prefixWord ++ tailWord_3210397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210397).length < 2 ^ (prefixWord ++ tailWord_3210397).sum := by decide
  have hdescent : baseEnd_3210397 < baseStart_3210397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210400 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 4]
def baseStart_3210400 : Nat := 118140960795 + 3210400 * 2 ^ 59
def prefixEnd_3210400 : Nat := 4983230072969 + 3 ^ 40 * 3210400 * 2
def baseEnd_3210400 : Nat := 1648478293194344528935645

theorem tailTrace_3210400 : CollatzResearch.WordTrace tailWord_3210400 prefixEnd_3210400 1648478293194344528935645 := by
  unfold tailWord_3210400
  simp only [CollatzResearch.WordTrace]
  refine ⟨58546453784638283756650327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78061938379517711675533769 58546453784638283756650327)
  ·
    refine ⟨87819680676957425634975491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58546453784638283756650327 87819680676957425634975491)
    ·
      refine ⟨131729521015436138452463237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87819680676957425634975491 131729521015436138452463237)
      ·
        refine ⟨24699285190394275959836857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131729521015436138452463237 24699285190394275959836857)
        ·
          refine ⟨18524463892795706969877643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24699285190394275959836857 18524463892795706969877643)
          ·
            refine ⟨27786695839193560454816465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18524463892795706969877643 27786695839193560454816465)
            ·
              refine ⟨20840021879395170341112349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27786695839193560454816465 20840021879395170341112349)
              ·
                refine ⟨7815008204773188877917131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20840021879395170341112349 7815008204773188877917131)
                ·
                  refine ⟨11722512307159783316875697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7815008204773188877917131 11722512307159783316875697)
                  ·
                    refine ⟨8791884230369837487656773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11722512307159783316875697 8791884230369837487656773)
                    ·
                      refine ⟨1648478293194344528935645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8791884230369837487656773 1648478293194344528935645)
                      ·
                        rfl

theorem cell23_3210400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 4].length) (baseStart_3210400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210400 prefixEnd_3210400 := by exact prefixLift 3210400
  have htrace : WordTrace (prefixWord ++ tailWord_3210400) baseStart_3210400 baseEnd_3210400 := by
    simpa [prefixWord, tailWord_3210400, baseEnd_3210400] using wordTrace_append hprefix tailTrace_3210400
  have hstable : (prefixWord ++ tailWord_3210400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210400).length < 2 ^ (prefixWord ++ tailWord_3210400).sum := by decide
  have hdescent : baseEnd_3210400 < baseStart_3210400 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210404 : List Nat := [2, 3, 1, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_3210404 : Nat := 118140960795 + 3210404 * 2 ^ 59
def prefixEnd_3210404 : Nat := 4983230072969 + 3 ^ 40 * 3210404 * 2
def baseEnd_3210404 : Nat := 1648480347116962513285627

theorem tailTrace_3210404 : CollatzResearch.WordTrace tailWord_3210404 prefixEnd_3210404 1648480347116962513285627 := by
  unfold tailWord_3210404
  simp only [CollatzResearch.WordTrace]
  refine ⟨58546526730631038098223133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78062035640841384130964177 58546526730631038098223133)
  ·
    refine ⟨21954947523986639286833675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58546526730631038098223133 21954947523986639286833675)
    ·
      refine ⟨32932421285979958930250513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21954947523986639286833675 32932421285979958930250513)
      ·
        refine ⟨24699315964484969197687885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32932421285979958930250513 24699315964484969197687885)
        ·
          refine ⟨9262243486681863449132957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24699315964484969197687885 9262243486681863449132957)
          ·
            refine ⟨3473341307505698793424859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9262243486681863449132957 3473341307505698793424859)
            ·
              refine ⟨5210011961258548190137289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3473341307505698793424859 5210011961258548190137289)
              ·
                refine ⟨3907508970943911142602967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5210011961258548190137289 3907508970943911142602967)
                ·
                  refine ⟨5861263456415866713904451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3907508970943911142602967 5861263456415866713904451)
                  ·
                    refine ⟨8791895184623800070856677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5861263456415866713904451 8791895184623800070856677)
                    ·
                      refine ⟨1648480347116962513285627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8791895184623800070856677 1648480347116962513285627)
                      ·
                        rfl

theorem cell23_3210404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_3210404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210404 prefixEnd_3210404 := by exact prefixLift 3210404
  have htrace : WordTrace (prefixWord ++ tailWord_3210404) baseStart_3210404 baseEnd_3210404 := by
    simpa [prefixWord, tailWord_3210404, baseEnd_3210404] using wordTrace_append hprefix tailTrace_3210404
  have hstable : (prefixWord ++ tailWord_3210404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210404).length < 2 ^ (prefixWord ++ tailWord_3210404).sum := by decide
  have hdescent : baseEnd_3210404 < baseStart_3210404 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210417 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 1, 2, 4]
def baseStart_3210417 : Nat := 118140960795 + 3210417 * 2 ^ 59
def prefixEnd_3210417 : Nat := 4983230072969 + 3 ^ 40 * 3210417 * 2
def baseEnd_3210417 : Nat := 1648487022365470962423067

theorem tailTrace_3210417 : CollatzResearch.WordTrace tailWord_3210417 prefixEnd_3210417 1648487022365470962423067 := by
  unfold tailWord_3210417
  simp only [CollatzResearch.WordTrace]
  refine ⟨117093527610214979416669505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78062351740143319611113003 117093527610214979416669505)
  ·
    refine ⟨87820145707661234562502129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117093527610214979416669505 87820145707661234562502129)
    ·
      refine ⟨65865109280745925921876597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87820145707661234562502129 65865109280745925921876597)
      ·
        refine ⟨6174853995069930555175931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65865109280745925921876597 6174853995069930555175931)
        ·
          refine ⟨9262280992604895832763897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6174853995069930555175931 9262280992604895832763897)
          ·
            refine ⟨6946710744453671874572923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9262280992604895832763897 6946710744453671874572923)
            ·
              refine ⟨10420066116680507811859385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946710744453671874572923 10420066116680507811859385)
              ·
                refine ⟨7815049587510380858894539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10420066116680507811859385 7815049587510380858894539)
                ·
                  refine ⟨11722574381265571288341809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7815049587510380858894539 11722574381265571288341809)
                  ·
                    refine ⟨8791930785949178466256357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11722574381265571288341809 8791930785949178466256357)
                    ·
                      refine ⟨1648487022365470962423067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8791930785949178466256357 1648487022365470962423067)
                      ·
                        rfl

theorem cell23_3210417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_3210417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210417 prefixEnd_3210417 := by exact prefixLift 3210417
  have htrace : WordTrace (prefixWord ++ tailWord_3210417) baseStart_3210417 baseEnd_3210417 := by
    simpa [prefixWord, tailWord_3210417, baseEnd_3210417] using wordTrace_append hprefix tailTrace_3210417
  have hstable : (prefixWord ++ tailWord_3210417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210417).length < 2 ^ (prefixWord ++ tailWord_3210417).sum := by decide
  have hdescent : baseEnd_3210417 < baseStart_3210417 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210490 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4]
def baseStart_3210490 : Nat := 118140960795 + 3210490 * 2 ^ 59
def prefixEnd_3210490 : Nat := 4983230072969 + 3 ^ 40 * 3210490 * 2
def baseEnd_3210490 : Nat := 1648524506453249176810231

theorem tailTrace_3210490 : CollatzResearch.WordTrace tailWord_3210490 prefixEnd_3210490 1648524506453249176810231 := by
  unfold tailWord_3210490
  simp only [CollatzResearch.WordTrace]
  refine ⟨29274047534737628221019231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78064126759300341922717949 29274047534737628221019231)
  ·
    refine ⟨43911071302106442331528847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29274047534737628221019231 43911071302106442331528847)
    ·
      refine ⟨65866606953159663497293271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43911071302106442331528847 65866606953159663497293271)
      ·
        refine ⟨98799910429739495245939907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65866606953159663497293271 98799910429739495245939907)
        ·
          refine ⟨148199865644609242868909861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98799910429739495245939907 148199865644609242868909861)
          ·
            refine ⟨27787474808364233037920599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148199865644609242868909861 27787474808364233037920599)
            ·
              refine ⟨41681212212546349556880899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27787474808364233037920599 41681212212546349556880899)
              ·
                refine ⟨62521818318819524335321349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 41681212212546349556880899 62521818318819524335321349)
                ·
                  refine ⟨11722840934778660812872753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62521818318819524335321349 11722840934778660812872753)
                  ·
                    refine ⟨8792130701083995609654565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11722840934778660812872753 8792130701083995609654565)
                    ·
                      refine ⟨1648524506453249176810231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8792130701083995609654565 1648524506453249176810231)
                      ·
                        rfl

theorem cell23_3210490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_3210490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210490 prefixEnd_3210490 := by exact prefixLift 3210490
  have htrace : WordTrace (prefixWord ++ tailWord_3210490) baseStart_3210490 baseEnd_3210490 := by
    simpa [prefixWord, tailWord_3210490, baseEnd_3210490] using wordTrace_append hprefix tailTrace_3210490
  have hstable : (prefixWord ++ tailWord_3210490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210490).length < 2 ^ (prefixWord ++ tailWord_3210490).sum := by decide
  have hdescent : baseEnd_3210490 < baseStart_3210490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210540 : List Nat := [2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_3210540 : Nat := 118140960795 + 3210540 * 2 ^ 59
def prefixEnd_3210540 : Nat := 4983230072969 + 3 ^ 40 * 3210540 * 2
def baseEnd_3210540 : Nat := 1648550180485973981185001

theorem tailTrace_3210540 : CollatzResearch.WordTrace tailWord_3210540 prefixEnd_3210540 1648550180485973981185001 := by
  unfold tailWord_3210540
  simp only [CollatzResearch.WordTrace]
  refine ⟨58549006894384685711698537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78065342525846247615598049 58549006894384685711698537)
  ·
    refine ⟨43911755170788514283773903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58549006894384685711698537 43911755170788514283773903)
    ·
      refine ⟨65867632756182771425660855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43911755170788514283773903 65867632756182771425660855)
      ·
        refine ⟨98801449134274157138491283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65867632756182771425660855 98801449134274157138491283)
        ·
          refine ⟨148202173701411235707736925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98801449134274157138491283 148202173701411235707736925)
          ·
            refine ⟨55575815138029213390401347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 148202173701411235707736925 55575815138029213390401347)
            ·
              refine ⟨83363722707043820085602021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55575815138029213390401347 83363722707043820085602021)
              ·
                refine ⟨15630698007570716266050379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 83363722707043820085602021 15630698007570716266050379)
                ·
                  refine ⟨23446047011356074399075569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15630698007570716266050379 23446047011356074399075569)
                  ·
                    refine ⟨17584535258517055799306677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23446047011356074399075569 17584535258517055799306677)
                    ·
                      refine ⟨1648550180485973981185001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17584535258517055799306677 1648550180485973981185001)
                      ·
                        rfl

theorem cell23_3210540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_3210540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210540 prefixEnd_3210540 := by exact prefixLift 3210540
  have htrace : WordTrace (prefixWord ++ tailWord_3210540) baseStart_3210540 baseEnd_3210540 := by
    simpa [prefixWord, tailWord_3210540, baseEnd_3210540] using wordTrace_append hprefix tailTrace_3210540
  have hstable : (prefixWord ++ tailWord_3210540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210540).length < 2 ^ (prefixWord ++ tailWord_3210540).sum := by decide
  have hdescent : baseEnd_3210540 < baseStart_3210540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210547 : List Nat := [1, 1, 1, 2, 5, 3, 1, 2, 2, 5]
def baseStart_3210547 : Nat := 118140960795 + 3210547 * 2 ^ 59
def prefixEnd_3210547 : Nat := 4983230072969 + 3 ^ 40 * 3210547 * 2
def baseEnd_3210547 : Nat := 549517924950185151265823

theorem tailTrace_3210547 : CollatzResearch.WordTrace tailWord_3210547 prefixEnd_3210547 549517924950185151265823 := by
  unfold tailWord_3210547
  simp only [CollatzResearch.WordTrace]
  refine ⟨117098269099744011618901895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78065512733162674412601263 117098269099744011618901895)
  ·
    refine ⟨175647403649616017428352843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117098269099744011618901895 175647403649616017428352843)
    ·
      refine ⟨263471105474424026142529265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175647403649616017428352843 263471105474424026142529265)
      ·
        refine ⟨197603329105818019606896949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 263471105474424026142529265 197603329105818019606896949)
        ·
          refine ⟨18525312103670439338146589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197603329105818019606896949 18525312103670439338146589)
          ·
            refine ⟨6946992038876414751804971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18525312103670439338146589 6946992038876414751804971)
            ·
              refine ⟨10420488058314622127707457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6946992038876414751804971 10420488058314622127707457)
              ·
                refine ⟨7815366043735966595780593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10420488058314622127707457 7815366043735966595780593)
                ·
                  refine ⟨5861524532801974946835445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7815366043735966595780593 5861524532801974946835445)
                  ·
                    refine ⟨549517924950185151265823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5861524532801974946835445 549517924950185151265823)
                    ·
                      rfl

theorem cell23_3210547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 5].length) (baseStart_3210547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210547 prefixEnd_3210547 := by exact prefixLift 3210547
  have htrace : WordTrace (prefixWord ++ tailWord_3210547) baseStart_3210547 baseEnd_3210547 := by
    simpa [prefixWord, tailWord_3210547, baseEnd_3210547] using wordTrace_append hprefix tailTrace_3210547
  have hstable : (prefixWord ++ tailWord_3210547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210547).length < 2 ^ (prefixWord ++ tailWord_3210547).sum := by decide
  have hdescent : baseEnd_3210547 < baseStart_3210547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210570 : List Nat := [3, 1, 2, 1, 1, 1, 1, 2, 1, 5, 5]
def baseStart_3210570 : Nat := 118140960795 + 3210570 * 2 ^ 59
def prefixEnd_3210570 : Nat := 4983230072969 + 3 ^ 40 * 3210570 * 2
def baseEnd_3210570 : Nat := 1648565584905608863809863

theorem tailTrace_3210570 : CollatzResearch.WordTrace tailWord_3210570 prefixEnd_3210570 1648565584905608863809863 := by
  unfold tailWord_3210570
  simp only [CollatzResearch.WordTrace]
  refine ⟨29274776994665171636747291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 78066071985773791031326109 29274776994665171636747291)
  ·
    refine ⟨43912165491997757455120937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29274776994665171636747291 43912165491997757455120937)
    ·
      refine ⟨32934124118998318091340703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43912165491997757455120937 32934124118998318091340703)
      ·
        refine ⟨49401186178497477137011055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32934124118998318091340703 49401186178497477137011055)
        ·
          refine ⟨74101779267746215705516583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 49401186178497477137011055 74101779267746215705516583)
          ·
            refine ⟨111152668901619323558274875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74101779267746215705516583 111152668901619323558274875)
            ·
              refine ⟨166729003352428985337412313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 111152668901619323558274875 166729003352428985337412313)
              ·
                refine ⟨125046752514321739003059235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 166729003352428985337412313 125046752514321739003059235)
                ·
                  refine ⟨187570128771482608504588853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 125046752514321739003059235 187570128771482608504588853)
                  ·
                    refine ⟨17584699572326494547305205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 187570128771482608504588853 17584699572326494547305205)
                    ·
                      refine ⟨1648565584905608863809863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17584699572326494547305205 1648565584905608863809863)
                      ·
                        rfl

theorem cell23_3210570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_3210570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210570 prefixEnd_3210570 := by exact prefixLift 3210570
  have htrace : WordTrace (prefixWord ++ tailWord_3210570) baseStart_3210570 baseEnd_3210570 := by
    simpa [prefixWord, tailWord_3210570, baseEnd_3210570] using wordTrace_append hprefix tailTrace_3210570
  have hstable : (prefixWord ++ tailWord_3210570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210570).length < 2 ^ (prefixWord ++ tailWord_3210570).sum := by decide
  have hdescent : baseEnd_3210570 < baseStart_3210570 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210577 : List Nat := [1, 2, 2, 1, 4, 1, 2, 1, 5, 4]
def baseStart_3210577 : Nat := 118140960795 + 3210577 * 2 ^ 59
def prefixEnd_3210577 : Nat := 4983230072969 + 3 ^ 40 * 3210577 * 2
def baseEnd_3210577 : Nat := 549523059756730112140777

theorem tailTrace_3210577 : CollatzResearch.WordTrace tailWord_3210577 prefixEnd_3210577 549523059756730112140777 := by
  unfold tailWord_3210577
  simp only [CollatzResearch.WordTrace]
  refine ⟨117099363289635326742493985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78066242193090217828329323 117099363289635326742493985)
  ·
    refine ⟨87824522467226495056870489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117099363289635326742493985 87824522467226495056870489)
    ·
      refine ⟨65868391850419871292652867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87824522467226495056870489 65868391850419871292652867)
      ·
        refine ⟨98802587775629806938979301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65868391850419871292652867 98802587775629806938979301)
        ·
          refine ⟨18525485207930588801058619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 98802587775629806938979301 18525485207930588801058619)
          ·
            refine ⟨27788227811895883201587929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18525485207930588801058619 27788227811895883201587929)
            ·
              refine ⟨20841170858921912401190947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27788227811895883201587929 20841170858921912401190947)
              ·
                refine ⟨31261756288382868601786421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20841170858921912401190947 31261756288382868601786421)
                ·
                  refine ⟨2930789652035893931417477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31261756288382868601786421 2930789652035893931417477)
                  ·
                    refine ⟨549523059756730112140777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2930789652035893931417477 549523059756730112140777)
                    ·
                      rfl

theorem cell23_3210577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 1, 5, 4].length) (baseStart_3210577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210577 prefixEnd_3210577 := by exact prefixLift 3210577
  have htrace : WordTrace (prefixWord ++ tailWord_3210577) baseStart_3210577 baseEnd_3210577 := by
    simpa [prefixWord, tailWord_3210577, baseEnd_3210577] using wordTrace_append hprefix tailTrace_3210577
  have hstable : (prefixWord ++ tailWord_3210577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210577).length < 2 ^ (prefixWord ++ tailWord_3210577).sum := by decide
  have hdescent : baseEnd_3210577 < baseStart_3210577 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210604 : List Nat := [2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 3]
def baseStart_3210604 : Nat := 118140960795 + 3210604 * 2 ^ 59
def prefixEnd_3210604 : Nat := 4983230072969 + 3 ^ 40 * 3210604 * 2
def baseEnd_3210604 : Nat := 1648583043247861730784707

theorem tailTrace_3210604 : CollatzResearch.WordTrace tailWord_3210604 prefixEnd_3210604 1648583043247861730784707 := by
  unfold tailWord_3210604
  simp only [CollatzResearch.WordTrace]
  refine ⟨58550174030268755176863433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78066898707025006902484577 58550174030268755176863433)
  ·
    refine ⟨43912630522701566382647575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58550174030268755176863433 43912630522701566382647575)
    ·
      refine ⟨65868945784052349573971363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43912630522701566382647575 65868945784052349573971363)
      ·
        refine ⟨98803418676078524360957045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65868945784052349573971363 98803418676078524360957045)
        ·
          refine ⟨9262820500882361658839723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 98803418676078524360957045 9262820500882361658839723)
          ·
            refine ⟨13894230751323542488259585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9262820500882361658839723 13894230751323542488259585)
            ·
              refine ⟨10420673063492656866194689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13894230751323542488259585 10420673063492656866194689)
              ·
                refine ⟨7815504797619492649646017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10420673063492656866194689 7815504797619492649646017)
                ·
                  refine ⟨5861628598214619487234513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7815504797619492649646017 5861628598214619487234513)
                  ·
                    refine ⟨4396221448660964615425885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5861628598214619487234513 4396221448660964615425885)
                    ·
                      refine ⟨1648583043247861730784707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4396221448660964615425885 1648583043247861730784707)
                      ·
                        rfl

theorem cell23_3210604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_3210604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210604 prefixEnd_3210604 := by exact prefixLift 3210604
  have htrace : WordTrace (prefixWord ++ tailWord_3210604) baseStart_3210604 baseEnd_3210604 := by
    simpa [prefixWord, tailWord_3210604, baseEnd_3210604] using wordTrace_append hprefix tailTrace_3210604
  have hstable : (prefixWord ++ tailWord_3210604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210604).length < 2 ^ (prefixWord ++ tailWord_3210604).sum := by decide
  have hdescent : baseEnd_3210604 < baseStart_3210604 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210607 : List Nat := [1, 1, 2, 1, 3, 1, 6, 2, 6]
def baseStart_3210607 : Nat := 118140960795 + 3210607 * 2 ^ 59
def prefixEnd_3210607 : Nat := 4983230072969 + 3 ^ 40 * 3210607 * 2
def baseEnd_3210607 : Nat := 183176064854425024338577

theorem tailTrace_3210607 : CollatzResearch.WordTrace tailWord_3210607 prefixEnd_3210607 183176064854425024338577 := by
  unfold tailWord_3210607
  simp only [CollatzResearch.WordTrace]
  refine ⟨117100457479526641866086075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78066971653017761244057383 117100457479526641866086075)
  ·
    refine ⟨175650686219289962799129113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117100457479526641866086075 175650686219289962799129113)
    ·
      refine ⟨131738014664467472099346835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175650686219289962799129113 131738014664467472099346835)
      ·
        refine ⟨197607021996701208149020253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131738014664467472099346835 197607021996701208149020253)
        ·
          refine ⟨74102633248762953055882595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 197607021996701208149020253 74102633248762953055882595)
          ·
            refine ⟨111153949873144429583823893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74102633248762953055882595 111153949873144429583823893)
            ·
              refine ⟨5210341400303645136741745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 111153949873144429583823893 5210341400303645136741745)
              ·
                refine ⟨3907756050227733852556309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5210341400303645136741745 3907756050227733852556309)
                ·
                  refine ⟨183176064854425024338577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3907756050227733852556309 183176064854425024338577)
                  ·
                    rfl

theorem cell23_3210607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 6, 2, 6].length) (baseStart_3210607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210607 prefixEnd_3210607 := by exact prefixLift 3210607
  have htrace : WordTrace (prefixWord ++ tailWord_3210607) baseStart_3210607 baseEnd_3210607 := by
    simpa [prefixWord, tailWord_3210607, baseEnd_3210607] using wordTrace_append hprefix tailTrace_3210607
  have hstable : (prefixWord ++ tailWord_3210607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210607).length < 2 ^ (prefixWord ++ tailWord_3210607).sum := by decide
  have hdescent : baseEnd_3210607 < baseStart_3210607 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210638 : List Nat := [4, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3]
def baseStart_3210638 : Nat := 118140960795 + 3210638 * 2 ^ 59
def prefixEnd_3210638 : Nat := 4983230072969 + 3 ^ 40 * 3210638 * 2
def baseEnd_3210638 : Nat := 1648600501590114597759551

theorem tailTrace_3210638 : CollatzResearch.WordTrace tailWord_3210638 prefixEnd_3210638 1648600501590114597759551 := by
  unfold tailWord_3210638
  simp only [CollatzResearch.WordTrace]
  refine ⟨14637698517801791770058071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78067725428276222773643045 14637698517801791770058071)
  ·
    refine ⟨21956547776702687655087107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14637698517801791770058071 21956547776702687655087107)
    ·
      refine ⟨32934821665054031482630661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21956547776702687655087107 32934821665054031482630661)
      ·
        refine ⟨6175279062197630902993249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32934821665054031482630661 6175279062197630902993249)
        ·
          refine ⟨4631459296648223177244937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6175279062197630902993249 4631459296648223177244937)
          ·
            refine ⟨3473594472486167382933703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4631459296648223177244937 3473594472486167382933703)
            ·
              refine ⟨5210391708729251074400555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3473594472486167382933703 5210391708729251074400555)
              ·
                refine ⟨7815587563093876611600833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5210391708729251074400555 7815587563093876611600833)
                ·
                  refine ⟨5861690672320407458700625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7815587563093876611600833 5861690672320407458700625)
                  ·
                    refine ⟨4396268004240305594025469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5861690672320407458700625 4396268004240305594025469)
                    ·
                      refine ⟨1648600501590114597759551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4396268004240305594025469 1648600501590114597759551)
                      ·
                        rfl

theorem cell23_3210638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_3210638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210638 prefixEnd_3210638 := by exact prefixLift 3210638
  have htrace : WordTrace (prefixWord ++ tailWord_3210638) baseStart_3210638 baseEnd_3210638 := by
    simpa [prefixWord, tailWord_3210638, baseEnd_3210638] using wordTrace_append hprefix tailTrace_3210638
  have hstable : (prefixWord ++ tailWord_3210638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210638).length < 2 ^ (prefixWord ++ tailWord_3210638).sum := by decide
  have hdescent : baseEnd_3210638 < baseStart_3210638 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210691 : List Nat := [1, 1, 1, 3, 1, 1, 6, 2, 3, 2, 2]
def baseStart_3210691 : Nat := 118140960795 + 3210691 * 2 ^ 59
def prefixEnd_3210691 : Nat := 4983230072969 + 3 ^ 40 * 3210691 * 2
def baseEnd_3210691 : Nat := 1648627716064802890396807

theorem tailTrace_3210691 : CollatzResearch.WordTrace tailWord_3210691 prefixEnd_3210691 1648627716064802890396807 := by
  unfold tailWord_3210691
  simp only [CollatzResearch.WordTrace]
  refine ⟨117103521211222324212143927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78069014140814882808095951 117103521211222324212143927)
  ·
    refine ⟨175655281816833486318215891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117103521211222324212143927 175655281816833486318215891)
    ·
      refine ⟨263482922725250229477323837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175655281816833486318215891 263482922725250229477323837)
      ·
        refine ⟨98806096021968836053996439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263482922725250229477323837 98806096021968836053996439)
        ·
          refine ⟨148209144032953254080994659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98806096021968836053996439 148209144032953254080994659)
          ·
            refine ⟨222313716049429881121491989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 148209144032953254080994659 222313716049429881121491989)
            ·
              refine ⟨10420955439817025677569937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 222313716049429881121491989 10420955439817025677569937)
              ·
                refine ⟨7815716579862769258177453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10420955439817025677569937 7815716579862769258177453)
                ·
                  refine ⟨2930893717448538471816545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7815716579862769258177453 2930893717448538471816545)
                  ·
                    refine ⟨2198170288086403853862409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2930893717448538471816545 2198170288086403853862409)
                    ·
                      refine ⟨1648627716064802890396807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2198170288086403853862409 1648627716064802890396807)
                      ·
                        rfl

theorem cell23_3210691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 2, 2].length) (baseStart_3210691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210691 prefixEnd_3210691 := by exact prefixLift 3210691
  have htrace : WordTrace (prefixWord ++ tailWord_3210691) baseStart_3210691 baseEnd_3210691 := by
    simpa [prefixWord, tailWord_3210691, baseEnd_3210691] using wordTrace_append hprefix tailTrace_3210691
  have hstable : (prefixWord ++ tailWord_3210691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210691).length < 2 ^ (prefixWord ++ tailWord_3210691).sum := by decide
  have hdescent : baseEnd_3210691 < baseStart_3210691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210725 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 3, 2, 2]
def baseStart_3210725 : Nat := 118140960795 + 3210725 * 2 ^ 59
def prefixEnd_3210725 : Nat := 4983230072969 + 3 ^ 40 * 3210725 * 2
def baseEnd_3210725 : Nat := 1648645174407055757371651

theorem tailTrace_3210725 : CollatzResearch.WordTrace tailWord_3210725 prefixEnd_3210725 1648645174407055757371651 := by
  unfold tailWord_3210725
  simp only [CollatzResearch.WordTrace]
  refine ⟨117104761293099148018881629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78069840862066098679254419 117104761293099148018881629)
  ·
    refine ⟨43914285484912180507080611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117104761293099148018881629 43914285484912180507080611)
    ·
      refine ⟨65871428227368270760620917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43914285484912180507080611 65871428227368270760620917)
      ·
        refine ⟨6175446396315775383808211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 65871428227368270760620917 6175446396315775383808211)
        ·
          refine ⟨9263169594473663075712317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6175446396315775383808211 9263169594473663075712317)
          ·
            refine ⟨3473688597927623653392119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9263169594473663075712317 3473688597927623653392119)
            ·
              refine ⟨5210532896891435480088179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3473688597927623653392119 5210532896891435480088179)
              ·
                refine ⟨7815799345337153220132269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5210532896891435480088179 7815799345337153220132269)
                ·
                  refine ⟨2930924754501432457549601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7815799345337153220132269 2930924754501432457549601)
                  ·
                    refine ⟨2198193565876074343162201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2930924754501432457549601 2198193565876074343162201)
                    ·
                      refine ⟨1648645174407055757371651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2198193565876074343162201 1648645174407055757371651)
                      ·
                        rfl

theorem cell23_3210725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_3210725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210725 prefixEnd_3210725 := by exact prefixLift 3210725
  have htrace : WordTrace (prefixWord ++ tailWord_3210725) baseStart_3210725 baseEnd_3210725 := by
    simpa [prefixWord, tailWord_3210725, baseEnd_3210725] using wordTrace_append hprefix tailTrace_3210725
  have hstable : (prefixWord ++ tailWord_3210725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210725).length < 2 ^ (prefixWord ++ tailWord_3210725).sum := by decide
  have hdescent : baseEnd_3210725 < baseStart_3210725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210747 : List Nat := [1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 4]
def baseStart_3210747 : Nat := 118140960795 + 3210747 * 2 ^ 59
def prefixEnd_3210747 : Nat := 4983230072969 + 3 ^ 40 * 3210747 * 2
def baseEnd_3210747 : Nat := 1648656470981454671296549

theorem tailTrace_3210747 : CollatzResearch.WordTrace tailWord_3210747 prefixEnd_3210747 1648656470981454671296549 := by
  unfold tailWord_3210747
  simp only [CollatzResearch.WordTrace]
  refine ⟨117105563699019445776182495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78070375799346297184121663 117105563699019445776182495)
  ·
    refine ⟨175658345548529168664273743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117105563699019445776182495 175658345548529168664273743)
    ·
      refine ⟨263487518322793752996410615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175658345548529168664273743 263487518322793752996410615)
      ·
        refine ⟨395231277484190629494615923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263487518322793752996410615 395231277484190629494615923)
        ·
          refine ⟨592846916226285944241923885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 395231277484190629494615923 592846916226285944241923885)
          ·
            refine ⟨222317593584857229090721457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 592846916226285944241923885 222317593584857229090721457)
            ·
              refine ⟨166738195188642921818041093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 222317593584857229090721457 166738195188642921818041093)
              ·
                refine ⟨31263411597870547840882705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 166738195188642921818041093 31263411597870547840882705)
                ·
                  refine ⟨23447558698402910880662029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31263411597870547840882705 23447558698402910880662029)
                  ·
                    refine ⟨8792834511901091580248261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23447558698402910880662029 8792834511901091580248261)
                    ·
                      refine ⟨1648656470981454671296549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8792834511901091580248261 1648656470981454671296549)
                      ·
                        rfl

theorem cell23_3210747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 3, 4].length) (baseStart_3210747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210747 prefixEnd_3210747 := by exact prefixLift 3210747
  have htrace : WordTrace (prefixWord ++ tailWord_3210747) baseStart_3210747 baseEnd_3210747 := by
    simpa [prefixWord, tailWord_3210747, baseEnd_3210747] using wordTrace_append hprefix tailTrace_3210747
  have hstable : (prefixWord ++ tailWord_3210747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210747).length < 2 ^ (prefixWord ++ tailWord_3210747).sum := by decide
  have hdescent : baseEnd_3210747 < baseStart_3210747 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210751 : List Nat := [1, 1, 2, 2, 1, 2, 2, 6, 1, 3, 2]
def baseStart_3210751 : Nat := 118140960795 + 3210751 * 2 ^ 59
def prefixEnd_3210751 : Nat := 4983230072969 + 3 ^ 40 * 3210751 * 2
def baseEnd_3210751 : Nat := 1648658524904072655646531

theorem tailTrace_3210751 : CollatzResearch.WordTrace tailWord_3210751 prefixEnd_3210751 1648658524904072655646531 := by
  unfold tailWord_3210751
  simp only [CollatzResearch.WordTrace]
  refine ⟨117105709591004954459328107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78070473060669969639552071 117105709591004954459328107)
  ·
    refine ⟨175658564386507431688992161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117105709591004954459328107 175658564386507431688992161)
    ·
      refine ⟨131743923289880573766744121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175658564386507431688992161 131743923289880573766744121)
      ·
        refine ⟨98807942467410430325058091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 131743923289880573766744121 98807942467410430325058091)
        ·
          refine ⟨148211913701115645487587137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98807942467410430325058091 148211913701115645487587137)
          ·
            refine ⟨111158935275836734115690353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 148211913701115645487587137 111158935275836734115690353)
            ·
              refine ⟨83369201456877550586767765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 111158935275836734115690353 83369201456877550586767765)
              ·
                refine ⟨3907931318291135183754739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 83369201456877550586767765 3907931318291135183754739)
                ·
                  refine ⟨5861896977436702775632109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3907931318291135183754739 5861896977436702775632109)
                  ·
                    refine ⟨2198211366538763540862041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5861896977436702775632109 2198211366538763540862041)
                    ·
                      refine ⟨1648658524904072655646531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2198211366538763540862041 1648658524904072655646531)
                      ·
                        rfl

theorem cell23_3210751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 3, 2].length) (baseStart_3210751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210751 prefixEnd_3210751 := by exact prefixLift 3210751
  have htrace : WordTrace (prefixWord ++ tailWord_3210751) baseStart_3210751 baseEnd_3210751 := by
    simpa [prefixWord, tailWord_3210751, baseEnd_3210751] using wordTrace_append hprefix tailTrace_3210751
  have hstable : (prefixWord ++ tailWord_3210751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210751).length < 2 ^ (prefixWord ++ tailWord_3210751).sum := by decide
  have hdescent : baseEnd_3210751 < baseStart_3210751 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210757 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 4, 6]
def baseStart_3210757 : Nat := 118140960795 + 3210757 * 2 ^ 59
def prefixEnd_3210757 : Nat := 4983230072969 + 3 ^ 40 * 3210757 * 2
def baseEnd_3210757 : Nat := 549553868595999877390501

theorem tailTrace_3210757 : CollatzResearch.WordTrace tailWord_3210757 prefixEnd_3210757 549553868595999877390501 := by
  unfold tailWord_3210757
  simp only [CollatzResearch.WordTrace]
  refine ⟨117105928428983217484046525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78070618952655478322697683 117105928428983217484046525)
  ·
    refine ⟨43914723160868706556517447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117105928428983217484046525 43914723160868706556517447)
    ·
      refine ⟨65872084741303059834776171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43914723160868706556517447 65872084741303059834776171)
      ·
        refine ⟨98808127111954589752164257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65872084741303059834776171 98808127111954589752164257)
        ·
          refine ⟨74106095333965942314123193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98808127111954589752164257 74106095333965942314123193)
          ·
            refine ⟨55579571500474456735592395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74106095333965942314123193 55579571500474456735592395)
            ·
              refine ⟨83369357250711685103388593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55579571500474456735592395 83369357250711685103388593)
              ·
                refine ⟨62527017938033763827541445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 83369357250711685103388593 62527017938033763827541445)
                ·
                  refine ⟨11723815863381330717664021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 62527017938033763827541445 11723815863381330717664021)
                  ·
                    refine ⟨549553868595999877390501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 11723815863381330717664021 549553868595999877390501)
                    ·
                      rfl

theorem cell23_3210757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 4, 6].length) (baseStart_3210757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210757 prefixEnd_3210757 := by exact prefixLift 3210757
  have htrace : WordTrace (prefixWord ++ tailWord_3210757) baseStart_3210757 baseEnd_3210757 := by
    simpa [prefixWord, tailWord_3210757, baseEnd_3210757] using wordTrace_append hprefix tailTrace_3210757
  have hstable : (prefixWord ++ tailWord_3210757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210757).length < 2 ^ (prefixWord ++ tailWord_3210757).sum := by decide
  have hdescent : baseEnd_3210757 < baseStart_3210757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210767 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 5]
def baseStart_3210767 : Nat := 118140960795 + 3210767 * 2 ^ 59
def prefixEnd_3210767 : Nat := 4983230072969 + 3 ^ 40 * 3210767 * 2
def baseEnd_3210767 : Nat := 1648666740594544593046457

theorem tailTrace_3210767 : CollatzResearch.WordTrace tailWord_3210767 prefixEnd_3210767 1648666740594544593046457 := by
  unfold tailWord_3210767
  simp only [CollatzResearch.WordTrace]
  refine ⟨117106293158946989191910555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78070862105964659461273703 117106293158946989191910555)
  ·
    refine ⟨175659439738420483787865833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117106293158946989191910555 175659439738420483787865833)
    ·
      refine ⟨131744579803815362840899375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175659439738420483787865833 131744579803815362840899375)
      ·
        refine ⟨197616869705723044261349063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131744579803815362840899375 197616869705723044261349063)
        ·
          refine ⟨296425304558584566392023595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 197616869705723044261349063 296425304558584566392023595)
          ·
            refine ⟨444637956837876849588035393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 296425304558584566392023595 444637956837876849588035393)
            ·
              refine ⟨333478467628407637191026545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 444637956837876849588035393 333478467628407637191026545)
              ·
                refine ⟨250108850721305727893269909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 333478467628407637191026545 250108850721305727893269909)
                ·
                  refine ⟨11723852377561205994997027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 250108850721305727893269909 11723852377561205994997027)
                  ·
                    refine ⟨17585778566341808992495541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11723852377561205994997027 17585778566341808992495541)
                    ·
                      refine ⟨1648666740594544593046457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17585778566341808992495541 1648666740594544593046457)
                      ·
                        rfl

theorem cell23_3210767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 6, 1, 5].length) (baseStart_3210767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210767 prefixEnd_3210767 := by exact prefixLift 3210767
  have htrace : WordTrace (prefixWord ++ tailWord_3210767) baseStart_3210767 baseEnd_3210767 := by
    simpa [prefixWord, tailWord_3210767, baseEnd_3210767] using wordTrace_append hprefix tailTrace_3210767
  have hstable : (prefixWord ++ tailWord_3210767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210767).length < 2 ^ (prefixWord ++ tailWord_3210767).sum := by decide
  have hdescent : baseEnd_3210767 < baseStart_3210767 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210781 : List Nat := [1, 4, 2, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_3210781 : Nat := 118140960795 + 3210781 * 2 ^ 59
def prefixEnd_3210781 : Nat := 4983230072969 + 3 ^ 40 * 3210781 * 2
def baseEnd_3210781 : Nat := 1648673929323707538271393

theorem tailTrace_3210781 : CollatzResearch.WordTrace tailWord_3210781 prefixEnd_3210781 1648673929323707538271393 := by
  unfold tailWord_3210781
  simp only [CollatzResearch.WordTrace]
  refine ⟨117106803780896269582920197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78071202520597513055280131 117106803780896269582920197)
  ·
    refine ⟨21957525708918050546797537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 117106803780896269582920197 21957525708918050546797537)
    ·
      refine ⟨16468144281688537910098153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21957525708918050546797537 16468144281688537910098153)
      ·
        refine ⟨12351108211266403432573615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16468144281688537910098153 12351108211266403432573615)
        ·
          refine ⟨18526662316899605148860423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12351108211266403432573615 18526662316899605148860423)
          ·
            refine ⟨27789993475349407723290635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18526662316899605148860423 27789993475349407723290635)
            ·
              refine ⟨41684990213024111584935953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27789993475349407723290635 41684990213024111584935953)
              ·
                refine ⟨31263742659768083688701965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41684990213024111584935953 31263742659768083688701965)
                ·
                  refine ⟨11723903497413031383263237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31263742659768083688701965 11723903497413031383263237)
                  ·
                    refine ⟨2198231905764943384361857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11723903497413031383263237 2198231905764943384361857)
                    ·
                      refine ⟨1648673929323707538271393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2198231905764943384361857 1648673929323707538271393)
                      ·
                        rfl

theorem cell23_3210781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_3210781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210781 prefixEnd_3210781 := by exact prefixLift 3210781
  have htrace : WordTrace (prefixWord ++ tailWord_3210781) baseStart_3210781 baseEnd_3210781 := by
    simpa [prefixWord, tailWord_3210781, baseEnd_3210781] using wordTrace_append hprefix tailTrace_3210781
  have hstable : (prefixWord ++ tailWord_3210781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210781).length < 2 ^ (prefixWord ++ tailWord_3210781).sum := by decide
  have hdescent : baseEnd_3210781 < baseStart_3210781 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210782 : List Nat := [4, 3, 3, 1, 2, 1, 1, 8]
def baseStart_3210782 : Nat := 118140960795 + 3210782 * 2 ^ 59
def prefixEnd_3210782 : Nat := 4983230072969 + 3 ^ 40 * 3210782 * 2
def baseEnd_3210782 : Nat := 61062016400161556828107

theorem tailTrace_3210782 : CollatzResearch.WordTrace tailWord_3210782 prefixEnd_3210782 61062016400161556828107 := by
  unfold tailWord_3210782
  simp only [CollatzResearch.WordTrace]
  refine ⟨14638355031736580844213325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78071226835928431169137733 14638355031736580844213325)
  ·
    refine ⟨5489383136901217816579997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14638355031736580844213325 5489383136901217816579997)
    ·
      refine ⟨2058518676337956681217499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5489383136901217816579997 2058518676337956681217499)
      ·
        refine ⟨3087778014506935021826249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2058518676337956681217499 3087778014506935021826249)
        ·
          refine ⟨2315833510880201266369687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3087778014506935021826249 2315833510880201266369687)
          ·
            refine ⟨3473750266320301899554531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2315833510880201266369687 3473750266320301899554531)
            ·
              refine ⟨5210625399480452849331797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3473750266320301899554531 5210625399480452849331797)
              ·
                refine ⟨61062016400161556828107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5210625399480452849331797 61062016400161556828107)
                ·
                  rfl

theorem cell23_3210782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 8].length) (baseStart_3210782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210782 prefixEnd_3210782 := by exact prefixLift 3210782
  have htrace : WordTrace (prefixWord ++ tailWord_3210782) baseStart_3210782 baseEnd_3210782 := by
    simpa [prefixWord, tailWord_3210782, baseEnd_3210782] using wordTrace_append hprefix tailTrace_3210782
  have hstable : (prefixWord ++ tailWord_3210782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210782).length < 2 ^ (prefixWord ++ tailWord_3210782).sum := by decide
  have hdescent : baseEnd_3210782 < baseStart_3210782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210798 : List Nat := [4, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2]
def baseStart_3210798 : Nat := 118140960795 + 3210798 * 2 ^ 59
def prefixEnd_3210798 : Nat := 4983230072969 + 3 ^ 40 * 3210798 * 2
def baseEnd_3210798 : Nat := 1648682658494833971758815

theorem tailTrace_3210798 : CollatzResearch.WordTrace tailWord_3210798 prefixEnd_3210798 1648682658494833971758815 := by
  unfold tailWord_3210798
  simp only [CollatzResearch.WordTrace]
  refine ⟨14638427977729335185786131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 78071615881223120990859365 14638427977729335185786131)
  ·
    refine ⟨21957641966594002778679197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14638427977729335185786131 21957641966594002778679197)
    ·
      refine ⟨8234115737472751042004699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21957641966594002778679197 8234115737472751042004699)
      ·
        refine ⟨12351173606209126563007049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8234115737472751042004699 12351173606209126563007049)
        ·
          refine ⟨9263380204656844922255287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12351173606209126563007049 9263380204656844922255287)
          ·
            refine ⟨13895070306985267383382931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9263380204656844922255287 13895070306985267383382931)
            ·
              refine ⟨20842605460477901075074397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13895070306985267383382931 20842605460477901075074397)
              ·
                refine ⟨7815977047679212903152899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20842605460477901075074397 7815977047679212903152899)
                ·
                  refine ⟨11723965571518819354729349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7815977047679212903152899 11723965571518819354729349)
                  ·
                    refine ⟨2198243544659778629011753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11723965571518819354729349 2198243544659778629011753)
                    ·
                      refine ⟨1648682658494833971758815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2198243544659778629011753 1648682658494833971758815)
                      ·
                        rfl

theorem cell23_3210798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_3210798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210798 prefixEnd_3210798 := by exact prefixLift 3210798
  have htrace : WordTrace (prefixWord ++ tailWord_3210798) baseStart_3210798 baseEnd_3210798 := by
    simpa [prefixWord, tailWord_3210798, baseEnd_3210798] using wordTrace_append hprefix tailTrace_3210798
  have hstable : (prefixWord ++ tailWord_3210798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210798).length < 2 ^ (prefixWord ++ tailWord_3210798).sum := by decide
  have hdescent : baseEnd_3210798 < baseStart_3210798 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210821 : List Nat := [1, 3, 1, 1, 1, 4, 4, 3, 5]
def baseStart_3210821 : Nat := 118140960795 + 3210821 * 2 ^ 59
def prefixEnd_3210821 : Nat := 4983230072969 + 3 ^ 40 * 3210821 * 2
def baseEnd_3210821 : Nat := 183188274283320820196801

theorem tailTrace_3210821 : CollatzResearch.WordTrace tailWord_3210821 prefixEnd_3210821 183188274283320820196801 := by
  unfold tailWord_3210821
  simp only [CollatzResearch.WordTrace]
  refine ⟨117108262700751356414376317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78072175133834237609584211 117108262700751356414376317)
  ·
    refine ⟨43915598512781758655391119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117108262700751356414376317 43915598512781758655391119)
    ·
      refine ⟨65873397769172637983086679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43915598512781758655391119 65873397769172637983086679)
      ·
        refine ⟨98810096653758956974630019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65873397769172637983086679 98810096653758956974630019)
        ·
          refine ⟨148215144980638435461945029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 98810096653758956974630019 148215144980638435461945029)
          ·
            refine ⟨27790339683869706649114693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148215144980638435461945029 27790339683869706649114693)
            ·
              refine ⟨5210688690725569996709005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27790339683869706649114693 5210688690725569996709005)
              ·
                refine ⟨1954008259022088748765877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5210688690725569996709005 1954008259022088748765877)
                ·
                  refine ⟨183188274283320820196801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1954008259022088748765877 183188274283320820196801)
                  ·
                    rfl

theorem cell23_3210821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 5].length) (baseStart_3210821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210821 prefixEnd_3210821 := by exact prefixLift 3210821
  have htrace : WordTrace (prefixWord ++ tailWord_3210821) baseStart_3210821 baseEnd_3210821 := by
    simpa [prefixWord, tailWord_3210821, baseEnd_3210821] using wordTrace_append hprefix tailTrace_3210821
  have hstable : (prefixWord ++ tailWord_3210821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210821).length < 2 ^ (prefixWord ++ tailWord_3210821).sum := by decide
  have hdescent : baseEnd_3210821 < baseStart_3210821 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210891 : List Nat := [1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 3]
def baseStart_3210891 : Nat := 118140960795 + 3210891 * 2 ^ 59
def prefixEnd_3210891 : Nat := 4983230072969 + 3 ^ 40 * 3210891 * 2
def baseEnd_3210891 : Nat := 1648730412195702107895887

theorem tailTrace_3210891 : CollatzResearch.WordTrace tailWord_3210891 prefixEnd_3210891 1648730412195702107895887 := by
  unfold tailWord_3210891
  simp only [CollatzResearch.WordTrace]
  refine ⟨117110815810497758369424527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78073877206998505579616351 117110815810497758369424527)
  ·
    refine ⟨175666223715746637554136791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117110815810497758369424527 175666223715746637554136791)
    ·
      refine ⟨263499335573619956331205187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175666223715746637554136791 263499335573619956331205187)
      ·
        refine ⟨395249003360429934496807781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 263499335573619956331205187 395249003360429934496807781)
        ·
          refine ⟨74109188130080612718151459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 395249003360429934496807781 74109188130080612718151459)
          ·
            refine ⟨111163782195120919077227189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 74109188130080612718151459 111163782195120919077227189)
            ·
              refine ⟨10421604580792586163490049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 111163782195120919077227189 10421604580792586163490049)
              ·
                refine ⟨7816203435594439622617537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10421604580792586163490049 7816203435594439622617537)
                ·
                  refine ⟨5862152576695829716963153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7816203435594439622617537 5862152576695829716963153)
                  ·
                    refine ⟨4396614432521872287722365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5862152576695829716963153 4396614432521872287722365)
                    ·
                      refine ⟨1648730412195702107895887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4396614432521872287722365 1648730412195702107895887)
                      ·
                        rfl

theorem cell23_3210891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 3].length) (baseStart_3210891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210891 prefixEnd_3210891 := by exact prefixLift 3210891
  have htrace : WordTrace (prefixWord ++ tailWord_3210891) baseStart_3210891 baseEnd_3210891 := by
    simpa [prefixWord, tailWord_3210891, baseEnd_3210891] using wordTrace_append hprefix tailTrace_3210891
  have hstable : (prefixWord ++ tailWord_3210891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210891).length < 2 ^ (prefixWord ++ tailWord_3210891).sum := by decide
  have hdescent : baseEnd_3210891 < baseStart_3210891 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210961 : List Nat := [1, 2, 2, 1, 2, 4, 1, 2, 3, 1, 4]
def baseStart_3210961 : Nat := 118140960795 + 3210961 * 2 ^ 59
def prefixEnd_3210961 : Nat := 4983230072969 + 3 ^ 40 * 3210961 * 2
def baseEnd_3210961 : Nat := 1648766355841516834020565

theorem tailTrace_3210961 : CollatzResearch.WordTrace tailWord_3210961 prefixEnd_3210961 1648766355841516834020565 := by
  unfold tailWord_3210961
  simp only [CollatzResearch.WordTrace]
  refine ⟨117113368920244160324472737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78075579280162773549648491 117113368920244160324472737)
  ·
    refine ⟨87835026690183120243354553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117113368920244160324472737 87835026690183120243354553)
    ·
      refine ⟨65876270017637340182515915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87835026690183120243354553 65876270017637340182515915)
      ·
        refine ⟨98814405026456010273773873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 65876270017637340182515915 98814405026456010273773873)
        ·
          refine ⟨74110803769842007705330405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98814405026456010273773873 74110803769842007705330405)
          ·
            refine ⟨13895775706845376444749451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 74110803769842007705330405 13895775706845376444749451)
            ·
              refine ⟨20843663560268064667124177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13895775706845376444749451 20843663560268064667124177)
              ·
                refine ⟨15632747670201048500343133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20843663560268064667124177 15632747670201048500343133)
                ·
                  refine ⟨5862280376325393187628675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15632747670201048500343133 5862280376325393187628675)
                  ·
                    refine ⟨8793420564488089781443013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5862280376325393187628675 8793420564488089781443013)
                    ·
                      refine ⟨1648766355841516834020565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8793420564488089781443013 1648766355841516834020565)
                      ·
                        rfl

theorem cell23_3210961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_3210961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210961 prefixEnd_3210961 := by exact prefixLift 3210961
  have htrace : WordTrace (prefixWord ++ tailWord_3210961) baseStart_3210961 baseEnd_3210961 := by
    simpa [prefixWord, tailWord_3210961, baseEnd_3210961] using wordTrace_append hprefix tailTrace_3210961
  have hstable : (prefixWord ++ tailWord_3210961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210961).length < 2 ^ (prefixWord ++ tailWord_3210961).sum := by decide
  have hdescent : baseEnd_3210961 < baseStart_3210961 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210972 : List Nat := [2, 2, 5, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_3210972 : Nat := 118140960795 + 3210972 * 2 ^ 59
def prefixEnd_3210972 : Nat := 4983230072969 + 3 ^ 40 * 3210972 * 2
def baseEnd_3210972 : Nat := 1648772004128716290983015

theorem tailTrace_3210972 : CollatzResearch.WordTrace tailWord_3210972 prefixEnd_3210972 1648772004128716290983015 := by
  unfold tailWord_3210972
  simp only [CollatzResearch.WordTrace]
  refine ⟨58556885061602154601561585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78075846748802872802082113 58556885061602154601561585)
  ·
    refine ⟨43917663796201615951171189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 58556885061602154601561585 43917663796201615951171189)
    ·
      refine ⟨4117280980893901495422299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43917663796201615951171189 4117280980893901495422299)
      ·
        refine ⟨6175921471340852243133449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4117280980893901495422299 6175921471340852243133449)
        ·
          refine ⟨4631941103505639182350087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6175921471340852243133449 4631941103505639182350087)
          ·
            refine ⟨6947911655258458773525131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4631941103505639182350087 6947911655258458773525131)
            ·
              refine ⟨10421867482887688160287697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6947911655258458773525131 10421867482887688160287697)
              ·
                refine ⟨7816400612165766120215773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10421867482887688160287697 7816400612165766120215773)
                ·
                  refine ⟨2931150229562162295080915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7816400612165766120215773 2931150229562162295080915)
                  ·
                    refine ⟨4396725344343243442621373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2931150229562162295080915 4396725344343243442621373)
                    ·
                      refine ⟨1648772004128716290983015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4396725344343243442621373 1648772004128716290983015)
                      ·
                        rfl

theorem cell23_3210972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_3210972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210972 prefixEnd_3210972 := by exact prefixLift 3210972
  have htrace : WordTrace (prefixWord ++ tailWord_3210972) baseStart_3210972 baseEnd_3210972 := by
    simpa [prefixWord, tailWord_3210972, baseEnd_3210972] using wordTrace_append hprefix tailTrace_3210972
  have hstable : (prefixWord ++ tailWord_3210972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210972).length < 2 ^ (prefixWord ++ tailWord_3210972).sum := by decide
  have hdescent : baseEnd_3210972 < baseStart_3210972 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3210991 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 4]
def baseStart_3210991 : Nat := 118140960795 + 3210991 * 2 ^ 59
def prefixEnd_3210991 : Nat := 4983230072969 + 3 ^ 40 * 3210991 * 2
def baseEnd_3210991 : Nat := 1648781760261151716645427

theorem tailTrace_3210991 : CollatzResearch.WordTrace tailWord_3210991 prefixEnd_3210991 1648781760261151716645427 := by
  unfold tailWord_3210991
  simp only [CollatzResearch.WordTrace]
  refine ⟨117114463110135475448064827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78076308740090316965376551 117114463110135475448064827)
  ·
    refine ⟨175671694665203213172097241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117114463110135475448064827 175671694665203213172097241)
    ·
      refine ⟨131753770998902409879072931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 175671694665203213172097241 131753770998902409879072931)
      ·
        refine ⟨197630656498353614818609397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131753770998902409879072931 197630656498353614818609397)
        ·
          refine ⟨18527874046720651389244631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 197630656498353614818609397 18527874046720651389244631)
          ·
            refine ⟨27791811070080977083866947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18527874046720651389244631 27791811070080977083866947)
            ·
              refine ⟨41687716605121465625800421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27791811070080977083866947 41687716605121465625800421)
              ·
                refine ⟨7816446863460274804837579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 41687716605121465625800421 7816446863460274804837579)
                ·
                  refine ⟨11724670295190412207256369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7816446863460274804837579 11724670295190412207256369)
                  ·
                    refine ⟨8793502721392809155442277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11724670295190412207256369 8793502721392809155442277)
                    ·
                      refine ⟨1648781760261151716645427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8793502721392809155442277 1648781760261151716645427)
                      ·
                        rfl

theorem cell23_3210991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 4].length) (baseStart_3210991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3210991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3210991 prefixEnd_3210991 := by exact prefixLift 3210991
  have htrace : WordTrace (prefixWord ++ tailWord_3210991) baseStart_3210991 baseEnd_3210991 := by
    simpa [prefixWord, tailWord_3210991, baseEnd_3210991] using wordTrace_append hprefix tailTrace_3210991
  have hstable : (prefixWord ++ tailWord_3210991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3210991).length < 2 ^ (prefixWord ++ tailWord_3210991).sum := by decide
  have hdescent : baseEnd_3210991 < baseStart_3210991 := by decide
  rcases family_descends (prefixWord ++ tailWord_3210991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211011 : List Nat := [1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 3]
def baseStart_3211011 : Nat := 118140960795 + 3211011 * 2 ^ 59
def prefixEnd_3211011 : Nat := 4983230072969 + 3 ^ 40 * 3211011 * 2
def baseEnd_3211011 : Nat := 1648792029874241638395335

theorem tailTrace_3211011 : CollatzResearch.WordTrace tailWord_3211011 prefixEnd_3211011 1648792029874241638395335 := by
  unfold tailWord_3211011
  simp only [CollatzResearch.WordTrace]
  refine ⟨117115192570063018863792887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78076795046708679242528591 117115192570063018863792887)
  ·
    refine ⟨175672788855094528295689331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 117115192570063018863792887 175672788855094528295689331)
    ·
      refine ⟨263509183282641792443533997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 175672788855094528295689331 263509183282641792443533997)
      ·
        refine ⟨98815943730990672166325249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 263509183282641792443533997 98815943730990672166325249)
        ·
          refine ⟨74111957798243004124743937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 98815943730990672166325249 74111957798243004124743937)
          ·
            refine ⟨55583968348682253093557953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 74111957798243004124743937 55583968348682253093557953)
            ·
              refine ⟨41687976261511689820168465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 55583968348682253093557953 41687976261511689820168465)
              ·
                refine ⟨31265982196133767365126349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 41687976261511689820168465 31265982196133767365126349)
                ·
                  refine ⟨11724743323550162761922381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31265982196133767365126349 11724743323550162761922381)
                  ·
                    refine ⟨4396778746331311035720893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11724743323550162761922381 4396778746331311035720893)
                    ·
                      refine ⟨1648792029874241638395335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4396778746331311035720893 1648792029874241638395335)
                      ·
                        rfl

theorem cell23_3211011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 3].length) (baseStart_3211011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211011 prefixEnd_3211011 := by exact prefixLift 3211011
  have htrace : WordTrace (prefixWord ++ tailWord_3211011) baseStart_3211011 baseEnd_3211011 := by
    simpa [prefixWord, tailWord_3211011, baseEnd_3211011] using wordTrace_append hprefix tailTrace_3211011
  have hstable : (prefixWord ++ tailWord_3211011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211011).length < 2 ^ (prefixWord ++ tailWord_3211011).sum := by decide
  have hdescent : baseEnd_3211011 < baseStart_3211011 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211012 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_3211012 : Nat := 118140960795 + 3211012 * 2 ^ 59
def prefixEnd_3211012 : Nat := 4983230072969 + 3 ^ 40 * 3211012 * 2
def baseEnd_3211012 : Nat := 1648792543354896134482831

theorem tailTrace_3211012 : CollatzResearch.WordTrace tailWord_3211012 prefixEnd_3211012 1648792543354896134482831 := by
  unfold tailWord_3211012
  simp only [CollatzResearch.WordTrace]
  refine ⟨58557614521529698017289645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78076819362039597356386193 58557614521529698017289645)
  ·
    refine ⟨21959105445573636756483617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 58557614521529698017289645 21959105445573636756483617)
    ·
      refine ⟨16469329084180227567362713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21959105445573636756483617 16469329084180227567362713)
      ·
        refine ⟨12351996813135170675522035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16469329084180227567362713 12351996813135170675522035)
        ·
          refine ⟨18527995219702756013283053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12351996813135170675522035 18527995219702756013283053)
          ·
            refine ⟨6947998207388533504981145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18527995219702756013283053 6947998207388533504981145)
            ·
              refine ⟨5210998655541400128735859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6947998207388533504981145 5210998655541400128735859)
              ·
                refine ⟨7816497983312100193103789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5210998655541400128735859 7816497983312100193103789)
                ·
                  refine ⟨2931186743742037572413921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7816497983312100193103789 2931186743742037572413921)
                  ·
                    refine ⟨2198390057806528179310441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2931186743742037572413921 2198390057806528179310441)
                    ·
                      refine ⟨1648792543354896134482831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2198390057806528179310441 1648792543354896134482831)
                      ·
                        rfl

theorem cell23_3211012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_3211012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211012 prefixEnd_3211012 := by exact prefixLift 3211012
  have htrace : WordTrace (prefixWord ++ tailWord_3211012) baseStart_3211012 baseEnd_3211012 := by
    simpa [prefixWord, tailWord_3211012, baseEnd_3211012] using wordTrace_append hprefix tailTrace_3211012
  have hstable : (prefixWord ++ tailWord_3211012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211012).length < 2 ^ (prefixWord ++ tailWord_3211012).sum := by decide
  have hdescent : baseEnd_3211012 < baseStart_3211012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211041 : List Nat := [1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 5]
def baseStart_3211041 : Nat := 118140960795 + 3211041 * 2 ^ 59
def prefixEnd_3211041 : Nat := 4983230072969 + 3 ^ 40 * 3211041 * 2
def baseEnd_3211041 : Nat := 1648807434293876521020197

theorem tailTrace_3211041 : CollatzResearch.WordTrace tailWord_3211041 prefixEnd_3211041 1648807434293876521020197 := by
  unfold tailWord_3211041
  simp only [CollatzResearch.WordTrace]
  refine ⟨117116286759954333987384977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78077524506636222658256651 117116286759954333987384977)
  ·
    refine ⟨87837215069965750490538733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117116286759954333987384977 87837215069965750490538733)
    ·
      refine ⟨32938955651237156433952025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 87837215069965750490538733 32938955651237156433952025)
      ·
        refine ⟨24704216738427867325464019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32938955651237156433952025 24704216738427867325464019)
        ·
          refine ⟨37056325107641800988196029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24704216738427867325464019 37056325107641800988196029)
          ·
            refine ⟨13896121915365675370573511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37056325107641800988196029 13896121915365675370573511)
            ·
              refine ⟨20844182873048513055860267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13896121915365675370573511 20844182873048513055860267)
              ·
                refine ⟨31266274309572769583790401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20844182873048513055860267 31266274309572769583790401)
                ·
                  refine ⟨23449705732179577187842801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31266274309572769583790401 23449705732179577187842801)
                  ·
                    refine ⟨17587279299134682890882101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23449705732179577187842801 17587279299134682890882101)
                    ·
                      refine ⟨1648807434293876521020197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 17587279299134682890882101 1648807434293876521020197)
                      ·
                        rfl

theorem cell23_3211041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_3211041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211041 prefixEnd_3211041 := by exact prefixLift 3211041
  have htrace : WordTrace (prefixWord ++ tailWord_3211041) baseStart_3211041 baseEnd_3211041 := by
    simpa [prefixWord, tailWord_3211041, baseEnd_3211041] using wordTrace_append hprefix tailTrace_3211041
  have hstable : (prefixWord ++ tailWord_3211041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211041).length < 2 ^ (prefixWord ++ tailWord_3211041).sum := by decide
  have hdescent : baseEnd_3211041 < baseStart_3211041 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211062 : List Nat := [5, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_3211062 : Nat := 118140960795 + 3211062 * 2 ^ 59
def prefixEnd_3211062 : Nat := 4983230072969 + 3 ^ 40 * 3211062 * 2
def baseEnd_3211062 : Nat := 1648818217387620938857601

theorem tailTrace_3211062 : CollatzResearch.WordTrace tailWord_3211062 prefixEnd_3211062 1648818217387620938857601 := by
  unfold tailWord_3211062
  simp only [CollatzResearch.WordTrace]
  refine ⟨7319815793304890910868715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 78078035128585503049266293 7319815793304890910868715)
  ·
    refine ⟨10979723689957336366303073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7319815793304890910868715 10979723689957336366303073)
    ·
      refine ⟨8234792767468002274727305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10979723689957336366303073 8234792767468002274727305)
      ·
        refine ⟨6176094575601001706045479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8234792767468002274727305 6176094575601001706045479)
        ·
          refine ⟨9264141863401502559068219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6176094575601001706045479 9264141863401502559068219)
          ·
            refine ⟨13896212795102253838602329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9264141863401502559068219 13896212795102253838602329)
            ·
              refine ⟨10422159596326690378951747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13896212795102253838602329 10422159596326690378951747)
              ·
                refine ⟨15633239394490035568427621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10422159596326690378951747 15633239394490035568427621)
                ·
                  refine ⟨2931232386466881669080179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15633239394490035568427621 2931232386466881669080179)
                  ·
                    refine ⟨4396848579700322503620269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2931232386466881669080179 4396848579700322503620269)
                    ·
                      refine ⟨1648818217387620938857601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4396848579700322503620269 1648818217387620938857601)
                      ·
                        rfl

theorem cell23_3211062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_3211062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211062 prefixEnd_3211062 := by exact prefixLift 3211062
  have htrace : WordTrace (prefixWord ++ tailWord_3211062) baseStart_3211062 baseEnd_3211062 := by
    simpa [prefixWord, tailWord_3211062, baseEnd_3211062] using wordTrace_append hprefix tailTrace_3211062
  have hstable : (prefixWord ++ tailWord_3211062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211062).length < 2 ^ (prefixWord ++ tailWord_3211062).sum := by decide
  have hdescent : baseEnd_3211062 < baseStart_3211062 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211081 : List Nat := [1, 2, 1, 1, 2, 4, 2, 1, 1, 4, 4]
def baseStart_3211081 : Nat := 118140960795 + 3211081 * 2 ^ 59
def prefixEnd_3211081 : Nat := 4983230072969 + 3 ^ 40 * 3211081 * 2
def baseEnd_3211081 : Nat := 1648827973520056364520013

theorem tailTrace_3211081 : CollatzResearch.WordTrace tailWord_3211081 prefixEnd_3211081 1648827973520056364520013 := by
  unfold tailWord_3211081
  simp only [CollatzResearch.WordTrace]
  refine ⟨117117745679809420818841097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78078497119872947212560731 117117745679809420818841097)
  ·
    refine ⟨87838309259857065614130823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117117745679809420818841097 87838309259857065614130823)
    ·
      refine ⟨131757463889785598421196235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87838309259857065614130823 131757463889785598421196235)
      ·
        refine ⟨197636195834678397631794353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 131757463889785598421196235 197636195834678397631794353)
        ·
          refine ⟨148227146876008798223845765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 197636195834678397631794353 148227146876008798223845765)
          ·
            refine ⟨27792590039251649666971081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 148227146876008798223845765 27792590039251649666971081)
            ·
              refine ⟨20844442529438737250228311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27792590039251649666971081 20844442529438737250228311)
              ·
                refine ⟨31266663794158105875342467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20844442529438737250228311 31266663794158105875342467)
                ·
                  refine ⟨46899995691237158813013701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31266663794158105875342467 46899995691237158813013701)
                  ·
                    refine ⟨8793749192106967277440069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46899995691237158813013701 8793749192106967277440069)
                    ·
                      refine ⟨1648827973520056364520013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8793749192106967277440069 1648827973520056364520013)
                      ·
                        rfl

theorem cell23_3211081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 4, 4].length) (baseStart_3211081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211081 prefixEnd_3211081 := by exact prefixLift 3211081
  have htrace : WordTrace (prefixWord ++ tailWord_3211081) baseStart_3211081 baseEnd_3211081 := by
    simpa [prefixWord, tailWord_3211081, baseEnd_3211081] using wordTrace_append hprefix tailTrace_3211081
  have hstable : (prefixWord ++ tailWord_3211081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211081).length < 2 ^ (prefixWord ++ tailWord_3211081).sum := by decide
  have hdescent : baseEnd_3211081 < baseStart_3211081 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211125 : List Nat := [1, 3, 4, 1, 1, 1, 3, 4, 5]
def baseStart_3211125 : Nat := 118140960795 + 3211125 * 2 ^ 59
def prefixEnd_3211125 : Nat := 4983230072969 + 3 ^ 40 * 3211125 * 2
def baseEnd_3211125 : Nat := 183205618518761576929979

theorem tailTrace_3211125 : CollatzResearch.WordTrace tailWord_3211125 prefixEnd_3211125 183205618518761576929979 := by
  unfold tailWord_3211125
  simp only [CollatzResearch.WordTrace]
  refine ⟨117119350491650016333442829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78079566994433344222295219 117119350491650016333442829)
  ·
    refine ⟨43919756434368756125041061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 117119350491650016333442829 43919756434368756125041061)
    ·
      refine ⟨8234954331444141773445199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43919756434368756125041061 8234954331444141773445199)
      ·
        refine ⟨12352431497166212660167799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8234954331444141773445199 12352431497166212660167799)
        ·
          refine ⟨18528647245749318990251699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12352431497166212660167799 18528647245749318990251699)
          ·
            refine ⟨27792970868623978485377549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18528647245749318990251699 27792970868623978485377549)
            ·
              refine ⟨10422364075733991932016581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27792970868623978485377549 10422364075733991932016581)
              ·
                refine ⟨1954193264200123487253109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10422364075733991932016581 1954193264200123487253109)
                ·
                  refine ⟨183205618518761576929979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1954193264200123487253109 183205618518761576929979)
                  ·
                    rfl

theorem cell23_3211125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 3, 4, 5].length) (baseStart_3211125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211125 prefixEnd_3211125 := by exact prefixLift 3211125
  have htrace : WordTrace (prefixWord ++ tailWord_3211125) baseStart_3211125 baseEnd_3211125 := by
    simpa [prefixWord, tailWord_3211125, baseEnd_3211125] using wordTrace_append hprefix tailTrace_3211125
  have hstable : (prefixWord ++ tailWord_3211125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211125).length < 2 ^ (prefixWord ++ tailWord_3211125).sum := by decide
  have hdescent : baseEnd_3211125 < baseStart_3211125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211168 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 7, 4]
def baseStart_3211168 : Nat := 118140960795 + 3211168 * 2 ^ 59
def prefixEnd_3211168 : Nat := 4983230072969 + 3 ^ 40 * 3211168 * 2
def baseEnd_3211168 : Nat := 549624215445665841377371

theorem tailTrace_3211168 : CollatzResearch.WordTrace tailWord_3211168 prefixEnd_3211168 549624215445665841377371 := by
  unfold tailWord_3211168
  simp only [CollatzResearch.WordTrace]
  refine ⟨58560459415247117338629079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 78080612553662823118172105 58560459415247117338629079)
  ·
    refine ⟨87840689122870676007943619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 58560459415247117338629079 87840689122870676007943619)
    ·
      refine ⟨131761033684306014011915429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 87840689122870676007943619 131761033684306014011915429)
      ·
        refine ⟨24705193815807377627234143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 131761033684306014011915429 24705193815807377627234143)
        ·
          refine ⟨37057790723711066440851215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24705193815807377627234143 37057790723711066440851215)
          ·
            refine ⟨55586686085566599661276823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37057790723711066440851215 55586686085566599661276823)
            ·
              refine ⟨83380029128349899491915235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 55586686085566599661276823 83380029128349899491915235)
              ·
                refine ⟨125070043692524849237872853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 83380029128349899491915235 125070043692524849237872853)
                ·
                  refine ⟨2931329149043551154012645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 125070043692524849237872853 2931329149043551154012645)
                  ·
                    refine ⟨549624215445665841377371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2931329149043551154012645 549624215445665841377371)
                    ·
                      rfl

theorem cell23_3211168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 7, 4].length) (baseStart_3211168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211168 prefixEnd_3211168 := by exact prefixLift 3211168
  have htrace : WordTrace (prefixWord ++ tailWord_3211168) baseStart_3211168 baseEnd_3211168 := by
    simpa [prefixWord, tailWord_3211168, baseEnd_3211168] using wordTrace_append hprefix tailTrace_3211168
  have hstable : (prefixWord ++ tailWord_3211168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211168).length < 2 ^ (prefixWord ++ tailWord_3211168).sum := by decide
  have hdescent : baseEnd_3211168 < baseStart_3211168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211185 : List Nat := [1, 2, 2, 4, 2, 1, 1, 3, 3, 4]
def baseStart_3211185 : Nat := 118140960795 + 3211185 * 2 ^ 59
def prefixEnd_3211185 : Nat := 4983230072969 + 3 ^ 40 * 3211185 * 2
def baseEnd_3211185 : Nat := 549627125169374652539845

theorem tailTrace_3211185 : CollatzResearch.WordTrace tailWord_3211185 prefixEnd_3211185 549627125169374652539845 := by
  unfold tailWord_3211185
  simp only [CollatzResearch.WordTrace]
  refine ⟨117121538871432646580627009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78081025914288431053751339 117121538871432646580627009)
  ·
    refine ⟨87841154153574484935470257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117121538871432646580627009 87841154153574484935470257)
    ·
      refine ⟨65880865615180863701602693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87841154153574484935470257 65880865615180863701602693)
      ·
        refine ⟨12352662302846411944050505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 65880865615180863701602693 12352662302846411944050505)
        ·
          refine ⟨9264496727134808958037879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12352662302846411944050505 9264496727134808958037879)
          ·
            refine ⟨13896745090702213437056819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9264496727134808958037879 13896745090702213437056819)
            ·
              refine ⟨20845117636053320155585229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13896745090702213437056819 20845117636053320155585229)
              ·
                refine ⟨7816919113519995058344461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20845117636053320155585229 7816919113519995058344461)
                ·
                  refine ⟨2931344667569998146879173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7816919113519995058344461 2931344667569998146879173)
                  ·
                    refine ⟨549627125169374652539845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2931344667569998146879173 549627125169374652539845)
                    ·
                      rfl

theorem cell23_3211185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 3, 3, 4].length) (baseStart_3211185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211185 prefixEnd_3211185 := by exact prefixLift 3211185
  have htrace : WordTrace (prefixWord ++ tailWord_3211185) baseStart_3211185 baseEnd_3211185 := by
    simpa [prefixWord, tailWord_3211185, baseEnd_3211185] using wordTrace_append hprefix tailTrace_3211185
  have hstable : (prefixWord ++ tailWord_3211185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211185).length < 2 ^ (prefixWord ++ tailWord_3211185).sum := by decide
  have hdescent : baseEnd_3211185 < baseStart_3211185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3211249 : List Nat := [1, 2, 2, 2, 6, 1, 2, 1, 6]
def baseStart_3211249 : Nat := 118140960795 + 3211249 * 2 ^ 59
def prefixEnd_3211249 : Nat := 4983230072969 + 3 ^ 40 * 3211249 * 2
def baseEnd_3211249 : Nat := 183212693141112411913249

theorem tailTrace_3211249 : CollatzResearch.WordTrace tailWord_3211249 prefixEnd_3211249 183212693141112411913249 := by
  unfold tailWord_3211249
  simp only [CollatzResearch.WordTrace]
  refine ⟨117123873143200785510956801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 78082582095467190340637867 117123873143200785510956801)
  ·
    refine ⟨87842904857400589133217601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 117123873143200785510956801 87842904857400589133217601)
    ·
      refine ⟨65882178643050441849913201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 87842904857400589133217601 65882178643050441849913201)
      ·
        refine ⟨49411633982287831387434901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 65882178643050441849913201 49411633982287831387434901)
        ·
          refine ⟨2316170342919742096286011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49411633982287831387434901 2316170342919742096286011)
          ·
            refine ⟨3474255514379613144429017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2316170342919742096286011 3474255514379613144429017)
            ·
              refine ⟨2605691635784709858321763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3474255514379613144429017 2605691635784709858321763)
              ·
                refine ⟨3908537453677064787482645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2605691635784709858321763 3908537453677064787482645)
                ·
                  refine ⟨183212693141112411913249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3908537453677064787482645 183212693141112411913249)
                  ·
                    rfl

theorem cell23_3211249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 2, 1, 6].length) (baseStart_3211249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3211249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3211249 prefixEnd_3211249 := by exact prefixLift 3211249
  have htrace : WordTrace (prefixWord ++ tailWord_3211249) baseStart_3211249 baseEnd_3211249 := by
    simpa [prefixWord, tailWord_3211249, baseEnd_3211249] using wordTrace_append hprefix tailTrace_3211249
  have hstable : (prefixWord ++ tailWord_3211249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3211249).length < 2 ^ (prefixWord ++ tailWord_3211249).sum := by decide
  have hdescent : baseEnd_3211249 < baseStart_3211249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3211249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
