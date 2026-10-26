import V185TrunkScan23Chunk0823

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4875113 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 9]
def baseStart_4875113 : Nat := 118140960795 + 4875113 * 2 ^ 59
def prefixEnd_4875113 : Nat := 4983230072969 + 3 ^ 40 * 4875113 * 2
def baseEnd_4875113 : Nat := 2503276213982489831667269

theorem tailTrace_4875113 : CollatzResearch.WordTrace tailWord_4875113 prefixEnd_4875113 2503276213982489831667269 := by
  unfold tailWord_4875113
  simp only [CollatzResearch.WordTrace]
  refine ⟨177809978787305678858597993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118539985858203785905731995 177809978787305678858597993)
  ·
    refine ⟨133357484090479259143948495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177809978787305678858597993 133357484090479259143948495)
    ·
      refine ⟨200036226135718888715922743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133357484090479259143948495 200036226135718888715922743)
      ·
        refine ⟨300054339203578333073884115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200036226135718888715922743 300054339203578333073884115)
        ·
          refine ⟨450081508805367499610826173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300054339203578333073884115 450081508805367499610826173)
          ·
            refine ⟨168780565802012812354059815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 450081508805367499610826173 168780565802012812354059815)
            ·
              refine ⟨253170848703019218531089723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168780565802012812354059815 253170848703019218531089723)
              ·
                refine ⟨379756273054528827796634585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253170848703019218531089723 379756273054528827796634585)
                ·
                  refine ⟨284817204790896620847475939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379756273054528827796634585 284817204790896620847475939)
                  ·
                    refine ⟨427225807186344931271213909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 284817204790896620847475939 427225807186344931271213909)
                    ·
                      refine ⟨2503276213982489831667269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 427225807186344931271213909 2503276213982489831667269)
                      ·
                        rfl

theorem cell23_4875113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 2, 1, 9].length) (baseStart_4875113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875113 prefixEnd_4875113 := by exact prefixLift 4875113
  have htrace : WordTrace (prefixWord ++ tailWord_4875113) baseStart_4875113 baseEnd_4875113 := by
    simpa [prefixWord, tailWord_4875113, baseEnd_4875113] using wordTrace_append hprefix tailTrace_4875113
  have hstable : (prefixWord ++ tailWord_4875113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875113).length < 2 ^ (prefixWord ++ tailWord_4875113).sum := by decide
  have hdescent : baseEnd_4875113 < baseStart_4875113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875117 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 2, 2, 3]
def baseStart_4875117 : Nat := 118140960795 + 4875117 * 2 ^ 59
def prefixEnd_4875117 : Nat := 4983230072969 + 3 ^ 40 * 4875117 * 2
def baseEnd_4875117 : Nat := 2503278267905107816017251

theorem tailTrace_4875117 : CollatzResearch.WordTrace tailWord_4875117 prefixEnd_4875117 2503278267905107816017251 := by
  unfold tailWord_4875117
  simp only [CollatzResearch.WordTrace]
  refine ⟨177810124679291187541743605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118540083119527458361162403 177810124679291187541743605)
  ·
    refine ⟨16669699188683548832038463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177810124679291187541743605 16669699188683548832038463)
    ·
      refine ⟨25004548783025323248057695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16669699188683548832038463 25004548783025323248057695)
      ·
        refine ⟨37506823174537984872086543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25004548783025323248057695 37506823174537984872086543)
        ·
          refine ⟨56260234761806977308129815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37506823174537984872086543 56260234761806977308129815)
          ·
            refine ⟨84390352142710465962194723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56260234761806977308129815 84390352142710465962194723)
            ·
              refine ⟨126585528214065698943292085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84390352142710465962194723 126585528214065698943292085)
              ·
                refine ⟨11867393270068659275933633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126585528214065698943292085 11867393270068659275933633)
                ·
                  refine ⟨8900544952551494456950225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11867393270068659275933633 8900544952551494456950225)
                  ·
                    refine ⟨6675408714413620842712669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8900544952551494456950225 6675408714413620842712669)
                    ·
                      refine ⟨2503278267905107816017251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6675408714413620842712669 2503278267905107816017251)
                      ·
                        rfl

theorem cell23_4875117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_4875117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875117 prefixEnd_4875117 := by exact prefixLift 4875117
  have htrace : WordTrace (prefixWord ++ tailWord_4875117) baseStart_4875117 baseEnd_4875117 := by
    simpa [prefixWord, tailWord_4875117, baseEnd_4875117] using wordTrace_append hprefix tailTrace_4875117
  have hstable : (prefixWord ++ tailWord_4875117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875117).length < 2 ^ (prefixWord ++ tailWord_4875117).sum := by decide
  have hdescent : baseEnd_4875117 < baseStart_4875117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875141 : List Nat := [1, 3, 1, 1, 3, 4, 3, 2, 1, 4]
def baseStart_4875141 : Nat := 118140960795 + 4875141 * 2 ^ 59
def prefixEnd_4875141 : Nat := 4983230072969 + 3 ^ 40 * 4875141 * 2
def baseEnd_4875141 : Nat := 834430197146938574039047

theorem tailTrace_4875141 : CollatzResearch.WordTrace tailWord_4875141 prefixEnd_4875141 834430197146938574039047 := by
  unfold tailWord_4875141
  simp only [CollatzResearch.WordTrace]
  refine ⟨177811000031204239640617277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118540666687469493093744851 177811000031204239640617277)
  ·
    refine ⟨66679125011701589865231479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177811000031204239640617277 66679125011701589865231479)
    ·
      refine ⟨100018687517552384797847219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66679125011701589865231479 100018687517552384797847219)
      ·
        refine ⟨150028031276328577196770829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100018687517552384797847219 150028031276328577196770829)
        ·
          refine ⟨56260511728623216448789061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150028031276328577196770829 56260511728623216448789061)
          ·
            refine ⟨10548845949116853084147949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56260511728623216448789061 10548845949116853084147949)
            ·
              refine ⟨3955817230918819906555481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10548845949116853084147949 3955817230918819906555481)
              ·
                refine ⟨2966862923189114929916611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3955817230918819906555481 2966862923189114929916611)
                ·
                  refine ⟨4450294384783672394874917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2966862923189114929916611 4450294384783672394874917)
                  ·
                    refine ⟨834430197146938574039047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4450294384783672394874917 834430197146938574039047)
                    ·
                      rfl

theorem cell23_4875141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 2, 1, 4].length) (baseStart_4875141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875141 prefixEnd_4875141 := by exact prefixLift 4875141
  have htrace : WordTrace (prefixWord ++ tailWord_4875141) baseStart_4875141 baseEnd_4875141 := by
    simpa [prefixWord, tailWord_4875141, baseEnd_4875141] using wordTrace_append hprefix tailTrace_4875141
  have hstable : (prefixWord ++ tailWord_4875141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875141).length < 2 ^ (prefixWord ++ tailWord_4875141).sum := by decide
  have hdescent : baseEnd_4875141 < baseStart_4875141 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875154 : List Nat := [3, 2, 3, 2, 2, 1, 1, 3, 6]
def baseStart_4875154 : Nat := 118140960795 + 4875154 * 2 ^ 59
def prefixEnd_4875154 : Nat := 4983230072969 + 3 ^ 40 * 4875154 * 2
def baseEnd_4875154 : Nat := 278144140743258241250509

theorem tailTrace_4875154 : CollatzResearch.WordTrace tailWord_4875154 prefixEnd_4875154 278144140743258241250509 := by
  unfold tailWord_4875154
  simp only [CollatzResearch.WordTrace]
  refine ⟨44452868545039285715210129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118540982786771428573893677 44452868545039285715210129)
  ·
    refine ⟨33339651408779464286407597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44452868545039285715210129 33339651408779464286407597)
    ·
      refine ⟨12502369278292299107402849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33339651408779464286407597 12502369278292299107402849)
      ·
        refine ⟨9376776958719224330552137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12502369278292299107402849 9376776958719224330552137)
        ·
          refine ⟨7032582719039418247914103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9376776958719224330552137 7032582719039418247914103)
          ·
            refine ⟨10548874078559127371871155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7032582719039418247914103 10548874078559127371871155)
            ·
              refine ⟨15823311117838691057806733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10548874078559127371871155 15823311117838691057806733)
              ·
                refine ⟨5933741669189509146677525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15823311117838691057806733 5933741669189509146677525)
                ·
                  refine ⟨278144140743258241250509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5933741669189509146677525 278144140743258241250509)
                  ·
                    rfl

theorem cell23_4875154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_4875154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875154 prefixEnd_4875154 := by exact prefixLift 4875154
  have htrace : WordTrace (prefixWord ++ tailWord_4875154) baseStart_4875154 baseEnd_4875154 := by
    simpa [prefixWord, tailWord_4875154, baseEnd_4875154] using wordTrace_append hprefix tailTrace_4875154
  have hstable : (prefixWord ++ tailWord_4875154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875154).length < 2 ^ (prefixWord ++ tailWord_4875154).sum := by decide
  have hdescent : baseEnd_4875154 < baseStart_4875154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875167 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 3, 5]
def baseStart_4875167 : Nat := 118140960795 + 4875167 * 2 ^ 59
def prefixEnd_4875167 : Nat := 4983230072969 + 3 ^ 40 * 4875167 * 2
def baseEnd_4875167 : Nat := 834434647312610873464007

theorem tailTrace_4875167 : CollatzResearch.WordTrace tailWord_4875167 prefixEnd_4875167 834434647312610873464007 := by
  unfold tailWord_4875167
  simp only [CollatzResearch.WordTrace]
  refine ⟨177811948329110046081063755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118541298886073364054042503 177811948329110046081063755)
  ·
    refine ⟨266717922493665069121595633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177811948329110046081063755 266717922493665069121595633)
    ·
      refine ⟨200038441870248801841196725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266717922493665069121595633 200038441870248801841196725)
      ·
        refine ⟨18753603925335825172612193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200038441870248801841196725 18753603925335825172612193)
        ·
          refine ⟨14065202944001868879459145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18753603925335825172612193 14065202944001868879459145)
          ·
            refine ⟨10548902208001401659594359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14065202944001868879459145 10548902208001401659594359)
            ·
              refine ⟨15823353312002102489391539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10548902208001401659594359 15823353312002102489391539)
              ·
                refine ⟨23735029968003153734087309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15823353312002102489391539 23735029968003153734087309)
                ·
                  refine ⟨8900636238001182650282741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23735029968003153734087309 8900636238001182650282741)
                  ·
                    refine ⟨834434647312610873464007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8900636238001182650282741 834434647312610873464007)
                    ·
                      rfl

theorem cell23_4875167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_4875167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875167 prefixEnd_4875167 := by exact prefixLift 4875167
  have htrace : WordTrace (prefixWord ++ tailWord_4875167) baseStart_4875167 baseEnd_4875167 := by
    simpa [prefixWord, tailWord_4875167, baseEnd_4875167] using wordTrace_append hprefix tailTrace_4875167
  have hstable : (prefixWord ++ tailWord_4875167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875167).length < 2 ^ (prefixWord ++ tailWord_4875167).sum := by decide
  have hdescent : baseEnd_4875167 < baseStart_4875167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875180 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 1, 6]
def baseStart_4875180 : Nat := 118140960795 + 4875180 * 2 ^ 59
def prefixEnd_4875180 : Nat := 4983230072969 + 3 ^ 40 * 4875180 * 2
def baseEnd_4875180 : Nat := 834436872395447023176487

theorem tailTrace_4875180 : CollatzResearch.WordTrace tailWord_4875180 prefixEnd_4875180 834436872395447023176487 := by
  unfold tailWord_4875180
  simp only [CollatzResearch.WordTrace]
  refine ⟨88906211239031474650643497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118541614985375299534191329 88906211239031474650643497)
  ·
    refine ⟨66679658429273605987982623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88906211239031474650643497 66679658429273605987982623)
    ·
      refine ⟨100019487643910408981973935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66679658429273605987982623 100019487643910408981973935)
      ·
        refine ⟨150029231465865613472960903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100019487643910408981973935 150029231465865613472960903)
        ·
          refine ⟨225043847198798420209441355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150029231465865613472960903 225043847198798420209441355)
          ·
            refine ⟨337565770798197630314162033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225043847198798420209441355 337565770798197630314162033)
            ·
              refine ⟨253174328098648222735621525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337565770798197630314162033 253174328098648222735621525)
              ·
                refine ⟨11867546629624135440732259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 253174328098648222735621525 11867546629624135440732259)
                ·
                  refine ⟨17801319944436203161098389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11867546629624135440732259 17801319944436203161098389)
                  ·
                    refine ⟨834436872395447023176487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17801319944436203161098389 834436872395447023176487)
                    ·
                      rfl

theorem cell23_4875180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_4875180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875180 prefixEnd_4875180 := by exact prefixLift 4875180
  have htrace : WordTrace (prefixWord ++ tailWord_4875180) baseStart_4875180 baseEnd_4875180 := by
    simpa [prefixWord, tailWord_4875180, baseEnd_4875180] using wordTrace_append hprefix tailTrace_4875180
  have hstable : (prefixWord ++ tailWord_4875180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875180).length < 2 ^ (prefixWord ++ tailWord_4875180).sum := by decide
  have hdescent : baseEnd_4875180 < baseStart_4875180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875207 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 3]
def baseStart_4875207 : Nat := 118140960795 + 4875207 * 2 ^ 59
def prefixEnd_4875207 : Nat := 4983230072969 + 3 ^ 40 * 4875207 * 2
def baseEnd_4875207 : Nat := 2503324481164012463891837

theorem tailTrace_4875207 : CollatzResearch.WordTrace tailWord_4875207 prefixEnd_4875207 2503324481164012463891837 := by
  unfold tailWord_4875207
  simp only [CollatzResearch.WordTrace]
  refine ⟨177813407248965132912519875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118542271499310088608346583 177813407248965132912519875)
  ·
    refine ⟨266720110873447699368779813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177813407248965132912519875 266720110873447699368779813)
    ·
      refine ⟨50010020788771443631646215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266720110873447699368779813 50010020788771443631646215)
      ·
        refine ⟨75015031183157165447469323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50010020788771443631646215 75015031183157165447469323)
        ·
          refine ⟨112522546774735748171203985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75015031183157165447469323 112522546774735748171203985)
          ·
            refine ⟨84391910081051811128402989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112522546774735748171203985 84391910081051811128402989)
            ·
              refine ⟨31646966280394429173151121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84391910081051811128402989 31646966280394429173151121)
              ·
                refine ⟨23735224710295821879863341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31646966280394429173151121 23735224710295821879863341)
                ·
                  refine ⟨8900709266360933204948753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23735224710295821879863341 8900709266360933204948753)
                  ·
                    refine ⟨6675531949770699903711565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8900709266360933204948753 6675531949770699903711565)
                    ·
                      refine ⟨2503324481164012463891837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6675531949770699903711565 2503324481164012463891837)
                      ·
                        rfl

theorem cell23_4875207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_4875207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875207 prefixEnd_4875207 := by exact prefixLift 4875207
  have htrace : WordTrace (prefixWord ++ tailWord_4875207) baseStart_4875207 baseEnd_4875207 := by
    simpa [prefixWord, tailWord_4875207, baseEnd_4875207] using wordTrace_append hprefix tailTrace_4875207
  have hstable : (prefixWord ++ tailWord_4875207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875207).length < 2 ^ (prefixWord ++ tailWord_4875207).sum := by decide
  have hdescent : baseEnd_4875207 < baseStart_4875207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875214 : List Nat := [4, 1, 1, 1, 2, 3, 2, 3, 2, 4]
def baseStart_4875214 : Nat := 118140960795 + 4875214 * 2 ^ 59
def prefixEnd_4875214 : Nat := 4983230072969 + 3 ^ 40 * 4875214 * 2
def baseEnd_4875214 : Nat := 834442691842864645501435

theorem tailTrace_4875214 : CollatzResearch.WordTrace tailWord_4875214 prefixEnd_4875214 834442691842864645501435 := by
  unfold tailWord_4875214
  simp only [CollatzResearch.WordTrace]
  refine ⟨22226707819992471638503087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118542441706626515405349797 22226707819992471638503087)
  ·
    refine ⟨33340061729988707457754631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22226707819992471638503087 33340061729988707457754631)
    ·
      refine ⟨50010092594983061186631947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33340061729988707457754631 50010092594983061186631947)
      ·
        refine ⟨75015138892474591779947921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50010092594983061186631947 75015138892474591779947921)
        ·
          refine ⟨56261354169355943834960941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75015138892474591779947921 56261354169355943834960941)
          ·
            refine ⟨21098007813508478938110353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56261354169355943834960941 21098007813508478938110353)
            ·
              refine ⟨15823505860131359203582765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21098007813508478938110353 15823505860131359203582765)
              ·
                refine ⟨5933814697549259701343537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15823505860131359203582765 5933814697549259701343537)
                ·
                  refine ⟨4450361023161944776007653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5933814697549259701343537 4450361023161944776007653)
                  ·
                    refine ⟨834442691842864645501435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4450361023161944776007653 834442691842864645501435)
                    ·
                      rfl

theorem cell23_4875214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_4875214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875214 prefixEnd_4875214 := by exact prefixLift 4875214
  have htrace : WordTrace (prefixWord ++ tailWord_4875214) baseStart_4875214 baseEnd_4875214 := by
    simpa [prefixWord, tailWord_4875214, baseEnd_4875214] using wordTrace_append hprefix tailTrace_4875214
  have hstable : (prefixWord ++ tailWord_4875214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875214).length < 2 ^ (prefixWord ++ tailWord_4875214).sum := by decide
  have hdescent : baseEnd_4875214 < baseStart_4875214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875217 : List Nat := [1, 2, 2, 1, 2, 1, 6, 1, 1, 2, 4]
def baseStart_4875217 : Nat := 118140960795 + 4875217 * 2 ^ 59
def prefixEnd_4875217 : Nat := 4983230072969 + 3 ^ 40 * 4875217 * 2
def baseEnd_4875217 : Nat := 2503329615970557424766791

theorem tailTrace_4875217 : CollatzResearch.WordTrace tailWord_4875217 prefixEnd_4875217 2503329615970557424766791 := by
  unfold tailWord_4875217
  simp only [CollatzResearch.WordTrace]
  refine ⟨177813771978928904620383905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118542514652619269746922603 177813771978928904620383905)
  ·
    refine ⟨133360328984196678465287929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177813771978928904620383905 133360328984196678465287929)
    ·
      refine ⟨100020246738147508848965947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133360328984196678465287929 100020246738147508848965947)
      ·
        refine ⟨150030370107221263273448921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100020246738147508848965947 150030370107221263273448921)
        ·
          refine ⟨112522777580415947455086691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150030370107221263273448921 112522777580415947455086691)
          ·
            refine ⟨168784166370623921182630037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112522777580415947455086691 168784166370623921182630037)
            ·
              refine ⟨7911757798622996305435783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 168784166370623921182630037 7911757798622996305435783)
              ·
                refine ⟨11867636697934494458153675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7911757798622996305435783 11867636697934494458153675)
                ·
                  refine ⟨17801455046901741687230513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11867636697934494458153675 17801455046901741687230513)
                  ·
                    refine ⟨13351091285176306265422885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17801455046901741687230513 13351091285176306265422885)
                    ·
                      refine ⟨2503329615970557424766791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13351091285176306265422885 2503329615970557424766791)
                      ·
                        rfl

theorem cell23_4875217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 6, 1, 1, 2, 4].length) (baseStart_4875217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875217 prefixEnd_4875217 := by exact prefixLift 4875217
  have htrace : WordTrace (prefixWord ++ tailWord_4875217) baseStart_4875217 baseEnd_4875217 := by
    simpa [prefixWord, tailWord_4875217, baseEnd_4875217] using wordTrace_append hprefix tailTrace_4875217
  have hstable : (prefixWord ++ tailWord_4875217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875217).length < 2 ^ (prefixWord ++ tailWord_4875217).sum := by decide
  have hdescent : baseEnd_4875217 < baseStart_4875217 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875297 : List Nat := [1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 5]
def baseStart_4875297 : Nat := 118140960795 + 4875297 * 2 ^ 59
def prefixEnd_4875297 : Nat := 4983230072969 + 3 ^ 40 * 4875297 * 2
def baseEnd_4875297 : Nat := 2503370694422917111766423

theorem tailTrace_4875297 : CollatzResearch.WordTrace tailWord_4875297 prefixEnd_4875297 2503370694422917111766423 := by
  unfold tailWord_4875297
  simp only [CollatzResearch.WordTrace]
  refine ⟨177816689818639078283296145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118544459879092718855530763 177816689818639078283296145)
  ·
    refine ⟨133362517363979308712472109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177816689818639078283296145 133362517363979308712472109)
    ·
      refine ⟨50010944011492240767177041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133362517363979308712472109 50010944011492240767177041)
      ·
        refine ⟨37508208008619180575382781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50010944011492240767177041 37508208008619180575382781)
        ·
          refine ⟨14065578003232192715768543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37508208008619180575382781 14065578003232192715768543)
          ·
            refine ⟨21098367004848289073652815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14065578003232192715768543 21098367004848289073652815)
            ·
              refine ⟨31647550507272433610479223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21098367004848289073652815 31647550507272433610479223)
              ·
                refine ⟨47471325760908650415718835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31647550507272433610479223 47471325760908650415718835)
                ·
                  refine ⟨71206988641362975623578253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47471325760908650415718835 71206988641362975623578253)
                  ·
                    refine ⟨26702620740511115858841845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71206988641362975623578253 26702620740511115858841845)
                    ·
                      refine ⟨2503370694422917111766423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26702620740511115858841845 2503370694422917111766423)
                      ·
                        rfl

theorem cell23_4875297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_4875297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875297 prefixEnd_4875297 := by exact prefixLift 4875297
  have htrace : WordTrace (prefixWord ++ tailWord_4875297) baseStart_4875297 baseEnd_4875297 := by
    simpa [prefixWord, tailWord_4875297, baseEnd_4875297] using wordTrace_append hprefix tailTrace_4875297
  have hstable : (prefixWord ++ tailWord_4875297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875297).length < 2 ^ (prefixWord ++ tailWord_4875297).sum := by decide
  have hdescent : baseEnd_4875297 < baseStart_4875297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875327 : List Nat := [1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 3]
def baseStart_4875327 : Nat := 118140960795 + 4875327 * 2 ^ 59
def prefixEnd_4875327 : Nat := 4983230072969 + 3 ^ 40 * 4875327 * 2
def baseEnd_4875327 : Nat := 2503386098842551994391285

theorem tailTrace_4875327 : CollatzResearch.WordTrace tailWord_4875327 prefixEnd_4875327 2503386098842551994391285 := by
  unfold tailWord_4875327
  simp only [CollatzResearch.WordTrace]
  refine ⟨177817784008530393406888235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118545189339020262271258823 177817784008530393406888235)
  ·
    refine ⟨266726676012795590110332353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177817784008530393406888235 266726676012795590110332353)
    ·
      refine ⟨200045007009596692582749265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266726676012795590110332353 200045007009596692582749265)
      ·
        refine ⟨150033755257197519437061949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200045007009596692582749265 150033755257197519437061949)
        ·
          refine ⟨56262658221449069788898231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150033755257197519437061949 56262658221449069788898231)
          ·
            refine ⟨84393987332173604683347347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56262658221449069788898231 84393987332173604683347347)
            ·
              refine ⟨126590980998260407025021021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84393987332173604683347347 126590980998260407025021021)
              ·
                refine ⟨47471617874347652634382883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126590980998260407025021021 47471617874347652634382883)
                ·
                  refine ⟨71207426811521478951574325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47471617874347652634382883 71207426811521478951574325)
                  ·
                    refine ⟨6675696263580138651710093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71207426811521478951574325 6675696263580138651710093)
                    ·
                      refine ⟨2503386098842551994391285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6675696263580138651710093 2503386098842551994391285)
                      ·
                        rfl

theorem cell23_4875327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 3].length) (baseStart_4875327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875327 prefixEnd_4875327 := by exact prefixLift 4875327
  have htrace : WordTrace (prefixWord ++ tailWord_4875327) baseStart_4875327 baseEnd_4875327 := by
    simpa [prefixWord, tailWord_4875327, baseEnd_4875327] using wordTrace_append hprefix tailTrace_4875327
  have hstable : (prefixWord ++ tailWord_4875327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875327).length < 2 ^ (prefixWord ++ tailWord_4875327).sum := by decide
  have hdescent : baseEnd_4875327 < baseStart_4875327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875347 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 2, 5]
def baseStart_4875347 : Nat := 118140960795 + 4875347 * 2 ^ 59
def prefixEnd_4875347 : Nat := 4983230072969 + 3 ^ 40 * 4875347 * 2
def baseEnd_4875347 : Nat := 834465456151880638713731

theorem tailTrace_4875347 : CollatzResearch.WordTrace tailWord_4875347 prefixEnd_4875347 834465456151880638713731 := by
  unfold tailWord_4875347
  simp only [CollatzResearch.WordTrace]
  refine ⟨177818513468457936822616295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118545675645638624548410863 177818513468457936822616295)
  ·
    refine ⟨266727770202686905233924443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177818513468457936822616295 266727770202686905233924443)
    ·
      refine ⟨400091655304030357850886665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266727770202686905233924443 400091655304030357850886665)
      ·
        refine ⟨300068741478022768388164999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400091655304030357850886665 300068741478022768388164999)
        ·
          refine ⟨450103112217034152582247499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300068741478022768388164999 450103112217034152582247499)
          ·
            refine ⟨675154668325551228873371249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450103112217034152582247499 675154668325551228873371249)
            ·
              refine ⟨506366001244163421655028437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675154668325551228873371249 506366001244163421655028437)
              ·
                refine ⟨11867953154160080195039729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 506366001244163421655028437 11867953154160080195039729)
                ·
                  refine ⟨8900964865620060146279797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11867953154160080195039729 8900964865620060146279797)
                  ·
                    refine ⟨834465456151880638713731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8900964865620060146279797 834465456151880638713731)
                    ·
                      rfl

theorem cell23_4875347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 2, 5].length) (baseStart_4875347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875347 prefixEnd_4875347 := by exact prefixLift 4875347
  have htrace : WordTrace (prefixWord ++ tailWord_4875347) baseStart_4875347 baseEnd_4875347 := by
    simpa [prefixWord, tailWord_4875347, baseEnd_4875347] using wordTrace_append hprefix tailTrace_4875347
  have hstable : (prefixWord ++ tailWord_4875347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875347).length < 2 ^ (prefixWord ++ tailWord_4875347).sum := by decide
  have hdescent : baseEnd_4875347 < baseStart_4875347 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875368 : List Nat := [2, 1, 4, 4, 1, 1, 1, 4, 5]
def baseStart_4875368 : Nat := 118140960795 + 4875368 * 2 ^ 59
def prefixEnd_4875368 : Nat := 4983230072969 + 3 ^ 40 * 4875368 * 2
def baseEnd_4875368 : Nat := 278156350172154037108733

theorem tailTrace_4875368 : CollatzResearch.WordTrace tailWord_4875368 prefixEnd_4875368 278156350172154037108733 := by
  unfold tailWord_4875368
  simp only [CollatzResearch.WordTrace]
  refine ⟨88909639700690928704565379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118546186267587904939420505 88909639700690928704565379)
  ·
    refine ⟨133364459551036393056848069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88909639700690928704565379 133364459551036393056848069)
    ·
      refine ⟨25005836165819323698159013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133364459551036393056848069 25005836165819323698159013)
      ·
        refine ⟨4688594281091123193404815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25005836165819323698159013 4688594281091123193404815)
        ·
          refine ⟨7032891421636684790107223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4688594281091123193404815 7032891421636684790107223)
          ·
            refine ⟨10549337132455027185160835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7032891421636684790107223 10549337132455027185160835)
            ·
              refine ⟨15824005698682540777741253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10549337132455027185160835 15824005698682540777741253)
              ·
                refine ⟨2967001068502976395826485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15824005698682540777741253 2967001068502976395826485)
                ·
                  refine ⟨278156350172154037108733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2967001068502976395826485 278156350172154037108733)
                  ·
                    rfl

theorem cell23_4875368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 5].length) (baseStart_4875368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875368 prefixEnd_4875368 := by exact prefixLift 4875368
  have htrace : WordTrace (prefixWord ++ tailWord_4875368) baseStart_4875368 baseEnd_4875368 := by
    simpa [prefixWord, tailWord_4875368, baseEnd_4875368] using wordTrace_append hprefix tailTrace_4875368
  have hstable : (prefixWord ++ tailWord_4875368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875368).length < 2 ^ (prefixWord ++ tailWord_4875368).sum := by decide
  have hdescent : baseEnd_4875368 < baseStart_4875368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875374 : List Nat := [4, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_4875374 : Nat := 118140960795 + 4875374 * 2 ^ 59
def prefixEnd_4875374 : Nat := 4983230072969 + 3 ^ 40 * 4875374 * 2
def baseEnd_4875374 : Nat := 2503410232433313310503569

theorem tailTrace_4875374 : CollatzResearch.WordTrace tailWord_4875374 prefixEnd_4875374 2503410232433313310503569 := by
  unfold tailWord_4875374
  simp only [CollatzResearch.WordTrace]
  refine ⟨22227437279920015054231147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118546332159573413622566117 22227437279920015054231147)
  ·
    refine ⟨33341155919880022581346721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22227437279920015054231147 33341155919880022581346721)
    ·
      refine ⟨25005866939910016936010041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33341155919880022581346721 25005866939910016936010041)
      ·
        refine ⟨18754400204932512702007531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25005866939910016936010041 18754400204932512702007531)
        ·
          refine ⟨28131600307398769053011297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18754400204932512702007531 28131600307398769053011297)
          ·
            refine ⟨21098700230549076789758473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28131600307398769053011297 21098700230549076789758473)
            ·
              refine ⟨15824025172911807592318855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21098700230549076789758473 15824025172911807592318855)
              ·
                refine ⟨23736037759367711388478283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15824025172911807592318855 23736037759367711388478283)
                ·
                  refine ⟨35604056639051567082717425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23736037759367711388478283 35604056639051567082717425)
                  ·
                    refine ⟨26703042479288675312038069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35604056639051567082717425 26703042479288675312038069)
                    ·
                      refine ⟨2503410232433313310503569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26703042479288675312038069 2503410232433313310503569)
                      ·
                        rfl

theorem cell23_4875374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_4875374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875374 prefixEnd_4875374 := by exact prefixLift 4875374
  have htrace : WordTrace (prefixWord ++ tailWord_4875374) baseStart_4875374 baseEnd_4875374 := by
    simpa [prefixWord, tailWord_4875374, baseEnd_4875374] using wordTrace_append hprefix tailTrace_4875374
  have hstable : (prefixWord ++ tailWord_4875374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875374).length < 2 ^ (prefixWord ++ tailWord_4875374).sum := by decide
  have hdescent : baseEnd_4875374 < baseStart_4875374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875384 : List Nat := [2, 1, 2, 1, 1, 1, 5, 1, 1, 6, 2]
def baseStart_4875384 : Nat := 118140960795 + 4875384 * 2 ^ 59
def prefixEnd_4875384 : Nat := 4983230072969 + 3 ^ 40 * 4875384 * 2
def baseEnd_4875384 : Nat := 2503415367239858271378523

theorem tailTrace_4875384 : CollatzResearch.WordTrace tailWord_4875384 prefixEnd_4875384 2503415367239858271378523 := by
  unfold tailWord_4875384
  simp only [CollatzResearch.WordTrace]
  refine ⟨88909931484661946070856603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118546575312882594761142137 88909931484661946070856603)
  ·
    refine ⟨133364897226992919106284905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88909931484661946070856603 133364897226992919106284905)
    ·
      refine ⟨100023672920244689329713679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133364897226992919106284905 100023672920244689329713679)
      ·
        refine ⟨150035509380367033994570519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100023672920244689329713679 150035509380367033994570519)
        ·
          refine ⟨225053264070550550991855779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150035509380367033994570519 225053264070550550991855779)
          ·
            refine ⟨337579896105825826487783669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225053264070550550991855779 337579896105825826487783669)
            ·
              refine ⟨31648115259921171233229719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 337579896105825826487783669 31648115259921171233229719)
              ·
                refine ⟨47472172889881756849844579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31648115259921171233229719 47472172889881756849844579)
                ·
                  refine ⟨71208259334822635274766869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47472172889881756849844579 71208259334822635274766869)
                  ·
                    refine ⟨3337887156319811028504697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71208259334822635274766869 3337887156319811028504697)
                    ·
                      refine ⟨2503415367239858271378523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337887156319811028504697 2503415367239858271378523)
                      ·
                        rfl

theorem cell23_4875384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 1, 1, 6, 2].length) (baseStart_4875384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875384 prefixEnd_4875384 := by exact prefixLift 4875384
  have htrace : WordTrace (prefixWord ++ tailWord_4875384) baseStart_4875384 baseEnd_4875384 := by
    simpa [prefixWord, tailWord_4875384, baseEnd_4875384] using wordTrace_append hprefix tailTrace_4875384
  have hstable : (prefixWord ++ tailWord_4875384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875384).length < 2 ^ (prefixWord ++ tailWord_4875384).sum := by decide
  have hdescent : baseEnd_4875384 < baseStart_4875384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875401 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 2, 1, 4]
def baseStart_4875401 : Nat := 118140960795 + 4875401 * 2 ^ 59
def prefixEnd_4875401 : Nat := 4983230072969 + 3 ^ 40 * 4875401 * 2
def baseEnd_4875401 : Nat := 2503424096410984704865945

theorem tailTrace_4875401 : CollatzResearch.WordTrace tailWord_4875401 prefixEnd_4875401 2503424096410984704865945 := by
  unfold tailWord_4875401
  simp only [CollatzResearch.WordTrace]
  refine ⟨177820483010262304045082057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118546988673508202696721371 177820483010262304045082057)
  ·
    refine ⟨133365362257696728033811543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177820483010262304045082057 133365362257696728033811543)
    ·
      refine ⟨200048043386545092050717315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133365362257696728033811543 200048043386545092050717315)
      ·
        refine ⟨300072065079817638076075973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200048043386545092050717315 300072065079817638076075973)
        ·
          refine ⟨56263512202465807139264245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 300072065079817638076075973 56263512202465807139264245)
          ·
            refine ⟨5274704268981169419306023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56263512202465807139264245 5274704268981169419306023)
            ·
              refine ⟨7912056403471754128959035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274704268981169419306023 7912056403471754128959035)
              ·
                refine ⟨11868084605207631193438553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7912056403471754128959035 11868084605207631193438553)
                ·
                  refine ⟨8901063453905723395078915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11868084605207631193438553 8901063453905723395078915)
                  ·
                    refine ⟨13351595180858585092618373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8901063453905723395078915 13351595180858585092618373)
                    ·
                      refine ⟨2503424096410984704865945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13351595180858585092618373 2503424096410984704865945)
                      ·
                        rfl

theorem cell23_4875401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 2, 1, 4].length) (baseStart_4875401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875401 prefixEnd_4875401 := by exact prefixLift 4875401
  have htrace : WordTrace (prefixWord ++ tailWord_4875401) baseStart_4875401 baseEnd_4875401 := by
    simpa [prefixWord, tailWord_4875401, baseEnd_4875401] using wordTrace_append hprefix tailTrace_4875401
  have hstable : (prefixWord ++ tailWord_4875401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875401).length < 2 ^ (prefixWord ++ tailWord_4875401).sum := by decide
  have hdescent : baseEnd_4875401 < baseStart_4875401 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875411 : List Nat := [1, 1, 1, 2, 1, 2, 5, 5, 1, 4]
def baseStart_4875411 : Nat := 118140960795 + 4875411 * 2 ^ 59
def prefixEnd_4875411 : Nat := 4983230072969 + 3 ^ 40 * 4875411 * 2
def baseEnd_4875411 : Nat := 834476410405843221913633

theorem tailTrace_4875411 : CollatzResearch.WordTrace tailWord_4875411 prefixEnd_4875411 834476410405843221913633 := by
  unfold tailWord_4875411
  simp only [CollatzResearch.WordTrace]
  refine ⟨177820847740226075752946087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118547231826817383835297391 177820847740226075752946087)
  ·
    refine ⟨266731271610339113629419131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177820847740226075752946087 266731271610339113629419131)
    ·
      refine ⟨400096907415508670444128697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266731271610339113629419131 400096907415508670444128697)
      ·
        refine ⟨300072680561631502833096523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400096907415508670444128697 300072680561631502833096523)
        ·
          refine ⟨450109020842447254249644785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300072680561631502833096523 450109020842447254249644785)
          ·
            refine ⟨337581765631835440687233589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450109020842447254249644785 337581765631835440687233589)
            ·
              refine ⟨31648290527984572564428149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 337581765631835440687233589 31648290527984572564428149)
              ·
                refine ⟨2967027236998553677915139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31648290527984572564428149 2967027236998553677915139)
                ·
                  refine ⟨4450540855497830516872709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967027236998553677915139 4450540855497830516872709)
                  ·
                    refine ⟨834476410405843221913633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4450540855497830516872709 834476410405843221913633)
                    ·
                      rfl

theorem cell23_4875411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 5, 1, 4].length) (baseStart_4875411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875411 prefixEnd_4875411 := by exact prefixLift 4875411
  have htrace : WordTrace (prefixWord ++ tailWord_4875411) baseStart_4875411 baseEnd_4875411 := by
    simpa [prefixWord, tailWord_4875411, baseEnd_4875411] using wordTrace_append hprefix tailTrace_4875411
  have hstable : (prefixWord ++ tailWord_4875411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875411).length < 2 ^ (prefixWord ++ tailWord_4875411).sum := by decide
  have hdescent : baseEnd_4875411 < baseStart_4875411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875428 : List Nat := [2, 3, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_4875428 : Nat := 118140960795 + 4875428 * 2 ^ 59
def prefixEnd_4875428 : Nat := 4983230072969 + 3 ^ 40 * 4875428 * 2
def baseEnd_4875428 : Nat := 834479320129552033076107

theorem tailTrace_4875428 : CollatzResearch.WordTrace tailWord_4875428 prefixEnd_4875428 834479320129552033076107 := by
  unfold tailWord_4875428
  simp only [CollatzResearch.WordTrace]
  refine ⟨88910733890582243828157469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118547645187442991770876625 88910733890582243828157469)
  ·
    refine ⟨33341525208968341435559051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88910733890582243828157469 33341525208968341435559051)
    ·
      refine ⟨50012287813452512153338577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33341525208968341435559051 50012287813452512153338577)
      ·
        refine ⟨37509215860089384115003933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50012287813452512153338577 37509215860089384115003933)
        ·
          refine ⟨14065955947533519043126475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37509215860089384115003933 14065955947533519043126475)
          ·
            refine ⟨21098933921300278564689713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14065955947533519043126475 21098933921300278564689713)
            ·
              refine ⟨15824200440975208923517285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21098933921300278564689713 15824200440975208923517285)
              ·
                refine ⟨2967037582682851673159491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15824200440975208923517285 2967037582682851673159491)
                ·
                  refine ⟨4450556374024277509739237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967037582682851673159491 4450556374024277509739237)
                  ·
                    refine ⟨834479320129552033076107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4450556374024277509739237 834479320129552033076107)
                    ·
                      rfl

theorem cell23_4875428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_4875428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875428 prefixEnd_4875428 := by exact prefixLift 4875428
  have htrace : WordTrace (prefixWord ++ tailWord_4875428) baseStart_4875428 baseEnd_4875428 := by
    simpa [prefixWord, tailWord_4875428, baseEnd_4875428] using wordTrace_append hprefix tailTrace_4875428
  have hstable : (prefixWord ++ tailWord_4875428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875428).length < 2 ^ (prefixWord ++ tailWord_4875428).sum := by decide
  have hdescent : baseEnd_4875428 < baseStart_4875428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875461 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 2, 3, 2]
def baseStart_4875461 : Nat := 118140960795 + 4875461 * 2 ^ 59
def prefixEnd_4875461 : Nat := 4983230072969 + 3 ^ 40 * 4875461 * 2
def baseEnd_4875461 : Nat := 2503454905250254470115669

theorem tailTrace_4875461 : CollatzResearch.WordTrace tailWord_4875461 prefixEnd_4875461 2503454905250254470115669 := by
  unfold tailWord_4875461
  simp only [CollatzResearch.WordTrace]
  refine ⟨177822671390044934292266237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118548447593363289528177491 177822671390044934292266237)
  ·
    refine ⟨66683501771266850359599839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177822671390044934292266237 66683501771266850359599839)
    ·
      refine ⟨100025252656900275539399759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66683501771266850359599839 100025252656900275539399759)
      ·
        refine ⟨150037878985350413309099639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100025252656900275539399759 150037878985350413309099639)
        ·
          refine ⟨225056818478025619963649459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150037878985350413309099639 225056818478025619963649459)
          ·
            refine ⟨337585227717038429945474189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225056818478025619963649459 337585227717038429945474189)
            ·
              refine ⟨126594460393889411229552821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337585227717038429945474189 126594460393889411229552821)
              ·
                refine ⟨11868230661927132302770577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126594460393889411229552821 11868230661927132302770577)
                ·
                  refine ⟨8901172996445349227077933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11868230661927132302770577 8901172996445349227077933)
                  ·
                    refine ⟨3337939873667005960154225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8901172996445349227077933 3337939873667005960154225)
                    ·
                      refine ⟨2503454905250254470115669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337939873667005960154225 2503454905250254470115669)
                      ·
                        rfl

theorem cell23_4875461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 2, 3, 2].length) (baseStart_4875461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875461 prefixEnd_4875461 := by exact prefixLift 4875461
  have htrace : WordTrace (prefixWord ++ tailWord_4875461) baseStart_4875461 baseEnd_4875461 := by
    simpa [prefixWord, tailWord_4875461, baseEnd_4875461] using wordTrace_append hprefix tailTrace_4875461
  have hstable : (prefixWord ++ tailWord_4875461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875461).length < 2 ^ (prefixWord ++ tailWord_4875461).sum := by decide
  have hdescent : baseEnd_4875461 < baseStart_4875461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875521 : List Nat := [1, 2, 4, 1, 1, 4, 1, 2, 1, 2, 4]
def baseStart_4875521 : Nat := 118140960795 + 4875521 * 2 ^ 59
def prefixEnd_4875521 : Nat := 4983230072969 + 3 ^ 40 * 4875521 * 2
def baseEnd_4875521 : Nat := 2503485714089524235365393

theorem tailTrace_4875521 : CollatzResearch.WordTrace tailWord_4875521 prefixEnd_4875521 2503485714089524235365393 := by
  unfold tailWord_4875521
  simp only [CollatzResearch.WordTrace]
  refine ⟨177824859769827564539450417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118549906513218376359633611 177824859769827564539450417)
  ·
    refine ⟨133368644827370673404587813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177824859769827564539450417 133368644827370673404587813)
    ·
      refine ⟨25006620905132001263360215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133368644827370673404587813 25006620905132001263360215)
      ·
        refine ⟨37509931357698001895040323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25006620905132001263360215 37509931357698001895040323)
        ·
          refine ⟨56264897036547002842560485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37509931357698001895040323 56264897036547002842560485)
          ·
            refine ⟨10549668194352563032980091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56264897036547002842560485 10549668194352563032980091)
            ·
              refine ⟨15824502291528844549470137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10549668194352563032980091 15824502291528844549470137)
              ·
                refine ⟨11868376718646633412102603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15824502291528844549470137 11868376718646633412102603)
                ·
                  refine ⟨17802565077969950118153905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11868376718646633412102603 17802565077969950118153905)
                  ·
                    refine ⟨13351923808477462588615429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17802565077969950118153905 13351923808477462588615429)
                    ·
                      refine ⟨2503485714089524235365393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13351923808477462588615429 2503485714089524235365393)
                      ·
                        rfl

theorem cell23_4875521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 2, 1, 2, 4].length) (baseStart_4875521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875521 prefixEnd_4875521 := by exact prefixLift 4875521
  have htrace : WordTrace (prefixWord ++ tailWord_4875521) baseStart_4875521 baseEnd_4875521 := by
    simpa [prefixWord, tailWord_4875521, baseEnd_4875521] using wordTrace_append hprefix tailTrace_4875521
  have hstable : (prefixWord ++ tailWord_4875521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875521).length < 2 ^ (prefixWord ++ tailWord_4875521).sum := by decide
  have hdescent : baseEnd_4875521 < baseStart_4875521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875525 : List Nat := [1, 3, 1, 1, 2, 1, 4, 5, 1, 2, 2]
def baseStart_4875525 : Nat := 118140960795 + 4875525 * 2 ^ 59
def prefixEnd_4875525 : Nat := 4983230072969 + 3 ^ 40 * 4875525 * 2
def baseEnd_4875525 : Nat := 2503487768012142219715375

theorem tailTrace_4875525 : CollatzResearch.WordTrace tailWord_4875525 prefixEnd_4875525 2503487768012142219715375 := by
  unfold tailWord_4875525
  simp only [CollatzResearch.WordTrace]
  refine ⟨177825005661813073222596029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118550003774542048815064019 177825005661813073222596029)
  ·
    refine ⟨66684377123179902458473511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177825005661813073222596029 66684377123179902458473511)
    ·
      refine ⟨100026565684769853687710267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66684377123179902458473511 100026565684769853687710267)
      ·
        refine ⟨150039848527154780531565401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100026565684769853687710267 150039848527154780531565401)
        ·
          refine ⟨112529886395366085398674051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150039848527154780531565401 112529886395366085398674051)
          ·
            refine ⟨168794829593049128098011077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112529886395366085398674051 168794829593049128098011077)
            ·
              refine ⟨31649030548696711518377077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168794829593049128098011077 31649030548696711518377077)
              ·
                refine ⟨2967096613940316704847851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31649030548696711518377077 2967096613940316704847851)
                ·
                  refine ⟨4450644920910475057271777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967096613940316704847851 4450644920910475057271777)
                  ·
                    refine ⟨3337983690682856292953833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4450644920910475057271777 3337983690682856292953833)
                    ·
                      refine ⟨2503487768012142219715375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3337983690682856292953833 2503487768012142219715375)
                      ·
                        rfl

theorem cell23_4875525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 5, 1, 2, 2].length) (baseStart_4875525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875525 prefixEnd_4875525 := by exact prefixLift 4875525
  have htrace : WordTrace (prefixWord ++ tailWord_4875525) baseStart_4875525 baseEnd_4875525 := by
    simpa [prefixWord, tailWord_4875525, baseEnd_4875525] using wordTrace_append hprefix tailTrace_4875525
  have hstable : (prefixWord ++ tailWord_4875525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875525).length < 2 ^ (prefixWord ++ tailWord_4875525).sum := by decide
  have hdescent : baseEnd_4875525 < baseStart_4875525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875528 : List Nat := [2, 1, 3, 2, 4, 2, 1, 1, 1, 1, 5]
def baseStart_4875528 : Nat := 118140960795 + 4875528 * 2 ^ 59
def prefixEnd_4875528 : Nat := 4983230072969 + 3 ^ 40 * 4875528 * 2
def baseEnd_4875528 : Nat := 2503489308454105707977861

theorem tailTrace_4875528 : CollatzResearch.WordTrace tailWord_4875528 prefixEnd_4875528 2503489308454105707977861 := by
  unfold tailWord_4875528
  simp only [CollatzResearch.WordTrace]
  refine ⟨88912557540401102367477619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118550076720534803156636825 88912557540401102367477619)
  ·
    refine ⟨133368836310601653551216429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88912557540401102367477619 133368836310601653551216429)
    ·
      refine ⟨50013313616475620081706161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133368836310601653551216429 50013313616475620081706161)
      ·
        refine ⟨37509985212356715061279621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50013313616475620081706161 37509985212356715061279621)
        ·
          refine ⟨7033122227316884073989929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37509985212356715061279621 7033122227316884073989929)
          ·
            refine ⟨5274841670487663055492447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7033122227316884073989929 5274841670487663055492447)
            ·
              refine ⟨7912262505731494583238671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274841670487663055492447 7912262505731494583238671)
              ·
                refine ⟨11868393758597241874858007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7912262505731494583238671 11868393758597241874858007)
                ·
                  refine ⟨17802590637895862812287011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11868393758597241874858007 17802590637895862812287011)
                  ·
                    refine ⟨26703885956843794218430517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17802590637895862812287011 26703885956843794218430517)
                    ·
                      refine ⟨2503489308454105707977861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26703885956843794218430517 2503489308454105707977861)
                      ·
                        rfl

theorem cell23_4875528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_4875528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875528 prefixEnd_4875528 := by exact prefixLift 4875528
  have htrace : WordTrace (prefixWord ++ tailWord_4875528) baseStart_4875528 baseEnd_4875528 := by
    simpa [prefixWord, tailWord_4875528, baseEnd_4875528] using wordTrace_append hprefix tailTrace_4875528
  have hstable : (prefixWord ++ tailWord_4875528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875528).length < 2 ^ (prefixWord ++ tailWord_4875528).sum := by decide
  have hdescent : baseEnd_4875528 < baseStart_4875528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875544 : List Nat := [2, 1, 2, 3, 1, 3, 1, 1, 2, 7]
def baseStart_4875544 : Nat := 118140960795 + 4875544 * 2 ^ 59
def prefixEnd_4875544 : Nat := 4983230072969 + 3 ^ 40 * 4875544 * 2
def baseEnd_4875544 : Nat := 834499174714859215125929

theorem tailTrace_4875544 : CollatzResearch.WordTrace tailWord_4875544 prefixEnd_4875544 834499174714859215125929 := by
  unfold tailWord_4875544
  simp only [CollatzResearch.WordTrace]
  refine ⟨88912849324372119733768843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118550465765829492978358457 88912849324372119733768843)
  ·
    refine ⟨133369273986558179600653265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88912849324372119733768843 133369273986558179600653265)
    ·
      refine ⟨100026955489918634700489949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133369273986558179600653265 100026955489918634700489949)
      ·
        refine ⟨37510108308719488012683731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100026955489918634700489949 37510108308719488012683731)
        ·
          refine ⟨56265162463079232019025597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37510108308719488012683731 56265162463079232019025597)
          ·
            refine ⟨21099435923654712007134599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56265162463079232019025597 21099435923654712007134599)
            ·
              refine ⟨31649153885482068010701899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21099435923654712007134599 31649153885482068010701899)
              ·
                refine ⟨47473730828223102016052849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31649153885482068010701899 47473730828223102016052849)
                ·
                  refine ⟨35605298121167326512039637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47473730828223102016052849 35605298121167326512039637)
                  ·
                    refine ⟨834499174714859215125929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35605298121167326512039637 834499174714859215125929)
                    ·
                      rfl

theorem cell23_4875544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 2, 7].length) (baseStart_4875544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875544 prefixEnd_4875544 := by exact prefixLift 4875544
  have htrace : WordTrace (prefixWord ++ tailWord_4875544) baseStart_4875544 baseEnd_4875544 := by
    simpa [prefixWord, tailWord_4875544, baseEnd_4875544] using wordTrace_append hprefix tailTrace_4875544
  have hstable : (prefixWord ++ tailWord_4875544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875544).length < 2 ^ (prefixWord ++ tailWord_4875544).sum := by decide
  have hdescent : baseEnd_4875544 < baseStart_4875544 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875564 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_4875564 : Nat := 118140960795 + 4875564 * 2 ^ 59
def prefixEnd_4875564 : Nat := 4983230072969 + 3 ^ 40 * 4875564 * 2
def baseEnd_4875564 : Nat := 2503507793757667567127695

theorem tailTrace_4875564 : CollatzResearch.WordTrace tailWord_4875564 prefixEnd_4875564 2503507793757667567127695 := by
  unfold tailWord_4875564
  simp only [CollatzResearch.WordTrace]
  refine ⟨88913214054335891441632873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118550952072447855255510497 88913214054335891441632873)
  ·
    refine ⟨66684910540751918581224655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88913214054335891441632873 66684910540751918581224655)
    ·
      refine ⟨100027365811127877871836983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66684910540751918581224655 100027365811127877871836983)
      ·
        refine ⟨150041048716691816807755475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100027365811127877871836983 150041048716691816807755475)
        ·
          refine ⟨225061573075037725211633213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150041048716691816807755475 225061573075037725211633213)
          ·
            refine ⟨84398089903139146954362455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 225061573075037725211633213 84398089903139146954362455)
            ·
              refine ⟨126597134854708720431543683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84398089903139146954362455 126597134854708720431543683)
              ·
                refine ⟨189895702282063080647315525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126597134854708720431543683 189895702282063080647315525)
                ·
                  refine ⟨35605444177886827621371661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 189895702282063080647315525 35605444177886827621371661)
                  ·
                    refine ⟨13352041566707560358014373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35605444177886827621371661 13352041566707560358014373)
                    ·
                      refine ⟨2503507793757667567127695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13352041566707560358014373 2503507793757667567127695)
                      ·
                        rfl

theorem cell23_4875564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_4875564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875564 prefixEnd_4875564 := by exact prefixLift 4875564
  have htrace : WordTrace (prefixWord ++ tailWord_4875564) baseStart_4875564 baseEnd_4875564 := by
    simpa [prefixWord, tailWord_4875564, baseEnd_4875564] using wordTrace_append hprefix tailTrace_4875564
  have hstable : (prefixWord ++ tailWord_4875564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875564).length < 2 ^ (prefixWord ++ tailWord_4875564).sum := by decide
  have hdescent : baseEnd_4875564 < baseStart_4875564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875568 : List Nat := [2, 1, 1, 1, 2, 2, 4, 4, 1, 3, 2]
def baseStart_4875568 : Nat := 118140960795 + 4875568 * 2 ^ 59
def prefixEnd_4875568 : Nat := 4983230072969 + 3 ^ 40 * 4875568 * 2
def baseEnd_4875568 : Nat := 2503509847680285551477677

theorem tailTrace_4875568 : CollatzResearch.WordTrace tailWord_4875568 prefixEnd_4875568 2503509847680285551477677 := by
  unfold tailWord_4875568
  simp only [CollatzResearch.WordTrace]
  refine ⟨88913287000328645783205679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118551049333771527710940905 88913287000328645783205679)
  ·
    refine ⟨133369930500492968674808519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88913287000328645783205679 133369930500492968674808519)
    ·
      refine ⟨200054895750739453012212779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133369930500492968674808519 200054895750739453012212779)
      ·
        refine ⟨300082343626109179518319169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200054895750739453012212779 300082343626109179518319169)
        ·
          refine ⟨225061757719581884638739377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300082343626109179518319169 225061757719581884638739377)
          ·
            refine ⟨168796318289686413479054533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225061757719581884638739377 168796318289686413479054533)
            ·
              refine ⟨31649309679316202527322725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168796318289686413479054533 31649309679316202527322725)
              ·
                refine ⟨5934245564871787973873011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31649309679316202527322725 5934245564871787973873011)
                ·
                  refine ⟨8901368347307681960809517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5934245564871787973873011 8901368347307681960809517)
                  ·
                    refine ⟨3338013130240380735303569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8901368347307681960809517 3338013130240380735303569)
                    ·
                      refine ⟨2503509847680285551477677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3338013130240380735303569 2503509847680285551477677)
                      ·
                        rfl

theorem cell23_4875568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 4, 1, 3, 2].length) (baseStart_4875568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875568 prefixEnd_4875568 := by exact prefixLift 4875568
  have htrace : WordTrace (prefixWord ++ tailWord_4875568) baseStart_4875568 baseEnd_4875568 := by
    simpa [prefixWord, tailWord_4875568, baseEnd_4875568] using wordTrace_append hprefix tailTrace_4875568
  have hstable : (prefixWord ++ tailWord_4875568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875568).length < 2 ^ (prefixWord ++ tailWord_4875568).sum := by decide
  have hdescent : baseEnd_4875568 < baseStart_4875568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875584 : List Nat := [2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 5]
def baseStart_4875584 : Nat := 118140960795 + 4875584 * 2 ^ 59
def prefixEnd_4875584 : Nat := 4983230072969 + 3 ^ 40 * 4875584 * 2
def baseEnd_4875584 : Nat := 2503518063370757488877603

theorem tailTrace_4875584 : CollatzResearch.WordTrace tailWord_4875584 prefixEnd_4875584 2503518063370757488877603 := by
  unfold tailWord_4875584
  simp only [CollatzResearch.WordTrace]
  refine ⟨88913578784299663149496903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118551438379066217532662537 88913578784299663149496903)
  ·
    refine ⟨133370368176449494724245355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88913578784299663149496903 133370368176449494724245355)
    ·
      refine ⟨200055552264674242086368033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133370368176449494724245355 200055552264674242086368033)
      ·
        refine ⟨150041664198505681564776025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200055552264674242086368033 150041664198505681564776025)
        ·
          refine ⟨112531248148879261173582019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150041664198505681564776025 112531248148879261173582019)
          ·
            refine ⟨168796872223318891760373029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112531248148879261173582019 168796872223318891760373029)
            ·
              refine ⟨31649413541872292205069943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168796872223318891760373029 31649413541872292205069943)
              ·
                refine ⟨47474120312808438307604915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31649413541872292205069943 47474120312808438307604915)
                ·
                  refine ⟨71211180469212657461407373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47474120312808438307604915 71211180469212657461407373)
                  ·
                    refine ⟨26704192675954746548027765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71211180469212657461407373 26704192675954746548027765)
                    ·
                      refine ⟨2503518063370757488877603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26704192675954746548027765 2503518063370757488877603)
                      ·
                        rfl

theorem cell23_4875584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 5].length) (baseStart_4875584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875584 prefixEnd_4875584 := by exact prefixLift 4875584
  have htrace : WordTrace (prefixWord ++ tailWord_4875584) baseStart_4875584 baseEnd_4875584 := by
    simpa [prefixWord, tailWord_4875584, baseEnd_4875584] using wordTrace_append hprefix tailTrace_4875584
  have hstable : (prefixWord ++ tailWord_4875584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875584).length < 2 ^ (prefixWord ++ tailWord_4875584).sum := by decide
  have hdescent : baseEnd_4875584 < baseStart_4875584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875606 : List Nat := [5, 2, 3, 1, 2, 1, 1, 1, 1, 2, 4]
def baseStart_4875606 : Nat := 118140960795 + 4875606 * 2 ^ 59
def prefixEnd_4875606 : Nat := 4983230072969 + 3 ^ 40 * 4875606 * 2
def baseEnd_4875606 : Nat := 2503529359945156402802503

theorem tailTrace_4875606 : CollatzResearch.WordTrace tailWord_4875606 prefixEnd_4875606 2503529359945156402802503 := by
  unfold tailWord_4875606
  simp only [CollatzResearch.WordTrace]
  refine ⟨11114247498407476503518417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118551973316346416037529781 11114247498407476503518417)
  ·
    refine ⟨8335685623805607377638813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11114247498407476503518417 8335685623805607377638813)
    ·
      refine ⟨3125882108927102766614555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8335685623805607377638813 3125882108927102766614555)
      ·
        refine ⟨4688823163390654149921833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3125882108927102766614555 4688823163390654149921833)
        ·
          refine ⟨3516617372542990612441375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4688823163390654149921833 3516617372542990612441375)
          ·
            refine ⟨5274926058814485918662063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3516617372542990612441375 5274926058814485918662063)
            ·
              refine ⟨7912389088221728877993095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5274926058814485918662063 7912389088221728877993095)
              ·
                refine ⟨11868583632332593316989643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7912389088221728877993095 11868583632332593316989643)
                ·
                  refine ⟨17802875448498889975484465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11868583632332593316989643 17802875448498889975484465)
                  ·
                    refine ⟨13352156586374167481613349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17802875448498889975484465 13352156586374167481613349)
                    ·
                      refine ⟨2503529359945156402802503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13352156586374167481613349 2503529359945156402802503)
                      ·
                        rfl

theorem cell23_4875606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_4875606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875606 prefixEnd_4875606 := by exact prefixLift 4875606
  have htrace : WordTrace (prefixWord ++ tailWord_4875606) baseStart_4875606 baseEnd_4875606 := by
    simpa [prefixWord, tailWord_4875606, baseEnd_4875606] using wordTrace_append hprefix tailTrace_4875606
  have hstable : (prefixWord ++ tailWord_4875606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875606).length < 2 ^ (prefixWord ++ tailWord_4875606).sum := by decide
  have hdescent : baseEnd_4875606 < baseStart_4875606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875651 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 4, 5]
def baseStart_4875651 : Nat := 118140960795 + 4875651 * 2 ^ 59
def prefixEnd_4875651 : Nat := 4983230072969 + 3 ^ 40 * 4875651 * 2
def baseEnd_4875651 : Nat := 834517488858202908913265

theorem tailTrace_4875651 : CollatzResearch.WordTrace tailWord_4875651 prefixEnd_4875651 834517488858202908913265 := by
  unfold tailWord_4875651
  simp only [CollatzResearch.WordTrace]
  refine ⟨177829601259356596741682807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118553067506237731161121871 177829601259356596741682807)
  ·
    refine ⟨266744401889034895112524211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177829601259356596741682807 266744401889034895112524211)
    ·
      refine ⟨400116602833552342668786317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266744401889034895112524211 400116602833552342668786317)
      ·
        refine ⟨150043726062582128500794869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 400116602833552342668786317 150043726062582128500794869)
        ·
          refine ⟨14066599318367074546949519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150043726062582128500794869 14066599318367074546949519)
          ·
            refine ⟨21099898977550611820424279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14066599318367074546949519 21099898977550611820424279)
            ·
              refine ⟨31649848466325917730636419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21099898977550611820424279 31649848466325917730636419)
              ·
                refine ⟨47474772699488876595954629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31649848466325917730636419 47474772699488876595954629)
                ·
                  refine ⟨8901519881154164361741493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47474772699488876595954629 8901519881154164361741493)
                  ·
                    refine ⟨834517488858202908913265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8901519881154164361741493 834517488858202908913265)
                    ·
                      rfl

theorem cell23_4875651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 4, 5].length) (baseStart_4875651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875651 prefixEnd_4875651 := by exact prefixLift 4875651
  have htrace : WordTrace (prefixWord ++ tailWord_4875651) baseStart_4875651 baseEnd_4875651 := by
    simpa [prefixWord, tailWord_4875651, baseEnd_4875651] using wordTrace_append hprefix tailTrace_4875651
  have hstable : (prefixWord ++ tailWord_4875651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875651).length < 2 ^ (prefixWord ++ tailWord_4875651).sum := by decide
  have hdescent : baseEnd_4875651 < baseStart_4875651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875655 : List Nat := [1, 1, 4, 2, 2, 3, 3, 2, 5]
def baseStart_4875655 : Nat := 118140960795 + 4875655 * 2 ^ 59
def prefixEnd_4875655 : Nat := 4983230072969 + 3 ^ 40 * 4875655 * 2
def baseEnd_4875655 : Nat := 278172724499691856787753

theorem tailTrace_4875655 : CollatzResearch.WordTrace tailWord_4875655 prefixEnd_4875655 278172724499691856787753 := by
  unfold tailWord_4875655
  simp only [CollatzResearch.WordTrace]
  refine ⟨177829747151342105424828419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118553164767561403616552279 177829747151342105424828419)
  ·
    refine ⟨266744620727013158137242629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177829747151342105424828419 266744620727013158137242629)
    ·
      refine ⟨50014616386314967150732993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266744620727013158137242629 50014616386314967150732993)
      ·
        refine ⟨37510962289736225363049745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50014616386314967150732993 37510962289736225363049745)
        ·
          refine ⟨28133221717302169022287309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37510962289736225363049745 28133221717302169022287309)
          ·
            refine ⟨10549958143988313383357741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28133221717302169022287309 10549958143988313383357741)
            ·
              refine ⟨3956234303995617518759153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10549958143988313383357741 3956234303995617518759153)
              ·
                refine ⟨2967175727996713139069365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3956234303995617518759153 2967175727996713139069365)
                ·
                  refine ⟨278172724499691856787753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2967175727996713139069365 278172724499691856787753)
                  ·
                    rfl

theorem cell23_4875655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 5].length) (baseStart_4875655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875655 prefixEnd_4875655 := by exact prefixLift 4875655
  have htrace : WordTrace (prefixWord ++ tailWord_4875655) baseStart_4875655 baseEnd_4875655 := by
    simpa [prefixWord, tailWord_4875655, baseEnd_4875655] using wordTrace_append hprefix tailTrace_4875655
  have hstable : (prefixWord ++ tailWord_4875655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875655).length < 2 ^ (prefixWord ++ tailWord_4875655).sum := by decide
  have hdescent : baseEnd_4875655 < baseStart_4875655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875671 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 4]
def baseStart_4875671 : Nat := 118140960795 + 4875671 * 2 ^ 59
def prefixEnd_4875671 : Nat := 4983230072969 + 3 ^ 40 * 4875671 * 2
def baseEnd_4875671 : Nat := 2503562736187698648489703

theorem tailTrace_4875671 : CollatzResearch.WordTrace tailWord_4875671 prefixEnd_4875671 2503562736187698648489703 := by
  unfold tailWord_4875671
  simp only [CollatzResearch.WordTrace]
  refine ⟨177830330719284140157410867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118553553812856093438273911 177830330719284140157410867)
  ·
    refine ⟨266745496078926210236116301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177830330719284140157410867 266745496078926210236116301)
    ·
      refine ⟨100029561029597328838543613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266745496078926210236116301 100029561029597328838543613)
      ·
        refine ⟨37511085386098998314453855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100029561029597328838543613 37511085386098998314453855)
        ·
          refine ⟨56266628079148497471680783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37511085386098998314453855 56266628079148497471680783)
          ·
            refine ⟨84399942118722746207521175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56266628079148497471680783 84399942118722746207521175)
            ·
              refine ⟨126599913178084119311281763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84399942118722746207521175 126599913178084119311281763)
              ·
                refine ⟨189899869767126178966922645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126599913178084119311281763 189899869767126178966922645)
                ·
                  refine ⟨8901556395334039639074499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 189899869767126178966922645 8901556395334039639074499)
                  ·
                    refine ⟨13352334593001059458611749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8901556395334039639074499 13352334593001059458611749)
                    ·
                      refine ⟨2503562736187698648489703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13352334593001059458611749 2503562736187698648489703)
                      ·
                        rfl

theorem cell23_4875671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_4875671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875671 prefixEnd_4875671 := by exact prefixLift 4875671
  have htrace : WordTrace (prefixWord ++ tailWord_4875671) baseStart_4875671 baseEnd_4875671 := by
    simpa [prefixWord, tailWord_4875671, baseEnd_4875671] using wordTrace_append hprefix tailTrace_4875671
  have hstable : (prefixWord ++ tailWord_4875671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875671).length < 2 ^ (prefixWord ++ tailWord_4875671).sum := by decide
  have hdescent : baseEnd_4875671 < baseStart_4875671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875721 : List Nat := [1, 2, 1, 1, 2, 1, 3, 2, 2, 5, 3]
def baseStart_4875721 : Nat := 118140960795 + 4875721 * 2 ^ 59
def prefixEnd_4875721 : Nat := 4983230072969 + 3 ^ 40 * 4875721 * 2
def baseEnd_4875721 : Nat := 2503588410220423452864473

theorem tailTrace_4875721 : CollatzResearch.WordTrace tailWord_4875721 prefixEnd_4875721 2503588410220423452864473 := by
  unfold tailWord_4875721
  simp only [CollatzResearch.WordTrace]
  refine ⟨177832154369102998696731017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118554769579401999131154011 177832154369102998696731017)
  ·
    refine ⟨133374115776827249022548263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177832154369102998696731017 133374115776827249022548263)
    ·
      refine ⟨200061173665240873533822395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133374115776827249022548263 200061173665240873533822395)
      ·
        refine ⟨300091760497861310300733593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200061173665240873533822395 300091760497861310300733593)
        ·
          refine ⟨225068820373395982725550195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300091760497861310300733593 225068820373395982725550195)
          ·
            refine ⟨337603230560093974088325293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225068820373395982725550195 337603230560093974088325293)
            ·
              refine ⟨126601211460035240283121985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337603230560093974088325293 126601211460035240283121985)
              ·
                refine ⟨94950908595026430212341489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126601211460035240283121985 94950908595026430212341489)
                ·
                  refine ⟨71213181446269822659256117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94950908595026430212341489 71213181446269822659256117)
                  ·
                    refine ⟨6676235760587795874305261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71213181446269822659256117 6676235760587795874305261)
                    ·
                      refine ⟨2503588410220423452864473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6676235760587795874305261 2503588410220423452864473)
                      ·
                        rfl

theorem cell23_4875721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 2, 2, 5, 3].length) (baseStart_4875721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875721 prefixEnd_4875721 := by exact prefixLift 4875721
  have htrace : WordTrace (prefixWord ++ tailWord_4875721) baseStart_4875721 baseEnd_4875721 := by
    simpa [prefixWord, tailWord_4875721, baseEnd_4875721] using wordTrace_append hprefix tailTrace_4875721
  have hstable : (prefixWord ++ tailWord_4875721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875721).length < 2 ^ (prefixWord ++ tailWord_4875721).sum := by decide
  have hdescent : baseEnd_4875721 < baseStart_4875721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875772 : List Nat := [2, 2, 2, 1, 2, 1, 4, 4, 1, 1, 3]
def baseStart_4875772 : Nat := 118140960795 + 4875772 * 2 ^ 59
def prefixEnd_4875772 : Nat := 4983230072969 + 3 ^ 40 * 4875772 * 2
def baseEnd_4875772 : Nat := 2503614597733802753326739

theorem tailTrace_4875772 : CollatzResearch.WordTrace tailWord_4875772 prefixEnd_4875772 2503614597733802753326739 := by
  unfold tailWord_4875772
  simp only [CollatzResearch.WordTrace]
  refine ⟨88917007245959117203418785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118556009661278822937891713 88917007245959117203418785)
  ·
    refine ⟨66687755434469337902564089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88917007245959117203418785 66687755434469337902564089)
    ·
      refine ⟨50015816575852003426923067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66687755434469337902564089 50015816575852003426923067)
      ·
        refine ⟨75023724863778005140384601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50015816575852003426923067 75023724863778005140384601)
        ·
          refine ⟨56267793647833503855288451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75023724863778005140384601 56267793647833503855288451)
          ·
            refine ⟨84401690471750255782932677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56267793647833503855288451 84401690471750255782932677)
            ·
              refine ⟨15825316963453172959299877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84401690471750255782932677 15825316963453172959299877)
              ·
                refine ⟨2967246930647469929868727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15825316963453172959299877 2967246930647469929868727)
                ·
                  refine ⟨4450870395971204894803091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967246930647469929868727 4450870395971204894803091)
                  ·
                    refine ⟨6676305593956807342204637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4450870395971204894803091 6676305593956807342204637)
                    ·
                      refine ⟨2503614597733802753326739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6676305593956807342204637 2503614597733802753326739)
                      ·
                        rfl

theorem cell23_4875772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_4875772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875772 prefixEnd_4875772 := by exact prefixLift 4875772
  have htrace : WordTrace (prefixWord ++ tailWord_4875772) baseStart_4875772 baseEnd_4875772 := by
    simpa [prefixWord, tailWord_4875772, baseEnd_4875772] using wordTrace_append hprefix tailTrace_4875772
  have hstable : (prefixWord ++ tailWord_4875772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875772).length < 2 ^ (prefixWord ++ tailWord_4875772).sum := by decide
  have hdescent : baseEnd_4875772 < baseStart_4875772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875795 : List Nat := [1, 1, 1, 2, 1, 7, 2, 2, 1, 1, 4]
def baseStart_4875795 : Nat := 118140960795 + 4875795 * 2 ^ 59
def prefixEnd_4875795 : Nat := 4983230072969 + 3 ^ 40 * 4875795 * 2
def baseEnd_4875795 : Nat := 2503626407788856163339133

theorem tailTrace_4875795 : CollatzResearch.WordTrace tailWord_4875795 prefixEnd_4875795 2503626407788856163339133 := by
  unfold tailWord_4875795
  simp only [CollatzResearch.WordTrace]
  refine ⟨177834853370834909334924839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118556568913889939556616559 177834853370834909334924839)
  ·
    refine ⟨266752280056252364002387259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177834853370834909334924839 266752280056252364002387259)
    ·
      refine ⟨400128420084378546003580889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266752280056252364002387259 400128420084378546003580889)
      ·
        refine ⟨300096315063283909502685667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400128420084378546003580889 300096315063283909502685667)
        ·
          refine ⟨450144472594925864254028501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300096315063283909502685667 450144472594925864254028501)
          ·
            refine ⟨10550261076443574943453793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 450144472594925864254028501 10550261076443574943453793)
            ·
              refine ⟨7912695807332681207590345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10550261076443574943453793 7912695807332681207590345)
              ·
                refine ⟨5934521855499510905692759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7912695807332681207590345 5934521855499510905692759)
                ·
                  refine ⟨8901782783249266358539139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5934521855499510905692759 8901782783249266358539139)
                  ·
                    refine ⟨13352674174873899537808709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8901782783249266358539139 13352674174873899537808709)
                    ·
                      refine ⟨2503626407788856163339133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13352674174873899537808709 2503626407788856163339133)
                      ·
                        rfl

theorem cell23_4875795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 2, 2, 1, 1, 4].length) (baseStart_4875795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875795 prefixEnd_4875795 := by exact prefixLift 4875795
  have htrace : WordTrace (prefixWord ++ tailWord_4875795) baseStart_4875795 baseEnd_4875795 := by
    simpa [prefixWord, tailWord_4875795, baseEnd_4875795] using wordTrace_append hprefix tailTrace_4875795
  have hstable : (prefixWord ++ tailWord_4875795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875795).length < 2 ^ (prefixWord ++ tailWord_4875795).sum := by decide
  have hdescent : baseEnd_4875795 < baseStart_4875795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875829 : List Nat := [1, 3, 3, 1, 1, 5, 1, 1, 3, 2, 2]
def baseStart_4875829 : Nat := 118140960795 + 4875829 * 2 ^ 59
def prefixEnd_4875829 : Nat := 4983230072969 + 3 ^ 40 * 4875829 * 2
def baseEnd_4875829 : Nat := 2503643866131109030313977

theorem tailTrace_4875829 : CollatzResearch.WordTrace tailWord_4875829 prefixEnd_4875829 2503643866131109030313977 := by
  unfold tailWord_4875829
  simp only [CollatzResearch.WordTrace]
  refine ⟨177836093452711733141662541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118557395635141155427775027 177836093452711733141662541)
  ·
    refine ⟨66688535044766899928123453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177836093452711733141662541 66688535044766899928123453)
    ·
      refine ⟨25008200641787587473046295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66688535044766899928123453 25008200641787587473046295)
      ·
        refine ⟨37512300962681381209569443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25008200641787587473046295 37512300962681381209569443)
        ·
          refine ⟨56268451444022071814354165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37512300962681381209569443 56268451444022071814354165)
          ·
            refine ⟨5275167322877069232595703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56268451444022071814354165 5275167322877069232595703)
            ·
              refine ⟨7912750984315603848893555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5275167322877069232595703 7912750984315603848893555)
              ·
                refine ⟨11869126476473405773340333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7912750984315603848893555 11869126476473405773340333)
                ·
                  refine ⟨4450922428677527165002625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11869126476473405773340333 4450922428677527165002625)
                  ·
                    refine ⟨3338191821508145373751969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4450922428677527165002625 3338191821508145373751969)
                    ·
                      refine ⟨2503643866131109030313977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3338191821508145373751969 2503643866131109030313977)
                      ·
                        rfl

theorem cell23_4875829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 5, 1, 1, 3, 2, 2].length) (baseStart_4875829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875829 prefixEnd_4875829 := by exact prefixLift 4875829
  have htrace : WordTrace (prefixWord ++ tailWord_4875829) baseStart_4875829 baseEnd_4875829 := by
    simpa [prefixWord, tailWord_4875829, baseEnd_4875829] using wordTrace_append hprefix tailTrace_4875829
  have hstable : (prefixWord ++ tailWord_4875829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875829).length < 2 ^ (prefixWord ++ tailWord_4875829).sum := by decide
  have hdescent : baseEnd_4875829 < baseStart_4875829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875846 : List Nat := [6, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_4875846 : Nat := 118140960795 + 4875846 * 2 ^ 59
def prefixEnd_4875846 : Nat := 4983230072969 + 3 ^ 40 * 4875846 * 2
def baseEnd_4875846 : Nat := 2503652595302235463801399

theorem tailTrace_4875846 : CollatzResearch.WordTrace tailWord_4875846 prefixEnd_4875846 2503652595302235463801399 := by
  unfold tailWord_4875846
  simp only [CollatzResearch.WordTrace]
  refine ⟨5557397296676567032657231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118557808995766763363354261 5557397296676567032657231)
  ·
    refine ⟨8336095945014850548985847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5557397296676567032657231 8336095945014850548985847)
    ·
      refine ⟨12504143917522275823478771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8336095945014850548985847 12504143917522275823478771)
      ·
        refine ⟨18756215876283413735218157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12504143917522275823478771 18756215876283413735218157)
        ·
          refine ⟨7033580953606280150706809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18756215876283413735218157 7033580953606280150706809)
          ·
            refine ⟨5275185715204710113030107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7033580953606280150706809 5275185715204710113030107)
            ·
              refine ⟨7912778572807065169545161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5275185715204710113030107 7912778572807065169545161)
              ·
                refine ⟨5934583929605298877158871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7912778572807065169545161 5934583929605298877158871)
                ·
                  refine ⟨8901875894407948315738307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5934583929605298877158871 8901875894407948315738307)
                  ·
                    refine ⟨13352813841611922473607461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8901875894407948315738307 13352813841611922473607461)
                    ·
                      refine ⟨2503652595302235463801399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13352813841611922473607461 2503652595302235463801399)
                      ·
                        rfl

theorem cell23_4875846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_4875846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875846 prefixEnd_4875846 := by exact prefixLift 4875846
  have htrace : WordTrace (prefixWord ++ tailWord_4875846) baseStart_4875846 baseEnd_4875846 := by
    simpa [prefixWord, tailWord_4875846, baseEnd_4875846] using wordTrace_append hprefix tailTrace_4875846
  have hstable : (prefixWord ++ tailWord_4875846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875846).length < 2 ^ (prefixWord ++ tailWord_4875846).sum := by decide
  have hdescent : baseEnd_4875846 < baseStart_4875846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875851 : List Nat := [1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 8]
def baseStart_4875851 : Nat := 118140960795 + 4875851 * 2 ^ 59
def prefixEnd_4875851 : Nat := 4983230072969 + 3 ^ 40 * 4875851 * 2
def baseEnd_4875851 : Nat := 2503655162705507944238875

theorem tailTrace_4875851 : CollatzResearch.WordTrace tailWord_4875851 prefixEnd_4875851 2503655162705507944238875 := by
  unfold tailWord_4875851
  simp only [CollatzResearch.WordTrace]
  refine ⟨177836895858632030898963407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118557930572421353932642271 177836895858632030898963407)
  ·
    refine ⟨266755343787948046348445111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177836895858632030898963407 266755343787948046348445111)
    ·
      refine ⟨400133015681922069522667667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266755343787948046348445111 400133015681922069522667667)
      ·
        refine ⟨600199523522883104284001501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400133015681922069522667667 600199523522883104284001501)
        ·
          refine ⟨225074821321081164106500563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 600199523522883104284001501 225074821321081164106500563)
          ·
            refine ⟨337612231981621746159750845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225074821321081164106500563 337612231981621746159750845)
            ·
              refine ⟨126604586993108154809906567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337612231981621746159750845 126604586993108154809906567)
              ·
                refine ⟨189906880489662232214859851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126604586993108154809906567 189906880489662232214859851)
                ·
                  refine ⟨284860320734493348322289777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 189906880489662232214859851 284860320734493348322289777)
                  ·
                    refine ⟨213645240550870011241717333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 284860320734493348322289777 213645240550870011241717333)
                    ·
                      refine ⟨2503655162705507944238875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 213645240550870011241717333 2503655162705507944238875)
                      ·
                        rfl

theorem cell23_4875851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 8].length) (baseStart_4875851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875851 prefixEnd_4875851 := by exact prefixLift 4875851
  have htrace : WordTrace (prefixWord ++ tailWord_4875851) baseStart_4875851 baseEnd_4875851 := by
    simpa [prefixWord, tailWord_4875851, baseEnd_4875851] using wordTrace_append hprefix tailTrace_4875851
  have hstable : (prefixWord ++ tailWord_4875851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875851).length < 2 ^ (prefixWord ++ tailWord_4875851).sum := by decide
  have hdescent : baseEnd_4875851 < baseStart_4875851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875936 : List Nat := [2, 1, 1, 4, 3, 3, 1, 2, 2, 2, 2]
def baseStart_4875936 : Nat := 118140960795 + 4875936 * 2 ^ 59
def prefixEnd_4875936 : Nat := 4983230072969 + 3 ^ 40 * 4875936 * 2
def baseEnd_4875936 : Nat := 2503698808561140111675985

theorem tailTrace_4875936 : CollatzResearch.WordTrace tailWord_4875936 prefixEnd_4875936 2503698808561140111675985 := by
  unfold tailWord_4875936
  simp only [CollatzResearch.WordTrace]
  refine ⟨88919998031662045207903831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118559997375549393610538441 88919998031662045207903831)
  ·
    refine ⟨133379997047493067811855747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88919998031662045207903831 133379997047493067811855747)
    ·
      refine ⟨200069995571239601717783621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133379997047493067811855747 200069995571239601717783621)
      ·
        refine ⟨37513124169607425322084429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200069995571239601717783621 37513124169607425322084429)
        ·
          refine ⟨14067421563602784495781661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37513124169607425322084429 14067421563602784495781661)
          ·
            refine ⟨5275283086351044185918123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14067421563602784495781661 5275283086351044185918123)
            ·
              refine ⟨7912924629526566278877185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5275283086351044185918123 7912924629526566278877185)
              ·
                refine ⟨5934693472144924709157889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7912924629526566278877185 5934693472144924709157889)
                ·
                  refine ⟨4451020104108693531868417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5934693472144924709157889 4451020104108693531868417)
                  ·
                    refine ⟨3338265078081520148901313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4451020104108693531868417 3338265078081520148901313)
                    ·
                      refine ⟨2503698808561140111675985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3338265078081520148901313 2503698808561140111675985)
                      ·
                        rfl

theorem cell23_4875936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 3, 1, 2, 2, 2, 2].length) (baseStart_4875936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875936 prefixEnd_4875936 := by exact prefixLift 4875936
  have htrace : WordTrace (prefixWord ++ tailWord_4875936) baseStart_4875936 baseEnd_4875936 := by
    simpa [prefixWord, tailWord_4875936, baseEnd_4875936] using wordTrace_append hprefix tailTrace_4875936
  have hstable : (prefixWord ++ tailWord_4875936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875936).length < 2 ^ (prefixWord ++ tailWord_4875936).sum := by decide
  have hdescent : baseEnd_4875936 < baseStart_4875936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875968 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 2, 8]
def baseStart_4875968 : Nat := 118140960795 + 4875968 * 2 ^ 59
def prefixEnd_4875968 : Nat := 4983230072969 + 3 ^ 40 * 4875968 * 2
def baseEnd_4875968 : Nat := 834571746647361328825279

theorem tailTrace_4875968 : CollatzResearch.WordTrace tailWord_4875968 prefixEnd_4875968 834571746647361328825279 := by
  unfold tailWord_4875968
  simp only [CollatzResearch.WordTrace]
  refine ⟨88920581599604079940486279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118560775466138773253981705 88920581599604079940486279)
  ·
    refine ⟨133380872399406119910729419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88920581599604079940486279 133380872399406119910729419)
    ·
      refine ⟨200071308599109179866094129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133380872399406119910729419 200071308599109179866094129)
      ·
        refine ⟨150053481449331884899570597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200071308599109179866094129 150053481449331884899570597)
        ·
          refine ⟨28135027771749728418669487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150053481449331884899570597 28135027771749728418669487)
          ·
            refine ⟨42202541657624592628004231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28135027771749728418669487 42202541657624592628004231)
            ·
              refine ⟨63303812486436888942006347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42202541657624592628004231 63303812486436888942006347)
              ·
                refine ⟨94955718729655333413009521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63303812486436888942006347 94955718729655333413009521)
                ·
                  refine ⟨71216789047241500059757141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94955718729655333413009521 71216789047241500059757141)
                  ·
                    refine ⟨834571746647361328825279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71216789047241500059757141 834571746647361328825279)
                    ·
                      rfl

theorem cell23_4875968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 2, 8].length) (baseStart_4875968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875968 prefixEnd_4875968 := by exact prefixLift 4875968
  have htrace : WordTrace (prefixWord ++ tailWord_4875968) baseStart_4875968 baseEnd_4875968 := by
    simpa [prefixWord, tailWord_4875968, baseEnd_4875968] using wordTrace_append hprefix tailTrace_4875968
  have hstable : (prefixWord ++ tailWord_4875968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875968).length < 2 ^ (prefixWord ++ tailWord_4875968).sum := by decide
  have hdescent : baseEnd_4875968 < baseStart_4875968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4875975 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 4]
def baseStart_4875975 : Nat := 118140960795 + 4875975 * 2 ^ 59
def prefixEnd_4875975 : Nat := 4983230072969 + 3 ^ 40 * 4875975 * 2
def baseEnd_4875975 : Nat := 2503718834306665459088305

theorem tailTrace_4875975 : CollatzResearch.WordTrace tailWord_4875975 prefixEnd_4875975 2503718834306665459088305 := by
  unfold tailWord_4875975
  simp only [CollatzResearch.WordTrace]
  refine ⟨177841418510182800076477379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118560945673455200050984919 177841418510182800076477379)
  ·
    refine ⟨266762127765274200114716069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177841418510182800076477379 266762127765274200114716069)
    ·
      refine ⟨50017898955988912521509263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266762127765274200114716069 50017898955988912521509263)
      ·
        refine ⟨75026848433983368782263895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50017898955988912521509263 75026848433983368782263895)
        ·
          refine ⟨112540272650975053173395843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75026848433983368782263895 112540272650975053173395843)
          ·
            refine ⟨168810408976462579760093765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112540272650975053173395843 168810408976462579760093765)
            ·
              refine ⟨31651951683086733705017581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168810408976462579760093765 31651951683086733705017581)
              ·
                refine ⟨11869481881157525139381593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31651951683086733705017581 11869481881157525139381593)
                ·
                  refine ⟨8902111410868143854536195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11869481881157525139381593 8902111410868143854536195)
                  ·
                    refine ⟨13353167116302215781804293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8902111410868143854536195 13353167116302215781804293)
                    ·
                      refine ⟨2503718834306665459088305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13353167116302215781804293 2503718834306665459088305)
                      ·
                        rfl

theorem cell23_4875975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_4875975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4875975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4875975 prefixEnd_4875975 := by exact prefixLift 4875975
  have htrace : WordTrace (prefixWord ++ tailWord_4875975) baseStart_4875975 baseEnd_4875975 := by
    simpa [prefixWord, tailWord_4875975, baseEnd_4875975] using wordTrace_append hprefix tailTrace_4875975
  have hstable : (prefixWord ++ tailWord_4875975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4875975).length < 2 ^ (prefixWord ++ tailWord_4875975).sum := by decide
  have hdescent : baseEnd_4875975 < baseStart_4875975 := by decide
  rcases family_descends (prefixWord ++ tailWord_4875975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876015 : List Nat := [1, 1, 2, 1, 5, 1, 3, 3, 6]
def baseStart_4876015 : Nat := 118140960795 + 4876015 * 2 ^ 59
def prefixEnd_4876015 : Nat := 4983230072969 + 3 ^ 40 * 4876015 * 2
def baseEnd_4876015 : Nat := 278193263725871700287569

theorem tailTrace_4876015 : CollatzResearch.WordTrace tailWord_4876015 prefixEnd_4876015 278193263725871700287569 := by
  unfold tailWord_4876015
  simp only [CollatzResearch.WordTrace]
  refine ⟨177842877430037886907933499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118561918286691924605288999 177842877430037886907933499)
  ·
    refine ⟨266764316145056830361900249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177842877430037886907933499 266764316145056830361900249)
    ·
      refine ⟨200073237108792622771425187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266764316145056830361900249 200073237108792622771425187)
      ·
        refine ⟨300109855663188934157137781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200073237108792622771425187 300109855663188934157137781)
        ·
          refine ⟨28135298968423962577231667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 300109855663188934157137781 28135298968423962577231667)
          ·
            refine ⟨42202948452635943865847501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28135298968423962577231667 42202948452635943865847501)
            ·
              refine ⟨15826105669738478949692813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42202948452635943865847501 15826105669738478949692813)
              ·
                refine ⟨5934789626151929606134805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15826105669738478949692813 5934789626151929606134805)
                ·
                  refine ⟨278193263725871700287569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5934789626151929606134805 278193263725871700287569)
                  ·
                    rfl

theorem cell23_4876015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 6].length) (baseStart_4876015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876015 prefixEnd_4876015 := by exact prefixLift 4876015
  have htrace : WordTrace (prefixWord ++ tailWord_4876015) baseStart_4876015 baseEnd_4876015 := by
    simpa [prefixWord, tailWord_4876015, baseEnd_4876015] using wordTrace_append hprefix tailTrace_4876015
  have hstable : (prefixWord ++ tailWord_4876015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876015).length < 2 ^ (prefixWord ++ tailWord_4876015).sum := by decide
  have hdescent : baseEnd_4876015 < baseStart_4876015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876059 : List Nat := [1, 1, 1, 1, 1, 1, 4, 8, 1, 1, 3]
def baseStart_4876059 : Nat := 118140960795 + 4876059 * 2 ^ 59
def prefixEnd_4876059 : Nat := 4983230072969 + 3 ^ 40 * 4876059 * 2
def baseEnd_4876059 : Nat := 2503761966681643130437919

theorem tailTrace_4876059 : CollatzResearch.WordTrace tailWord_4876059 prefixEnd_4876059 2503761966681643130437919 := by
  unfold tailWord_4876059
  simp only [CollatzResearch.WordTrace]
  refine ⟨177844482241878482422535231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118562988161252321615023487 177844482241878482422535231)
  ·
    refine ⟨266766723362817723633802847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177844482241878482422535231 266766723362817723633802847)
    ·
      refine ⟨400150085044226585450704271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266766723362817723633802847 400150085044226585450704271)
      ·
        refine ⟨600225127566339878176056407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400150085044226585450704271 600225127566339878176056407)
        ·
          refine ⟨900337691349509817264084611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600225127566339878176056407 900337691349509817264084611)
          ·
            refine ⟨1350506537024264725896126917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900337691349509817264084611 1350506537024264725896126917)
            ·
              refine ⟨253219975692049636105523797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1350506537024264725896126917 253219975692049636105523797)
              ·
                refine ⟨2967421590141206673111607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 253219975692049636105523797 2967421590141206673111607)
                ·
                  refine ⟨4451132385211810009667411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967421590141206673111607 4451132385211810009667411)
                  ·
                    refine ⟨6676698577817715014501117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4451132385211810009667411 6676698577817715014501117)
                    ·
                      refine ⟨2503761966681643130437919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6676698577817715014501117 2503761966681643130437919)
                      ·
                        rfl

theorem cell23_4876059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 8, 1, 1, 3].length) (baseStart_4876059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876059 prefixEnd_4876059 := by exact prefixLift 4876059
  have htrace : WordTrace (prefixWord ++ tailWord_4876059) baseStart_4876059 baseEnd_4876059 := by
    simpa [prefixWord, tailWord_4876059, baseEnd_4876059] using wordTrace_append hprefix tailTrace_4876059
  have hstable : (prefixWord ++ tailWord_4876059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876059).length < 2 ^ (prefixWord ++ tailWord_4876059).sum := by decide
  have hdescent : baseEnd_4876059 < baseStart_4876059 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876082 : List Nat := [3, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_4876082 : Nat := 118140960795 + 4876082 * 2 ^ 59
def prefixEnd_4876082 : Nat := 4983230072969 + 3 ^ 40 * 4876082 * 2
def baseEnd_4876082 : Nat := 2503773776736696540450313

theorem tailTrace_4876082 : CollatzResearch.WordTrace tailWord_4876082 prefixEnd_4876082 2503773776736696540450313 := by
  unfold tailWord_4876082
  simp only [CollatzResearch.WordTrace]
  refine ⟨44461330280198789337655625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118563547413863438233748333 44461330280198789337655625)
  ·
    refine ⟨33345997710149092003241719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44461330280198789337655625 33345997710149092003241719)
    ·
      refine ⟨50018996565223638004862579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33345997710149092003241719 50018996565223638004862579)
      ·
        refine ⟨75028494847835457007293869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50018996565223638004862579 75028494847835457007293869)
        ·
          refine ⟨28135685567938296377735201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75028494847835457007293869 28135685567938296377735201)
          ·
            refine ⟨21101764175953722283301401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28135685567938296377735201 21101764175953722283301401)
            ·
              refine ⟨15826323131965291712476051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21101764175953722283301401 15826323131965291712476051)
              ·
                refine ⟨23739484697947937568714077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15826323131965291712476051 23739484697947937568714077)
                ·
                  refine ⟨8902306761730476588267779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23739484697947937568714077 8902306761730476588267779)
                  ·
                    refine ⟨13353460142595714882401669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8902306761730476588267779 13353460142595714882401669)
                    ·
                      refine ⟨2503773776736696540450313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13353460142595714882401669 2503773776736696540450313)
                      ·
                        rfl

theorem cell23_4876082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_4876082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876082 prefixEnd_4876082 := by exact prefixLift 4876082
  have htrace : WordTrace (prefixWord ++ tailWord_4876082) baseStart_4876082 baseEnd_4876082 := by
    simpa [prefixWord, tailWord_4876082, baseEnd_4876082] using wordTrace_append hprefix tailTrace_4876082
  have hstable : (prefixWord ++ tailWord_4876082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876082).length < 2 ^ (prefixWord ++ tailWord_4876082).sum := by decide
  have hdescent : baseEnd_4876082 < baseStart_4876082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876086 : List Nat := [5, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_4876086 : Nat := 118140960795 + 4876086 * 2 ^ 59
def prefixEnd_4876086 : Nat := 4983230072969 + 3 ^ 40 * 4876086 * 2
def baseEnd_4876086 : Nat := 2503775830659314524800295

theorem tailTrace_4876086 : CollatzResearch.WordTrace tailWord_4876086 prefixEnd_4876086 2503775830659314524800295 := by
  unfold tailWord_4876086
  simp only [CollatzResearch.WordTrace]
  refine ⟨11115341688298791627110507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118563644675187110689178741 11115341688298791627110507)
  ·
    refine ⟨16673012532448187440665761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11115341688298791627110507 16673012532448187440665761)
    ·
      refine ⟨12504759399336140580499321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16673012532448187440665761 12504759399336140580499321)
      ·
        refine ⟨9378569549502105435374491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12504759399336140580499321 9378569549502105435374491)
        ·
          refine ⟨14067854324253158153061737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9378569549502105435374491 14067854324253158153061737)
          ·
            refine ⟨10550890743189868614796303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14067854324253158153061737 10550890743189868614796303)
            ·
              refine ⟨15826336114784802922194455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10550890743189868614796303 15826336114784802922194455)
              ·
                refine ⟨23739504172177204383291683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15826336114784802922194455 23739504172177204383291683)
                ·
                  refine ⟨35609256258265806574937525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23739504172177204383291683 35609256258265806574937525)
                  ·
                    refine ⟨3338367774212419366400393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35609256258265806574937525 3338367774212419366400393)
                    ·
                      refine ⟨2503775830659314524800295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3338367774212419366400393 2503775830659314524800295)
                      ·
                        rfl

theorem cell23_4876086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_4876086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876086 prefixEnd_4876086 := by exact prefixLift 4876086
  have htrace : WordTrace (prefixWord ++ tailWord_4876086) baseStart_4876086 baseEnd_4876086 := by
    simpa [prefixWord, tailWord_4876086, baseEnd_4876086] using wordTrace_append hprefix tailTrace_4876086
  have hstable : (prefixWord ++ tailWord_4876086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876086).length < 2 ^ (prefixWord ++ tailWord_4876086).sum := by decide
  have hdescent : baseEnd_4876086 < baseStart_4876086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876093 : List Nat := [1, 4, 1, 4, 1, 2, 2, 3, 1, 1, 3]
def baseStart_4876093 : Nat := 118140960795 + 4876093 * 2 ^ 59
def prefixEnd_4876093 : Nat := 4983230072969 + 3 ^ 40 * 4876093 * 2
def baseEnd_4876093 : Nat := 2503779425023895997412763

theorem tailTrace_4876093 : CollatzResearch.WordTrace tailWord_4876093 prefixEnd_4876093 2503779425023895997412763 := by
  unfold tailWord_4876093
  simp only [CollatzResearch.WordTrace]
  refine ⟨177845722323755306229272933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118563814882503537486181955 177845722323755306229272933)
  ·
    refine ⟨33346072935704119917988675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177845722323755306229272933 33346072935704119917988675)
    ·
      refine ⟨50019109403556179876983013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33346072935704119917988675 50019109403556179876983013)
      ·
        refine ⟨9378583013166783726934315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50019109403556179876983013 9378583013166783726934315)
        ·
          refine ⟨14067874519750175590401473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9378583013166783726934315 14067874519750175590401473)
          ·
            refine ⟨10550905889812631692801105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14067874519750175590401473 10550905889812631692801105)
            ·
              refine ⟨7913179417359473769600829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10550905889812631692801105 7913179417359473769600829)
              ·
                refine ⟨2967442281509802663600311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7913179417359473769600829 2967442281509802663600311)
                ·
                  refine ⟨4451163422264703995400467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967442281509802663600311 4451163422264703995400467)
                  ·
                    refine ⟨6676745133397055993100701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4451163422264703995400467 6676745133397055993100701)
                    ·
                      refine ⟨2503779425023895997412763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6676745133397055993100701 2503779425023895997412763)
                      ·
                        rfl

theorem cell23_4876093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 3, 1, 1, 3].length) (baseStart_4876093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876093 prefixEnd_4876093 := by exact prefixLift 4876093
  have htrace : WordTrace (prefixWord ++ tailWord_4876093) baseStart_4876093 baseEnd_4876093 := by
    simpa [prefixWord, tailWord_4876093, baseEnd_4876093] using wordTrace_append hprefix tailTrace_4876093
  have hstable : (prefixWord ++ tailWord_4876093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876093).length < 2 ^ (prefixWord ++ tailWord_4876093).sum := by decide
  have hdescent : baseEnd_4876093 < baseStart_4876093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876099 : List Nat := [1, 1, 1, 3, 1, 5, 4, 1, 1, 1, 4]
def baseStart_4876099 : Nat := 118140960795 + 4876099 * 2 ^ 59
def prefixEnd_4876099 : Nat := 4983230072969 + 3 ^ 40 * 4876099 * 2
def baseEnd_4876099 : Nat := 2503782505907822973937735

theorem tailTrace_4876099 : CollatzResearch.WordTrace tailWord_4876099 prefixEnd_4876099 2503782505907822973937735 := by
  unfold tailWord_4876099
  simp only [CollatzResearch.WordTrace]
  refine ⟨177845941161733569253991351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118563960774489046169327567 177845941161733569253991351)
  ·
    refine ⟨266768911742600353880987027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177845941161733569253991351 266768911742600353880987027)
    ·
      refine ⟨400153367613900530821480541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266768911742600353880987027 400153367613900530821480541)
      ·
        refine ⟨150057512855212699058055203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 400153367613900530821480541 150057512855212699058055203)
        ·
          refine ⟨225086269282819048587082805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150057512855212699058055203 225086269282819048587082805)
          ·
            refine ⟨21101837745264285805039013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 225086269282819048587082805 21101837745264285805039013)
            ·
              refine ⟨3956594577237053588444815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21101837745264285805039013 3956594577237053588444815)
              ·
                refine ⟨5934891865855580382667223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3956594577237053588444815 5934891865855580382667223)
                ·
                  refine ⟨8902337798783370574000835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5934891865855580382667223 8902337798783370574000835)
                  ·
                    refine ⟨13353506698175055861001253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8902337798783370574000835 13353506698175055861001253)
                    ·
                      refine ⟨2503782505907822973937735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13353506698175055861001253 2503782505907822973937735)
                      ·
                        rfl

theorem cell23_4876099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 4, 1, 1, 1, 4].length) (baseStart_4876099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876099 prefixEnd_4876099 := by exact prefixLift 4876099
  have htrace : WordTrace (prefixWord ++ tailWord_4876099) baseStart_4876099 baseEnd_4876099 := by
    simpa [prefixWord, tailWord_4876099, baseEnd_4876099] using wordTrace_append hprefix tailTrace_4876099
  have hstable : (prefixWord ++ tailWord_4876099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876099).length < 2 ^ (prefixWord ++ tailWord_4876099).sum := by decide
  have hdescent : baseEnd_4876099 < baseStart_4876099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876115 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 3]
def baseStart_4876115 : Nat := 118140960795 + 4876115 * 2 ^ 59
def prefixEnd_4876115 : Nat := 4983230072969 + 3 ^ 40 * 4876115 * 2
def baseEnd_4876115 : Nat := 2503790721598294911337661

theorem tailTrace_4876115 : CollatzResearch.WordTrace tailWord_4876115 prefixEnd_4876115 2503790721598294911337661 := by
  unfold tailWord_4876115
  simp only [CollatzResearch.WordTrace]
  refine ⟨177846524729675603986573799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118564349819783735991049199 177846524729675603986573799)
  ·
    refine ⟨266769787094513405979860699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177846524729675603986573799 266769787094513405979860699)
    ·
      refine ⟨400154680641770108969791049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266769787094513405979860699 400154680641770108969791049)
      ·
        refine ⟨300116010481327581727343287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400154680641770108969791049 300116010481327581727343287)
        ·
          refine ⟨450174015721991372591014931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300116010481327581727343287 450174015721991372591014931)
          ·
            refine ⟨675261023582987058886522397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450174015721991372591014931 675261023582987058886522397)
            ·
              refine ⟨253222883843620147082445899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 675261023582987058886522397 253222883843620147082445899)
              ·
                refine ⟨379834325765430220623668849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253222883843620147082445899 379834325765430220623668849)
                ·
                  refine ⟨284875744324072665467751637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 379834325765430220623668849 284875744324072665467751637)
                  ·
                    refine ⟨6676775257595453096900429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 284875744324072665467751637 6676775257595453096900429)
                    ·
                      refine ⟨2503790721598294911337661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6676775257595453096900429 2503790721598294911337661)
                      ·
                        rfl

theorem cell23_4876115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 3].length) (baseStart_4876115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876115 prefixEnd_4876115 := by exact prefixLift 4876115
  have htrace : WordTrace (prefixWord ++ tailWord_4876115) baseStart_4876115 baseEnd_4876115 := by
    simpa [prefixWord, tailWord_4876115, baseEnd_4876115] using wordTrace_append hprefix tailTrace_4876115
  have hstable : (prefixWord ++ tailWord_4876115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876115).length < 2 ^ (prefixWord ++ tailWord_4876115).sum := by decide
  have hdescent : baseEnd_4876115 < baseStart_4876115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876116 : List Nat := [2, 4, 1, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_4876116 : Nat := 118140960795 + 4876116 * 2 ^ 59
def prefixEnd_4876116 : Nat := 4983230072969 + 3 ^ 40 * 4876116 * 2
def baseEnd_4876116 : Nat := 2503791235078949407425157

theorem tailTrace_4876116 : CollatzResearch.WordTrace tailWord_4876116 prefixEnd_4876116 2503791235078949407425157 := by
  unfold tailWord_4876116
  simp only [CollatzResearch.WordTrace]
  refine ⟨88923280601335990578680101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118564374135114654104906801 88923280601335990578680101)
  ·
    refine ⟨16673115112750498233502519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88923280601335990578680101 16673115112750498233502519)
    ·
      refine ⟨25009672669125747350253779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16673115112750498233502519 25009672669125747350253779)
      ·
        refine ⟨37514509003688621025380669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25009672669125747350253779 37514509003688621025380669)
        ·
          refine ⟨14067940876383232884517751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37514509003688621025380669 14067940876383232884517751)
          ·
            refine ⟨21101911314574849326776627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14067940876383232884517751 21101911314574849326776627)
            ·
              refine ⟨31652866971862273990164941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21101911314574849326776627 31652866971862273990164941)
              ·
                refine ⟨11869825114448352746311853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31652866971862273990164941 11869825114448352746311853)
                ·
                  refine ⟨4451184417918132279866945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11869825114448352746311853 4451184417918132279866945)
                  ·
                    refine ⟨3338388313438599209900209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4451184417918132279866945 3338388313438599209900209)
                    ·
                      refine ⟨2503791235078949407425157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3338388313438599209900209 2503791235078949407425157)
                      ·
                        rfl

theorem cell23_4876116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_4876116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876116 prefixEnd_4876116 := by exact prefixLift 4876116
  have htrace : WordTrace (prefixWord ++ tailWord_4876116) baseStart_4876116 baseEnd_4876116 := by
    simpa [prefixWord, tailWord_4876116, baseEnd_4876116] using wordTrace_append hprefix tailTrace_4876116
  have hstable : (prefixWord ++ tailWord_4876116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876116).length < 2 ^ (prefixWord ++ tailWord_4876116).sum := by decide
  have hdescent : baseEnd_4876116 < baseStart_4876116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876145 : List Nat := [1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 5]
def baseStart_4876145 : Nat := 118140960795 + 4876145 * 2 ^ 59
def prefixEnd_4876145 : Nat := 4983230072969 + 3 ^ 40 * 4876145 * 2
def baseEnd_4876145 : Nat := 2503806126017929793962523

theorem tailTrace_4876145 : CollatzResearch.WordTrace tailWord_4876145 prefixEnd_4876145 2503806126017929793962523 := by
  unfold tailWord_4876145
  simp only [CollatzResearch.WordTrace]
  refine ⟨177847618919566919110165889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118565079279711279406777259 177847618919566919110165889)
  ·
    refine ⟨133385714189675189332624417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177847618919566919110165889 133385714189675189332624417)
    ·
      refine ⟨100039285642256391999468313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133385714189675189332624417 100039285642256391999468313)
      ·
        refine ⟨75029464231692293999601235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100039285642256391999468313 75029464231692293999601235)
        ·
          refine ⟨112544196347538440999401853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75029464231692293999601235 112544196347538440999401853)
          ·
            refine ⟨42204073630326915374775695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112544196347538440999401853 42204073630326915374775695)
            ·
              refine ⟨63306110445490373062163543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42204073630326915374775695 63306110445490373062163543)
              ·
                refine ⟨94959165668235559593245315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63306110445490373062163543 94959165668235559593245315)
                ·
                  refine ⟨142438748502353339389867973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94959165668235559593245315 142438748502353339389867973)
                  ·
                    refine ⟨26707265344191251135600245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 142438748502353339389867973 26707265344191251135600245)
                    ·
                      refine ⟨2503806126017929793962523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26707265344191251135600245 2503806126017929793962523)
                      ·
                        rfl

theorem cell23_4876145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_4876145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876145 prefixEnd_4876145 := by exact prefixLift 4876145
  have htrace : WordTrace (prefixWord ++ tailWord_4876145) baseStart_4876145 baseEnd_4876145 := by
    simpa [prefixWord, tailWord_4876145, baseEnd_4876145] using wordTrace_append hprefix tailTrace_4876145
  have hstable : (prefixWord ++ tailWord_4876145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876145).length < 2 ^ (prefixWord ++ tailWord_4876145).sum := by decide
  have hdescent : baseEnd_4876145 < baseStart_4876145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876149 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 6, 1, 3]
def baseStart_4876149 : Nat := 118140960795 + 4876149 * 2 ^ 59
def prefixEnd_4876149 : Nat := 4983230072969 + 3 ^ 40 * 4876149 * 2
def baseEnd_4876149 : Nat := 2503808179940547778312505

theorem tailTrace_4876149 : CollatzResearch.WordTrace tailWord_4876149 prefixEnd_4876149 2503808179940547778312505 := by
  unfold tailWord_4876149
  simp only [CollatzResearch.WordTrace]
  refine ⟨177847764811552427793311501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118565176541034951862207667 177847764811552427793311501)
  ·
    refine ⟨66692911804332160422491813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177847764811552427793311501 66692911804332160422491813)
    ·
      refine ⟨12504920963312280079217215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66692911804332160422491813 12504920963312280079217215)
      ·
        refine ⟨18757381444968420118825823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12504920963312280079217215 18757381444968420118825823)
        ·
          refine ⟨28136072167452630178238735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18757381444968420118825823 28136072167452630178238735)
          ·
            refine ⟨42204108251178945267358103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28136072167452630178238735 42204108251178945267358103)
            ·
              refine ⟨63306162376768417901037155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42204108251178945267358103 63306162376768417901037155)
              ·
                refine ⟨94959243565152626851555733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63306162376768417901037155 94959243565152626851555733)
                ·
                  refine ⟨4451214542116529383666675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 94959243565152626851555733 4451214542116529383666675)
                  ·
                    refine ⟨6676821813174794075500013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4451214542116529383666675 6676821813174794075500013)
                    ·
                      refine ⟨2503808179940547778312505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6676821813174794075500013 2503808179940547778312505)
                      ·
                        rfl

theorem cell23_4876149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_4876149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876149 prefixEnd_4876149 := by exact prefixLift 4876149
  have htrace : WordTrace (prefixWord ++ tailWord_4876149) baseStart_4876149 baseEnd_4876149 := by
    simpa [prefixWord, tailWord_4876149, baseEnd_4876149] using wordTrace_append hprefix tailTrace_4876149
  have hstable : (prefixWord ++ tailWord_4876149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876149).length < 2 ^ (prefixWord ++ tailWord_4876149).sum := by decide
  have hdescent : baseEnd_4876149 < baseStart_4876149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876155 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 4]
def baseStart_4876155 : Nat := 118140960795 + 4876155 * 2 ^ 59
def prefixEnd_4876155 : Nat := 4983230072969 + 3 ^ 40 * 4876155 * 2
def baseEnd_4876155 : Nat := 2503811260824474754837477

theorem tailTrace_4876155 : CollatzResearch.WordTrace tailWord_4876155 prefixEnd_4876155 2503811260824474754837477 := by
  unfold tailWord_4876155
  simp only [CollatzResearch.WordTrace]
  refine ⟨177847983649530690818029919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118565322433020460545353279 177847983649530690818029919)
  ·
    refine ⟨266771975474296036227044879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177847983649530690818029919 266771975474296036227044879)
    ·
      refine ⟨400157963211444054340567319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266771975474296036227044879 400157963211444054340567319)
      ·
        refine ⟨600236944817166081510850979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400157963211444054340567319 600236944817166081510850979)
        ·
          refine ⟨900355417225749122266276469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600236944817166081510850979 900355417225749122266276469)
          ·
            refine ⟨84408320364913980212463419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 900355417225749122266276469 84408320364913980212463419)
            ·
              refine ⟨126612480547370970318695129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84408320364913980212463419 126612480547370970318695129)
              ·
                refine ⟨94959360410528227739021347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126612480547370970318695129 94959360410528227739021347)
                ·
                  refine ⟨142439040615792341608532021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94959360410528227739021347 142439040615792341608532021)
                  ·
                    refine ⟨13353660057730532025799877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 142439040615792341608532021 13353660057730532025799877)
                    ·
                      refine ⟨2503811260824474754837477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13353660057730532025799877 2503811260824474754837477)
                      ·
                        rfl

theorem cell23_4876155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 4].length) (baseStart_4876155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876155 prefixEnd_4876155 := by exact prefixLift 4876155
  have htrace : WordTrace (prefixWord ++ tailWord_4876155) baseStart_4876155 baseEnd_4876155 := by
    simpa [prefixWord, tailWord_4876155, baseEnd_4876155] using wordTrace_append hprefix tailTrace_4876155
  have hstable : (prefixWord ++ tailWord_4876155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876155).length < 2 ^ (prefixWord ++ tailWord_4876155).sum := by decide
  have hdescent : baseEnd_4876155 < baseStart_4876155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876183 : List Nat := [1, 1, 3, 3, 1, 5, 2, 1, 2, 1, 3]
def baseStart_4876183 : Nat := 118140960795 + 4876183 * 2 ^ 59
def prefixEnd_4876183 : Nat := 4983230072969 + 3 ^ 40 * 4876183 * 2
def baseEnd_4876183 : Nat := 2503825638282800645287349

theorem tailTrace_4876183 : CollatzResearch.WordTrace tailWord_4876183 prefixEnd_4876183 2503825638282800645287349 := by
  unfold tailWord_4876183
  simp only [CollatzResearch.WordTrace]
  refine ⟨177849004893429251600049203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118566003262286167733366135 177849004893429251600049203)
  ·
    refine ⟨266773507340143877400073805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177849004893429251600049203 266773507340143877400073805)
    ·
      refine ⟨100040065252553954025027677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266773507340143877400073805 100040065252553954025027677)
      ·
        refine ⟨37515024469707732759385379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100040065252553954025027677 37515024469707732759385379)
        ·
          refine ⟨56272536704561599139078069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37515024469707732759385379 56272536704561599139078069)
          ·
            refine ⟨5275550316052649919288569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56272536704561599139078069 5275550316052649919288569)
            ·
              refine ⟨3956662737039487439466427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5275550316052649919288569 3956662737039487439466427)
              ·
                refine ⟨5934994105559231159199641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3956662737039487439466427 5934994105559231159199641)
                ·
                  refine ⟨4451245579169423369399731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5934994105559231159199641 4451245579169423369399731)
                  ·
                    refine ⟨6676868368754135054099597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4451245579169423369399731 6676868368754135054099597)
                    ·
                      refine ⟨2503825638282800645287349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6676868368754135054099597 2503825638282800645287349)
                      ·
                        rfl

theorem cell23_4876183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_4876183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876183 prefixEnd_4876183 := by exact prefixLift 4876183
  have htrace : WordTrace (prefixWord ++ tailWord_4876183) baseStart_4876183 baseEnd_4876183 := by
    simpa [prefixWord, tailWord_4876183, baseEnd_4876183] using wordTrace_append hprefix tailTrace_4876183
  have hstable : (prefixWord ++ tailWord_4876183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876183).length < 2 ^ (prefixWord ++ tailWord_4876183).sum := by decide
  have hdescent : baseEnd_4876183 < baseStart_4876183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876195 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 9]
def baseStart_4876195 : Nat := 118140960795 + 4876195 * 2 ^ 59
def prefixEnd_4876195 : Nat := 4983230072969 + 3 ^ 40 * 4876195 * 2
def baseEnd_4876195 : Nat := 278203533338961622037477

theorem tailTrace_4876195 : CollatzResearch.WordTrace tailWord_4876195 prefixEnd_4876195 278203533338961622037477 := by
  unfold tailWord_4876195
  simp only [CollatzResearch.WordTrace]
  refine ⟨177849442569385777649486039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118566295046257185099657359 177849442569385777649486039)
  ·
    refine ⟨266774163854078666474229059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177849442569385777649486039 266774163854078666474229059)
    ·
      refine ⟨400161245781117999711343589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266774163854078666474229059 400161245781117999711343589)
      ·
        refine ⟨75030233583959624945876923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 400161245781117999711343589 75030233583959624945876923)
        ·
          refine ⟨112545350375939437418815385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75030233583959624945876923 112545350375939437418815385)
          ·
            refine ⟨84409012781954578064111539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112545350375939437418815385 84409012781954578064111539)
            ·
              refine ⟨126613519172931867096167309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84409012781954578064111539 126613519172931867096167309)
              ·
                refine ⟨47480069689849450161062741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126613519172931867096167309 47480069689849450161062741)
                ·
                  refine ⟨278203533338961622037477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47480069689849450161062741 278203533338961622037477)
                  ·
                    rfl

theorem cell23_4876195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 9].length) (baseStart_4876195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876195 prefixEnd_4876195 := by exact prefixLift 4876195
  have htrace : WordTrace (prefixWord ++ tailWord_4876195) baseStart_4876195 baseEnd_4876195 := by
    simpa [prefixWord, tailWord_4876195, baseEnd_4876195] using wordTrace_append hprefix tailTrace_4876195
  have hstable : (prefixWord ++ tailWord_4876195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876195).length < 2 ^ (prefixWord ++ tailWord_4876195).sum := by decide
  have hdescent : baseEnd_4876195 < baseStart_4876195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876246 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 7]
def baseStart_4876246 : Nat := 118140960795 + 4876246 * 2 ^ 59
def prefixEnd_4876246 : Nat := 4983230072969 + 3 ^ 40 * 4876246 * 2
def baseEnd_4876246 : Nat := 278206443062670433199951

theorem tailTrace_4876246 : CollatzResearch.WordTrace tailWord_4876246 prefixEnd_4876246 278206443062670433199951 := by
  unfold tailWord_4876246
  simp only [CollatzResearch.WordTrace]
  refine ⟨11115706418262563334974537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118567535128134008906395061 11115706418262563334974537)
  ·
    refine ⟨8336779813696922501230903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11115706418262563334974537 8336779813696922501230903)
    ·
      refine ⟨12505169720545383751846355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8336779813696922501230903 12505169720545383751846355)
      ·
        refine ⟨18757754580818075627769533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12505169720545383751846355 18757754580818075627769533)
        ·
          refine ⟨7034157967806778360413575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18757754580818075627769533 7034157967806778360413575)
          ·
            refine ⟨10551236951710167540620363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7034157967806778360413575 10551236951710167540620363)
            ·
              refine ⟨15826855427565251310930545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10551236951710167540620363 15826855427565251310930545)
              ·
                refine ⟨11870141570673938483197909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15826855427565251310930545 11870141570673938483197909)
                ·
                  refine ⟨278206443062670433199951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11870141570673938483197909 278206443062670433199951)
                  ·
                    rfl

theorem cell23_4876246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 7].length) (baseStart_4876246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876246 prefixEnd_4876246 := by exact prefixLift 4876246
  have htrace : WordTrace (prefixWord ++ tailWord_4876246) baseStart_4876246 baseEnd_4876246 := by
    simpa [prefixWord, tailWord_4876246, baseEnd_4876246] using wordTrace_append hprefix tailTrace_4876246
  have hstable : (prefixWord ++ tailWord_4876246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876246).length < 2 ^ (prefixWord ++ tailWord_4876246).sum := by decide
  have hdescent : baseEnd_4876246 < baseStart_4876246 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876259 : List Nat := [1, 1, 1, 6, 1, 2, 3, 1, 2, 5]
def baseStart_4876259 : Nat := 118140960795 + 4876259 * 2 ^ 59
def prefixEnd_4876259 : Nat := 4983230072969 + 3 ^ 40 * 4876259 * 2
def baseEnd_4876259 : Nat := 834621554270847449312333

theorem tailTrace_4876259 : CollatzResearch.WordTrace tailWord_4876259 prefixEnd_4876259 834621554270847449312333 := by
  unfold tailWord_4876259
  simp only [CollatzResearch.WordTrace]
  refine ⟨177851776841153916579815831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118567851227435944386543887 177851776841153916579815831)
  ·
    refine ⟨266777665261730874869723747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177851776841153916579815831 266777665261730874869723747)
    ·
      refine ⟨400166497892596312304585621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266777665261730874869723747 400166497892596312304585621)
      ·
        refine ⟨18757804588715452139277451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 400166497892596312304585621 18757804588715452139277451)
        ·
          refine ⟨28136706883073178208916177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18757804588715452139277451 28136706883073178208916177)
          ·
            refine ⟨21102530162304883656687133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28136706883073178208916177 21102530162304883656687133)
            ·
              refine ⟨7913448810864331371257675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21102530162304883656687133 7913448810864331371257675)
              ·
                refine ⟨11870173216296497056886513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7913448810864331371257675 11870173216296497056886513)
                ·
                  refine ⟨8902629912222372792664885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11870173216296497056886513 8902629912222372792664885)
                  ·
                    refine ⟨834621554270847449312333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8902629912222372792664885 834621554270847449312333)
                    ·
                      rfl

theorem cell23_4876259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 3, 1, 2, 5].length) (baseStart_4876259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876259 prefixEnd_4876259 := by exact prefixLift 4876259
  have htrace : WordTrace (prefixWord ++ tailWord_4876259) baseStart_4876259 baseEnd_4876259 := by
    simpa [prefixWord, tailWord_4876259, baseEnd_4876259] using wordTrace_append hprefix tailTrace_4876259
  have hstable : (prefixWord ++ tailWord_4876259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876259).length < 2 ^ (prefixWord ++ tailWord_4876259).sum := by decide
  have hdescent : baseEnd_4876259 < baseStart_4876259 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876340 : List Nat := [2, 5, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_4876340 : Nat := 118140960795 + 4876340 * 2 ^ 59
def prefixEnd_4876340 : Nat := 4983230072969 + 3 ^ 40 * 4876340 * 2
def baseEnd_4876340 : Nat := 834635418248518843674709

theorem tailTrace_4876340 : CollatzResearch.WordTrace tailWord_4876340 prefixEnd_4876340 834635418248518843674709 := by
  unfold tailWord_4876340
  simp only [CollatzResearch.WordTrace]
  refine ⟨88927365576930233706757237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118569820769240311609009649 88927365576930233706757237)
  ·
    refine ⟨8336940522837209410008491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88927365576930233706757237 8336940522837209410008491)
    ·
      refine ⟨12505410784255814115012737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8336940522837209410008491 12505410784255814115012737)
      ·
        refine ⟨9379058088191860586259553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12505410784255814115012737 9379058088191860586259553)
        ·
          refine ⟨7034293566143895439694665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9379058088191860586259553 7034293566143895439694665)
          ·
            refine ⟨5275720174607921579770999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7034293566143895439694665 5275720174607921579770999)
            ·
              refine ⟨7913580261911882369656499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5275720174607921579770999 7913580261911882369656499)
              ·
                refine ⟨11870370392867823554484749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7913580261911882369656499 11870370392867823554484749)
                ·
                  refine ⟨4451388897325433832931781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11870370392867823554484749 4451388897325433832931781)
                  ·
                    refine ⟨834635418248518843674709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4451388897325433832931781 834635418248518843674709)
                    ·
                      rfl

theorem cell23_4876340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_4876340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876340 prefixEnd_4876340 := by exact prefixLift 4876340
  have htrace : WordTrace (prefixWord ++ tailWord_4876340) baseStart_4876340 baseEnd_4876340 := by
    simpa [prefixWord, tailWord_4876340, baseEnd_4876340] using wordTrace_append hprefix tailTrace_4876340
  have hstable : (prefixWord ++ tailWord_4876340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876340).length < 2 ^ (prefixWord ++ tailWord_4876340).sum := by decide
  have hdescent : baseEnd_4876340 < baseStart_4876340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876349 : List Nat := [1, 4, 1, 3, 1, 1, 2, 2, 3, 5]
def baseStart_4876349 : Nat := 118140960795 + 4876349 * 2 ^ 59
def prefixEnd_4876349 : Nat := 4983230072969 + 3 ^ 40 * 4876349 * 2
def baseEnd_4876349 : Nat := 834636958690482331937195

theorem tailTrace_4876349 : CollatzResearch.WordTrace tailWord_4876349 prefixEnd_4876349 834636958690482331937195 := by
  unfold tailWord_4876349
  simp only [CollatzResearch.WordTrace]
  refine ⟨177855059410827861950592101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118570039607218574633728067 177855059410827861950592101)
  ·
    refine ⟨33347823639530224115736019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177855059410827861950592101 33347823639530224115736019)
    ·
      refine ⟨50021735459295336173604029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33347823639530224115736019 50021735459295336173604029)
      ·
        refine ⟨18758150797235751065101511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50021735459295336173604029 18758150797235751065101511)
        ·
          refine ⟨28137226195853626597652267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18758150797235751065101511 28137226195853626597652267)
          ·
            refine ⟨42205839293780439896478401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28137226195853626597652267 42205839293780439896478401)
            ·
              refine ⟨31654379470335329922358801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42205839293780439896478401 31654379470335329922358801)
              ·
                refine ⟨23740784602751497441769101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31654379470335329922358801 23740784602751497441769101)
                ·
                  refine ⟨8902794226031811540663413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23740784602751497441769101 8902794226031811540663413)
                  ·
                    refine ⟨834636958690482331937195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8902794226031811540663413 834636958690482331937195)
                    ·
                      rfl

theorem cell23_4876349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 2, 3, 5].length) (baseStart_4876349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876349 prefixEnd_4876349 := by exact prefixLift 4876349
  have htrace : WordTrace (prefixWord ++ tailWord_4876349) baseStart_4876349 baseEnd_4876349 := by
    simpa [prefixWord, tailWord_4876349, baseEnd_4876349] using wordTrace_append hprefix tailTrace_4876349
  have hstable : (prefixWord ++ tailWord_4876349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876349).length < 2 ^ (prefixWord ++ tailWord_4876349).sum := by decide
  have hdescent : baseEnd_4876349 < baseStart_4876349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876353 : List Nat := [1, 2, 5, 1, 2, 3, 2, 1, 6]
def baseStart_4876353 : Nat := 118140960795 + 4876353 * 2 ^ 59
def prefixEnd_4876353 : Nat := 4983230072969 + 3 ^ 40 * 4876353 * 2
def baseEnd_4876353 : Nat := 278212547777118331129063

theorem tailTrace_4876353 : CollatzResearch.WordTrace tailWord_4876353 prefixEnd_4876353 278212547777118331129063 := by
  unfold tailWord_4876353
  simp only [CollatzResearch.WordTrace]
  refine ⟨177855205302813370633737713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118570136868542247089158475 177855205302813370633737713)
  ·
    refine ⟨133391403977110027975303285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177855205302813370633737713 133391403977110027975303285)
    ·
      refine ⟨12505444122854065122684683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133391403977110027975303285 12505444122854065122684683)
      ·
        refine ⟨18758166184281097684027025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12505444122854065122684683 18758166184281097684027025)
        ·
          refine ⟨14068624638210823263020269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18758166184281097684027025 14068624638210823263020269)
          ·
            refine ⟨5275734239329058723632601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14068624638210823263020269 5275734239329058723632601)
            ·
              refine ⟨3956800679496794042724451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5275734239329058723632601 3956800679496794042724451)
              ·
                refine ⟨5935201019245191064086677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3956800679496794042724451 5935201019245191064086677)
                ·
                  refine ⟨278212547777118331129063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5935201019245191064086677 278212547777118331129063)
                  ·
                    rfl

theorem cell23_4876353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 6].length) (baseStart_4876353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876353 prefixEnd_4876353 := by exact prefixLift 4876353
  have htrace : WordTrace (prefixWord ++ tailWord_4876353) baseStart_4876353 baseEnd_4876353 := by
    simpa [prefixWord, tailWord_4876353, baseEnd_4876353] using wordTrace_append hprefix tailTrace_4876353
  have hstable : (prefixWord ++ tailWord_4876353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876353).length < 2 ^ (prefixWord ++ tailWord_4876353).sum := by decide
  have hdescent : baseEnd_4876353 < baseStart_4876353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876366 : List Nat := [4, 1, 1, 1, 1, 4, 3, 2, 1, 5]
def baseStart_4876366 : Nat := 118140960795 + 4876366 * 2 ^ 59
def prefixEnd_4876366 : Nat := 4983230072969 + 3 ^ 40 * 4876366 * 2
def baseEnd_4876366 : Nat := 834639868414191143099669

theorem tailTrace_4876366 : CollatzResearch.WordTrace tailWord_4876366 prefixEnd_4876366 834639868414191143099669 := by
  unfold tailWord_4876366
  simp only [CollatzResearch.WordTrace]
  refine ⟨22231959931470784231745119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118570452967844182569307301 22231959931470784231745119)
  ·
    refine ⟨33347939897206176347617679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22231959931470784231745119 33347939897206176347617679)
    ·
      refine ⟨50021909845809264521426519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33347939897206176347617679 50021909845809264521426519)
      ·
        refine ⟨75032864768713896782139779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50021909845809264521426519 75032864768713896782139779)
        ·
          refine ⟨112549297153070845173209669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75032864768713896782139779 112549297153070845173209669)
          ·
            refine ⟨21102993216200783469976813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112549297153070845173209669 21102993216200783469976813)
            ·
              refine ⟨7913622456075293801241305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21102993216200783469976813 7913622456075293801241305)
              ·
                refine ⟨5935216842056470350930979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7913622456075293801241305 5935216842056470350930979)
                ·
                  refine ⟨8902825263084705526396469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5935216842056470350930979 8902825263084705526396469)
                  ·
                    refine ⟨834639868414191143099669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8902825263084705526396469 834639868414191143099669)
                    ·
                      rfl

theorem cell23_4876366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_4876366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876366 prefixEnd_4876366 := by exact prefixLift 4876366
  have htrace : WordTrace (prefixWord ++ tailWord_4876366) baseStart_4876366 baseEnd_4876366 := by
    simpa [prefixWord, tailWord_4876366, baseEnd_4876366] using wordTrace_append hprefix tailTrace_4876366
  have hstable : (prefixWord ++ tailWord_4876366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876366).length < 2 ^ (prefixWord ++ tailWord_4876366).sum := by decide
  have hdescent : baseEnd_4876366 < baseStart_4876366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876373 : List Nat := [1, 3, 2, 2, 1, 4, 2, 1, 2, 3, 2]
def baseStart_4876373 : Nat := 118140960795 + 4876373 * 2 ^ 59
def prefixEnd_4876373 : Nat := 4983230072969 + 3 ^ 40 * 4876373 * 2
def baseEnd_4876373 : Nat := 2503923199607154901911475

theorem tailTrace_4876373 : CollatzResearch.WordTrace tailWord_4876373 prefixEnd_4876373 2503923199607154901911475 := by
  unfold tailWord_4876373
  simp only [CollatzResearch.WordTrace]
  refine ⟨177855934762740914049465773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118570623175160609366310515 177855934762740914049465773)
  ·
    refine ⟨66695975536027842768549665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177855934762740914049465773 66695975536027842768549665)
    ·
      refine ⟨50021981652020882076412249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66695975536027842768549665 50021981652020882076412249)
      ·
        refine ⟨37516486239015661557309187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50021981652020882076412249 37516486239015661557309187)
        ·
          refine ⟨56274729358523492335963781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37516486239015661557309187 56274729358523492335963781)
          ·
            refine ⟨10551511754723154812993209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56274729358523492335963781 10551511754723154812993209)
            ·
              refine ⟨7913633816042366109744907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10551511754723154812993209 7913633816042366109744907)
              ·
                refine ⟨11870450724063549164617361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7913633816042366109744907 11870450724063549164617361)
                ·
                  refine ⟨8902838043047661873463021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11870450724063549164617361 8902838043047661873463021)
                  ·
                    refine ⟨3338564266142873202548633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8902838043047661873463021 3338564266142873202548633)
                    ·
                      refine ⟨2503923199607154901911475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3338564266142873202548633 2503923199607154901911475)
                      ·
                        rfl

theorem cell23_4876373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_4876373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876373 prefixEnd_4876373 := by exact prefixLift 4876373
  have htrace : WordTrace (prefixWord ++ tailWord_4876373) baseStart_4876373 baseEnd_4876373 := by
    simpa [prefixWord, tailWord_4876373, baseEnd_4876373] using wordTrace_append hprefix tailTrace_4876373
  have hstable : (prefixWord ++ tailWord_4876373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876373).length < 2 ^ (prefixWord ++ tailWord_4876373).sum := by decide
  have hdescent : baseEnd_4876373 < baseStart_4876373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876392 : List Nat := [2, 1, 4, 16]
def baseStart_4876392 : Nat := 118140960795 + 4876392 * 2 ^ 59
def prefixEnd_4876392 : Nat := 4983230072969 + 3 ^ 40 * 4876392 * 2
def baseEnd_4876392 : Nat := 1144916760740553419101

theorem tailTrace_4876392 : CollatzResearch.WordTrace tailWord_4876392 prefixEnd_4876392 1144916760740553419101 := by
  unfold tailWord_4876392
  simp only [CollatzResearch.WordTrace]
  refine ⟨88928313874836040147203715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118571085166448053529604953 88928313874836040147203715)
  ·
    refine ⟨133392470812254060220805573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88928313874836040147203715 133392470812254060220805573)
    ·
      refine ⟨25011088277297636291401045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133392470812254060220805573 25011088277297636291401045)
      ·
        refine ⟨1144916760740553419101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 16 25011088277297636291401045 1144916760740553419101)
        ·
          rfl

theorem cell23_4876392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 16].length) (baseStart_4876392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876392 prefixEnd_4876392 := by exact prefixLift 4876392
  have htrace : WordTrace (prefixWord ++ tailWord_4876392) baseStart_4876392 baseEnd_4876392 := by
    simpa [prefixWord, tailWord_4876392, baseEnd_4876392] using wordTrace_append hprefix tailTrace_4876392
  have hstable : (prefixWord ++ tailWord_4876392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876392).length < 2 ^ (prefixWord ++ tailWord_4876392).sum := by decide
  have hdescent : baseEnd_4876392 < baseStart_4876392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876396 : List Nat := [2, 2, 1, 1, 3, 3, 1, 4, 2, 4]
def baseStart_4876396 : Nat := 118140960795 + 4876396 * 2 ^ 59
def prefixEnd_4876396 : Nat := 4983230072969 + 3 ^ 40 * 4876396 * 2
def baseEnd_4876396 : Nat := 834645003220736103974623

theorem tailTrace_4876396 : CollatzResearch.WordTrace tailWord_4876396 prefixEnd_4876396 834645003220736103974623 := by
  unfold tailWord_4876396
  simp only [CollatzResearch.WordTrace]
  refine ⟨88928386820828794488776521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118571182427771725985035361 88928386820828794488776521)
  ·
    refine ⟨66696290115621595866582391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88928386820828794488776521 66696290115621595866582391)
    ·
      refine ⟨100044435173432393799873587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66696290115621595866582391 100044435173432393799873587)
      ·
        refine ⟨150066652760148590699810381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100044435173432393799873587 150066652760148590699810381)
        ·
          refine ⟨56274994785055721512428893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150066652760148590699810381 56274994785055721512428893)
          ·
            refine ⟨21103123044395895567160835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56274994785055721512428893 21103123044395895567160835)
            ·
              refine ⟨31654684566593843350741253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21103123044395895567160835 31654684566593843350741253)
              ·
                refine ⟨5935253356236345628263985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31654684566593843350741253 5935253356236345628263985)
                ·
                  refine ⟨4451440017177259221197989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5935253356236345628263985 4451440017177259221197989)
                  ·
                    refine ⟨834645003220736103974623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4451440017177259221197989 834645003220736103974623)
                    ·
                      rfl

theorem cell23_4876396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 2, 4].length) (baseStart_4876396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876396 prefixEnd_4876396 := by exact prefixLift 4876396
  have htrace : WordTrace (prefixWord ++ tailWord_4876396) baseStart_4876396 baseEnd_4876396 := by
    simpa [prefixWord, tailWord_4876396, baseEnd_4876396] using wordTrace_append hprefix tailTrace_4876396
  have hstable : (prefixWord ++ tailWord_4876396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876396).length < 2 ^ (prefixWord ++ tailWord_4876396).sum := by decide
  have hdescent : baseEnd_4876396 < baseStart_4876396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876409 : List Nat := [1, 2, 1, 3, 4, 1, 3, 8]
def baseStart_4876409 : Nat := 118140960795 + 4876409 * 2 ^ 59
def prefixEnd_4876409 : Nat := 4983230072969 + 3 ^ 40 * 4876409 * 2
def baseEnd_4876409 : Nat := 92738580922619139298567

theorem tailTrace_4876409 : CollatzResearch.WordTrace tailWord_4876409 prefixEnd_4876409 92738580922619139298567 := by
  unfold tailWord_4876409
  simp only [CollatzResearch.WordTrace]
  refine ⟨177857247790610492197776281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118571498527073661465184187 177857247790610492197776281)
  ·
    refine ⟨133392935842957869148332211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177857247790610492197776281 133392935842957869148332211)
    ·
      refine ⟨200089403764436803722498317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133392935842957869148332211 200089403764436803722498317)
      ·
        refine ⟨75033526411663801395936869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200089403764436803722498317 75033526411663801395936869)
        ·
          refine ⟨14068786202186962761738163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75033526411663801395936869 14068786202186962761738163)
          ·
            refine ⟨21103179303280444142607245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14068786202186962761738163 21103179303280444142607245)
            ·
              refine ⟨7913692238730166553477717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21103179303280444142607245 7913692238730166553477717)
              ·
                refine ⟨92738580922619139298567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7913692238730166553477717 92738580922619139298567)
                ·
                  rfl

theorem cell23_4876409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 3, 8].length) (baseStart_4876409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876409 prefixEnd_4876409 := by exact prefixLift 4876409
  have htrace : WordTrace (prefixWord ++ tailWord_4876409) baseStart_4876409 baseEnd_4876409 := by
    simpa [prefixWord, tailWord_4876409, baseEnd_4876409] using wordTrace_append hprefix tailTrace_4876409
  have hstable : (prefixWord ++ tailWord_4876409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876409).length < 2 ^ (prefixWord ++ tailWord_4876409).sum := by decide
  have hdescent : baseEnd_4876409 < baseStart_4876409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876426 : List Nat := [3, 1, 2, 3, 1, 3, 3, 7]
def baseStart_4876426 : Nat := 118140960795 + 4876426 * 2 ^ 59
def prefixEnd_4876426 : Nat := 4983230072969 + 3 ^ 40 * 4876426 * 2
def baseEnd_4876426 : Nat := 92738904225253451649953

theorem tailTrace_4876426 : CollatzResearch.WordTrace tailWord_4876426 prefixEnd_4876426 92738904225253451649953 := by
  unfold tailWord_4876426
  simp only [CollatzResearch.WordTrace]
  refine ⟨44464466957887226025286283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118571911887699269400763421 44464466957887226025286283)
  ·
    refine ⟨66696700436830839037929425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44464466957887226025286283 66696700436830839037929425)
    ·
      refine ⟨50022525327623129278447069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66696700436830839037929425 50022525327623129278447069)
      ·
        refine ⟨18758446997858673479417651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50022525327623129278447069 18758446997858673479417651)
        ·
          refine ⟨28137670496788010219126477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18758446997858673479417651 28137670496788010219126477)
          ·
            refine ⟨10551626436295503832172429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28137670496788010219126477 10551626436295503832172429)
            ·
              refine ⟨3956859913610813937064661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10551626436295503832172429 3956859913610813937064661)
              ·
                refine ⟨92738904225253451649953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3956859913610813937064661 92738904225253451649953)
                ·
                  rfl

theorem cell23_4876426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 3, 7].length) (baseStart_4876426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876426 prefixEnd_4876426 := by exact prefixLift 4876426
  have htrace : WordTrace (prefixWord ++ tailWord_4876426) baseStart_4876426 baseEnd_4876426 := by
    simpa [prefixWord, tailWord_4876426, baseEnd_4876426] using wordTrace_append hprefix tailTrace_4876426
  have hstable : (prefixWord ++ tailWord_4876426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876426).length < 2 ^ (prefixWord ++ tailWord_4876426).sum := by decide
  have hdescent : baseEnd_4876426 < baseStart_4876426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876479 : List Nat := [1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 5]
def baseStart_4876479 : Nat := 118140960795 + 4876479 * 2 ^ 59
def prefixEnd_4876479 : Nat := 4983230072969 + 3 ^ 40 * 4876479 * 2
def baseEnd_4876479 : Nat := 2503977628556531487185987

theorem tailTrace_4876479 : CollatzResearch.WordTrace tailWord_4876479 prefixEnd_4876479 2503977628556531487185987 := by
  unfold tailWord_4876479
  simp only [CollatzResearch.WordTrace]
  refine ⟨177859800900356894152824491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118573200600237929435216327 177859800900356894152824491)
  ·
    refine ⟨266789701350535341229236737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177859800900356894152824491 266789701350535341229236737)
    ·
      refine ⟨200092276012901505921927553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266789701350535341229236737 200092276012901505921927553)
      ·
        refine ⟨150069207009676129441445665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200092276012901505921927553 150069207009676129441445665)
        ·
          refine ⟨112551905257257097081084249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150069207009676129441445665 112551905257257097081084249)
          ·
            refine ⟨84413928942942822810813187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112551905257257097081084249 84413928942942822810813187)
            ·
              refine ⟨126620893414414234216219781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84413928942942822810813187 126620893414414234216219781)
              ·
                refine ⟨23741417515202668915541209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126620893414414234216219781 23741417515202668915541209)
                ·
                  refine ⟨17806063136402001686655907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23741417515202668915541209 17806063136402001686655907)
                  ·
                    refine ⟨26709094704603002529983861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17806063136402001686655907 26709094704603002529983861)
                    ·
                      refine ⟨2503977628556531487185987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26709094704603002529983861 2503977628556531487185987)
                      ·
                        rfl

theorem cell23_4876479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 1, 5].length) (baseStart_4876479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876479 prefixEnd_4876479 := by exact prefixLift 4876479
  have htrace : WordTrace (prefixWord ++ tailWord_4876479) baseStart_4876479 baseEnd_4876479 := by
    simpa [prefixWord, tailWord_4876479, baseEnd_4876479] using wordTrace_append hprefix tailTrace_4876479
  have hstable : (prefixWord ++ tailWord_4876479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876479).length < 2 ^ (prefixWord ++ tailWord_4876479).sum := by decide
  have hdescent : baseEnd_4876479 < baseStart_4876479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876480 : List Nat := [2, 1, 1, 2, 5, 2, 2, 2, 1, 3, 2]
def baseStart_4876480 : Nat := 118140960795 + 4876480 * 2 ^ 59
def prefixEnd_4876480 : Nat := 4983230072969 + 3 ^ 40 * 4876480 * 2
def baseEnd_4876480 : Nat := 2503978142037185983273483

theorem tailTrace_4876480 : CollatzResearch.WordTrace tailWord_4876480 prefixEnd_4876480 2503978142037185983273483 := by
  unfold tailWord_4876480
  simp only [CollatzResearch.WordTrace]
  refine ⟨88929918686676635661805447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118573224915568847549073929 88929918686676635661805447)
  ·
    refine ⟨133394878030014953492708171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88929918686676635661805447 133394878030014953492708171)
    ·
      refine ⟨200092317045022430239062257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133394878030014953492708171 200092317045022430239062257)
      ·
        refine ⟨150069237783766822679296693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200092317045022430239062257 150069237783766822679296693)
        ·
          refine ⟨14068991042228139626184065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150069237783766822679296693 14068991042228139626184065)
          ·
            refine ⟨10551743281671104719638049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14068991042228139626184065 10551743281671104719638049)
            ·
              refine ⟨7913807461253328539728537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10551743281671104719638049 7913807461253328539728537)
              ·
                refine ⟨5935355595939996404796403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7913807461253328539728537 5935355595939996404796403)
                ·
                  refine ⟨8903033393909994607194605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5935355595939996404796403 8903033393909994607194605)
                  ·
                    refine ⟨3338637522716247977697977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8903033393909994607194605 3338637522716247977697977)
                    ·
                      refine ⟨2503978142037185983273483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3338637522716247977697977 2503978142037185983273483)
                      ·
                        rfl

theorem cell23_4876480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 2, 2, 1, 3, 2].length) (baseStart_4876480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876480 prefixEnd_4876480 := by exact prefixLift 4876480
  have htrace : WordTrace (prefixWord ++ tailWord_4876480) baseStart_4876480 baseEnd_4876480 := by
    simpa [prefixWord, tailWord_4876480, baseEnd_4876480] using wordTrace_append hprefix tailTrace_4876480
  have hstable : (prefixWord ++ tailWord_4876480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876480).length < 2 ^ (prefixWord ++ tailWord_4876480).sum := by decide
  have hdescent : baseEnd_4876480 < baseStart_4876480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876489 : List Nat := [1, 2, 1, 1, 2, 1, 1, 4, 4, 2, 4]
def baseStart_4876489 : Nat := 118140960795 + 4876489 * 2 ^ 59
def prefixEnd_4876489 : Nat := 4983230072969 + 3 ^ 40 * 4876489 * 2
def baseEnd_4876489 : Nat := 2503982763363076448060941

theorem tailTrace_4876489 : CollatzResearch.WordTrace tailWord_4876489 prefixEnd_4876489 2503982763363076448060941 := by
  unfold tailWord_4876489
  simp only [CollatzResearch.WordTrace]
  refine ⟨177860165630320665860688521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118573443753547110573792347 177860165630320665860688521)
  ·
    refine ⟨133395124222740499395516391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177860165630320665860688521 133395124222740499395516391)
    ·
      refine ⟨200092686334110749093274587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133395124222740499395516391 200092686334110749093274587)
      ·
        refine ⟨300139029501166123639911881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200092686334110749093274587 300139029501166123639911881)
        ·
          refine ⟨225104272125874592729933911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300139029501166123639911881 225104272125874592729933911)
          ·
            refine ⟨337656408188811889094900867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225104272125874592729933911 337656408188811889094900867)
            ·
              refine ⟨506484612283217833642351301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337656408188811889094900867 506484612283217833642351301)
              ·
                refine ⟨94965864803103343807940869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 506484612283217833642351301 94965864803103343807940869)
                ·
                  refine ⟨17806099650581876963988913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94965864803103343807940869 17806099650581876963988913)
                  ·
                    refine ⟨13354574737936407722991685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17806099650581876963988913 13354574737936407722991685)
                    ·
                      refine ⟨2503982763363076448060941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13354574737936407722991685 2503982763363076448060941)
                      ·
                        rfl

theorem cell23_4876489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 4, 4, 2, 4].length) (baseStart_4876489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876489 prefixEnd_4876489 := by exact prefixLift 4876489
  have htrace : WordTrace (prefixWord ++ tailWord_4876489) baseStart_4876489 baseEnd_4876489 := by
    simpa [prefixWord, tailWord_4876489, baseEnd_4876489] using wordTrace_append hprefix tailTrace_4876489
  have hstable : (prefixWord ++ tailWord_4876489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876489).length < 2 ^ (prefixWord ++ tailWord_4876489).sum := by decide
  have hdescent : baseEnd_4876489 < baseStart_4876489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876526 : List Nat := [4, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3]
def baseStart_4876526 : Nat := 118140960795 + 4876526 * 2 ^ 59
def prefixEnd_4876526 : Nat := 4983230072969 + 3 ^ 40 * 4876526 * 2
def baseEnd_4876526 : Nat := 2504001762147292803298271

theorem tailTrace_4876526 : CollatzResearch.WordTrace tailWord_4876526 prefixEnd_4876526 2504001762147292803298271 := by
  unfold tailWord_4876526
  simp only [CollatzResearch.WordTrace]
  refine ⟨22232689391398327647473179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118574343420791080786523621 22232689391398327647473179)
  ·
    refine ⟨33349034087097491471209769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22232689391398327647473179 33349034087097491471209769)
    ·
      refine ⟨25011775565323118603407327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33349034087097491471209769 25011775565323118603407327)
      ·
        refine ⟨37517663347984677905110991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25011775565323118603407327 37517663347984677905110991)
        ·
          refine ⟨56276495021977016857666487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37517663347984677905110991 56276495021977016857666487)
          ·
            refine ⟨84414742532965525286499731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56276495021977016857666487 84414742532965525286499731)
            ·
              refine ⟨126622113799448287929749597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84414742532965525286499731 126622113799448287929749597)
              ·
                refine ⟨47483292674793107973656099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126622113799448287929749597 47483292674793107973656099)
                ·
                  refine ⟨71224939012189661960484149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47483292674793107973656099 71224939012189661960484149)
                  ·
                    refine ⟨6677338032392780808795389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71224939012189661960484149 6677338032392780808795389)
                    ·
                      refine ⟨2504001762147292803298271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6677338032392780808795389 2504001762147292803298271)
                      ·
                        rfl

theorem cell23_4876526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_4876526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876526 prefixEnd_4876526 := by exact prefixLift 4876526
  have htrace : WordTrace (prefixWord ++ tailWord_4876526) baseStart_4876526 baseEnd_4876526 := by
    simpa [prefixWord, tailWord_4876526, baseEnd_4876526] using wordTrace_append hprefix tailTrace_4876526
  have hstable : (prefixWord ++ tailWord_4876526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876526).length < 2 ^ (prefixWord ++ tailWord_4876526).sum := by decide
  have hdescent : baseEnd_4876526 < baseStart_4876526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876527 : List Nat := [1, 1, 2, 1, 6, 1, 4, 1, 2, 2, 2]
def baseStart_4876527 : Nat := 118140960795 + 4876527 * 2 ^ 59
def prefixEnd_4876527 : Nat := 4983230072969 + 3 ^ 40 * 4876527 * 2
def baseEnd_4876527 : Nat := 2504002275627947299385767

theorem tailTrace_4876527 : CollatzResearch.WordTrace tailWord_4876527 prefixEnd_4876527 2504002275627947299385767 := by
  unfold tailWord_4876527
  simp only [CollatzResearch.WordTrace]
  refine ⟨177861551604182998350571835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118574367736121998900381223 177861551604182998350571835)
  ·
    refine ⟨266792327406274497525857753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177861551604182998350571835 266792327406274497525857753)
    ·
      refine ⟨200094245554705873144393315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266792327406274497525857753 200094245554705873144393315)
      ·
        refine ⟨300141368332058809716589973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200094245554705873144393315 300141368332058809716589973)
        ·
          refine ⟨14069126640565256705465155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 300141368332058809716589973 14069126640565256705465155)
          ·
            refine ⟨21103689960847885058197733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14069126640565256705465155 21103689960847885058197733)
            ·
              refine ⟨3956941867658978448412075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21103689960847885058197733 3956941867658978448412075)
              ·
                refine ⟨5935412801488467672618113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3956941867658978448412075 5935412801488467672618113)
                ·
                  refine ⟨4451559601116350754463585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5935412801488467672618113 4451559601116350754463585)
                  ·
                    refine ⟨3338669700837263065847689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4451559601116350754463585 3338669700837263065847689)
                    ·
                      refine ⟨2504002275627947299385767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3338669700837263065847689 2504002275627947299385767)
                      ·
                        rfl

theorem cell23_4876527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 4, 1, 2, 2, 2].length) (baseStart_4876527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876527 prefixEnd_4876527 := by exact prefixLift 4876527
  have htrace : WordTrace (prefixWord ++ tailWord_4876527) baseStart_4876527 baseEnd_4876527 := by
    simpa [prefixWord, tailWord_4876527, baseEnd_4876527] using wordTrace_append hprefix tailTrace_4876527
  have hstable : (prefixWord ++ tailWord_4876527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876527).length < 2 ^ (prefixWord ++ tailWord_4876527).sum := by decide
  have hdescent : baseEnd_4876527 < baseStart_4876527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876529 : List Nat := [1, 2, 2, 2, 2, 1, 2, 1, 3, 7]
def baseStart_4876529 : Nat := 118140960795 + 4876529 * 2 ^ 59
def prefixEnd_4876529 : Nat := 4983230072969 + 3 ^ 40 * 4876529 * 2
def baseEnd_4876529 : Nat := 834667767529752097186919

theorem tailTrace_4876529 : CollatzResearch.WordTrace tailWord_4876529 prefixEnd_4876529 834667767529752097186919 := by
  unfold tailWord_4876529
  simp only [CollatzResearch.WordTrace]
  refine ⟨177861624550175752692144641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118574416366783835128096427 177861624550175752692144641)
  ·
    refine ⟨133396218412631814519108481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177861624550175752692144641 133396218412631814519108481)
    ·
      refine ⟨100047163809473860889331361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133396218412631814519108481 100047163809473860889331361)
      ·
        refine ⟨75035372857105395666998521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100047163809473860889331361 75035372857105395666998521)
        ·
          refine ⟨56276529642829046750248891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75035372857105395666998521 56276529642829046750248891)
          ·
            refine ⟨84414794464243570125373337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56276529642829046750248891 84414794464243570125373337)
            ·
              refine ⟨63311095848182677594030003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84414794464243570125373337 63311095848182677594030003)
              ·
                refine ⟨94966643772274016391045005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63311095848182677594030003 94966643772274016391045005)
                ·
                  refine ⟨35612491414602756146641877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94966643772274016391045005 35612491414602756146641877)
                  ·
                    refine ⟨834667767529752097186919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35612491414602756146641877 834667767529752097186919)
                    ·
                      rfl

theorem cell23_4876529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 1, 3, 7].length) (baseStart_4876529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876529 prefixEnd_4876529 := by exact prefixLift 4876529
  have htrace : WordTrace (prefixWord ++ tailWord_4876529) baseStart_4876529 baseEnd_4876529 := by
    simpa [prefixWord, tailWord_4876529, baseEnd_4876529] using wordTrace_append hprefix tailTrace_4876529
  have hstable : (prefixWord ++ tailWord_4876529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876529).length < 2 ^ (prefixWord ++ tailWord_4876529).sum := by decide
  have hdescent : baseEnd_4876529 < baseStart_4876529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876626 : List Nat := [3, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_4876626 : Nat := 118140960795 + 4876626 * 2 ^ 59
def prefixEnd_4876626 : Nat := 4983230072969 + 3 ^ 40 * 4876626 * 2
def baseEnd_4876626 : Nat := 2504053110212742412047811

theorem tailTrace_4876626 : CollatzResearch.WordTrace tailWord_4876626 prefixEnd_4876626 2504053110212742412047811 := by
  unfold tailWord_4876626
  simp only [CollatzResearch.WordTrace]
  refine ⟨44466290607706084564606433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118576774953882892172283821 44466290607706084564606433)
  ·
    refine ⟨33349717955779563423454825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44466290607706084564606433 33349717955779563423454825)
    ·
      refine ⟨25012288466834672567591119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33349717955779563423454825 25012288466834672567591119)
      ·
        refine ⟨37518432700252008851386679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25012288466834672567591119 37518432700252008851386679)
        ·
          refine ⟨56277649050378013277080019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37518432700252008851386679 56277649050378013277080019)
          ·
            refine ⟨84416473575567019915620029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56277649050378013277080019 84416473575567019915620029)
            ·
              refine ⟨31656177590837632468357511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84416473575567019915620029 31656177590837632468357511)
              ·
                refine ⟨47484266386256448702536267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31656177590837632468357511 47484266386256448702536267)
                ·
                  refine ⟨71226399579384673053804401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47484266386256448702536267 71226399579384673053804401)
                  ·
                    refine ⟨53419799684538504790353301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71226399579384673053804401 53419799684538504790353301)
                    ·
                      refine ⟨2504053110212742412047811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53419799684538504790353301 2504053110212742412047811)
                      ·
                        rfl

theorem cell23_4876626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_4876626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876626 prefixEnd_4876626 := by exact prefixLift 4876626
  have htrace : WordTrace (prefixWord ++ tailWord_4876626) baseStart_4876626 baseEnd_4876626 := by
    simpa [prefixWord, tailWord_4876626, baseEnd_4876626] using wordTrace_append hprefix tailTrace_4876626
  have hstable : (prefixWord ++ tailWord_4876626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876626).length < 2 ^ (prefixWord ++ tailWord_4876626).sum := by decide
  have hdescent : baseEnd_4876626 < baseStart_4876626 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876640 : List Nat := [2, 1, 1, 3, 5, 1, 3, 1, 6]
def baseStart_4876640 : Nat := 118140960795 + 4876640 * 2 ^ 59
def prefixEnd_4876640 : Nat := 4983230072969 + 3 ^ 40 * 4876640 * 2
def baseEnd_4876640 : Nat := 278228922104656150808083

theorem tailTrace_4876640 : CollatzResearch.WordTrace tailWord_4876640 prefixEnd_4876640 278228922104656150808083 := by
  unfold tailWord_4876640
  simp only [CollatzResearch.WordTrace]
  refine ⟨88932836526386809324717687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118577115368515745766290249 88932836526386809324717687)
  ·
    refine ⟨133399254789580213987076531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88932836526386809324717687 133399254789580213987076531)
    ·
      refine ⟨200098882184370320980614797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133399254789580213987076531 200098882184370320980614797)
      ·
        refine ⟨75037080819138870367730549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200098882184370320980614797 75037080819138870367730549)
        ·
          refine ⟨7034726326794269096974739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75037080819138870367730549 7034726326794269096974739)
          ·
            refine ⟨10552089490191403645462109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7034726326794269096974739 10552089490191403645462109)
            ·
              refine ⟨3957033558821776367048291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10552089490191403645462109 3957033558821776367048291)
              ·
                refine ⟨5935550338232664550572437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3957033558821776367048291 5935550338232664550572437)
                ·
                  refine ⟨278228922104656150808083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5935550338232664550572437 278228922104656150808083)
                  ·
                    rfl

theorem cell23_4876640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 6].length) (baseStart_4876640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876640 prefixEnd_4876640 := by exact prefixLift 4876640
  have htrace : WordTrace (prefixWord ++ tailWord_4876640) baseStart_4876640 baseEnd_4876640 := by
    simpa [prefixWord, tailWord_4876640, baseEnd_4876640] using wordTrace_append hprefix tailTrace_4876640
  have hstable : (prefixWord ++ tailWord_4876640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876640).length < 2 ^ (prefixWord ++ tailWord_4876640).sum := by decide
  have hdescent : baseEnd_4876640 < baseStart_4876640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876643 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 3, 5, 2]
def baseStart_4876643 : Nat := 118140960795 + 4876643 * 2 ^ 59
def prefixEnd_4876643 : Nat := 4983230072969 + 3 ^ 40 * 4876643 * 2
def baseEnd_4876643 : Nat := 2504061839383868845535233

theorem tailTrace_4876643 : CollatzResearch.WordTrace tailWord_4876643 prefixEnd_4876643 2504061839383868845535233 := by
  unfold tailWord_4876643
  simp only [CollatzResearch.WordTrace]
  refine ⟨177865782471762750161794583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118577188314508500107863055 177865782471762750161794583)
  ·
    refine ⟨266798673707644125242691875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177865782471762750161794583 266798673707644125242691875)
    ·
      refine ⟨400198010561466187864037813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266798673707644125242691875 400198010561466187864037813)
      ·
        refine ⟨37518563490137455112253545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 400198010561466187864037813 37518563490137455112253545)
        ·
          refine ⟨28138922617603091334190159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37518563490137455112253545 28138922617603091334190159)
          ·
            refine ⟨42208383926404637001285239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28138922617603091334190159 42208383926404637001285239)
            ·
              refine ⟨63312575889606955501927859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42208383926404637001285239 63312575889606955501927859)
              ·
                refine ⟨94968863834410433252891789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63312575889606955501927859 94968863834410433252891789)
                ·
                  refine ⟨35613323937903912469834421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94968863834410433252891789 35613323937903912469834421)
                  ·
                    refine ⟨3338749119178491794046977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35613323937903912469834421 3338749119178491794046977)
                    ·
                      refine ⟨2504061839383868845535233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3338749119178491794046977 2504061839383868845535233)
                      ·
                        rfl

theorem cell23_4876643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 3, 5, 2].length) (baseStart_4876643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876643 prefixEnd_4876643 := by exact prefixLift 4876643
  have htrace : WordTrace (prefixWord ++ tailWord_4876643) baseStart_4876643 baseEnd_4876643 := by
    simpa [prefixWord, tailWord_4876643, baseEnd_4876643] using wordTrace_append hprefix tailTrace_4876643
  have hstable : (prefixWord ++ tailWord_4876643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876643).length < 2 ^ (prefixWord ++ tailWord_4876643).sum := by decide
  have hdescent : baseEnd_4876643 < baseStart_4876643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876667 : List Nat := [1, 1, 1, 1, 1, 7, 3, 3, 1, 1, 3]
def baseStart_4876667 : Nat := 118140960795 + 4876667 * 2 ^ 59
def prefixEnd_4876667 : Nat := 4983230072969 + 3 ^ 40 * 4876667 * 2
def baseEnd_4876667 : Nat := 2504074162919576751635123

theorem tailTrace_4876667 : CollatzResearch.WordTrace tailWord_4876667 prefixEnd_4876667 2504074162919576751635123 := by
  unfold tailWord_4876667
  simp only [CollatzResearch.WordTrace]
  refine ⟨177866657823675802260668255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118577771882450534840445503 177866657823675802260668255)
  ·
    refine ⟨266799986735513703391002383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177866657823675802260668255 266799986735513703391002383)
    ·
      refine ⟨400199980103270555086503575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266799986735513703391002383 400199980103270555086503575)
      ·
        refine ⟨600299970154905832629755363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400199980103270555086503575 600299970154905832629755363)
        ·
          refine ⟨900449955232358748944633045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600299970154905832629755363 900449955232358748944633045)
          ·
            refine ⟨21104295825758408178389837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 900449955232358748944633045 21104295825758408178389837)
            ·
              refine ⟨7914110934659403066896189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21104295825758408178389837 7914110934659403066896189)
              ·
                refine ⟨2967791600497276150086071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7914110934659403066896189 2967791600497276150086071)
                ·
                  refine ⟨4451687400745914225129107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967791600497276150086071 4451687400745914225129107)
                  ·
                    refine ⟨6677531101118871337693661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4451687400745914225129107 6677531101118871337693661)
                    ·
                      refine ⟨2504074162919576751635123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6677531101118871337693661 2504074162919576751635123)
                      ·
                        rfl

theorem cell23_4876667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 3, 1, 1, 3].length) (baseStart_4876667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876667 prefixEnd_4876667 := by exact prefixLift 4876667
  have htrace : WordTrace (prefixWord ++ tailWord_4876667) baseStart_4876667 baseEnd_4876667 := by
    simpa [prefixWord, tailWord_4876667, baseEnd_4876667] using wordTrace_append hprefix tailTrace_4876667
  have hstable : (prefixWord ++ tailWord_4876667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876667).length < 2 ^ (prefixWord ++ tailWord_4876667).sum := by decide
  have hdescent : baseEnd_4876667 < baseStart_4876667 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876683 : List Nat := [1, 1, 1, 1, 4, 4, 2, 1, 4, 4]
def baseStart_4876683 : Nat := 118140960795 + 4876683 * 2 ^ 59
def prefixEnd_4876683 : Nat := 4983230072969 + 3 ^ 40 * 4876683 * 2
def baseEnd_4876683 : Nat := 834694126203349563011683

theorem tailTrace_4876683 : CollatzResearch.WordTrace tailWord_4876683 prefixEnd_4876683 834694126203349563011683 := by
  unfold tailWord_4876683
  simp only [CollatzResearch.WordTrace]
  refine ⟨177867241391617836993250703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118578160927745224662167135 177867241391617836993250703)
  ·
    refine ⟨266800862087426755489876055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177867241391617836993250703 266800862087426755489876055)
    ·
      refine ⟨400201293131140133234814083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266800862087426755489876055 400201293131140133234814083)
      ·
        refine ⟨600301939696710199852221125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400201293131140133234814083 600301939696710199852221125)
        ·
          refine ⟨112556613693133162472291461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 600301939696710199852221125 112556613693133162472291461)
          ·
            refine ⟨21104365067462467963554649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 112556613693133162472291461 21104365067462467963554649)
            ·
              refine ⟨15828273800596850972665987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21104365067462467963554649 15828273800596850972665987)
              ·
                refine ⟨23742410700895276458998981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15828273800596850972665987 23742410700895276458998981)
                ·
                  refine ⟨4451702006417864336062309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23742410700895276458998981 4451702006417864336062309)
                  ·
                    refine ⟨834694126203349563011683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4451702006417864336062309 834694126203349563011683)
                    ·
                      rfl

theorem cell23_4876683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 1, 4, 4].length) (baseStart_4876683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876683 prefixEnd_4876683 := by exact prefixLift 4876683
  have htrace : WordTrace (prefixWord ++ tailWord_4876683) baseStart_4876683 baseEnd_4876683 := by
    simpa [prefixWord, tailWord_4876683, baseEnd_4876683] using wordTrace_append hprefix tailTrace_4876683
  have hstable : (prefixWord ++ tailWord_4876683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876683).length < 2 ^ (prefixWord ++ tailWord_4876683).sum := by decide
  have hdescent : baseEnd_4876683 < baseStart_4876683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876684 : List Nat := [2, 2, 1, 2, 1, 5, 3, 2, 1, 1, 3]
def baseStart_4876684 : Nat := 118140960795 + 4876684 * 2 ^ 59
def prefixEnd_4876684 : Nat := 4983230072969 + 3 ^ 40 * 4876684 * 2
def baseEnd_4876684 : Nat := 2504082892090703185122545

theorem tailTrace_4876684 : CollatzResearch.WordTrace tailWord_4876684 prefixEnd_4876684 2504082892090703185122545 := by
  unfold tailWord_4876684
  simp only [CollatzResearch.WordTrace]
  refine ⟨88933638932307107082018553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118578185243076142776024737 88933638932307107082018553)
  ·
    refine ⟨66700229199230330311513915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88933638932307107082018553 66700229199230330311513915)
    ·
      refine ⟨100050343798845495467270873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66700229199230330311513915 100050343798845495467270873)
      ·
        refine ⟨75037757849134121600453155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100050343798845495467270873 75037757849134121600453155)
        ·
          refine ⟨112556636773701182400679733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75037757849134121600453155 112556636773701182400679733)
          ·
            refine ⟨10552184697534485850063725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112556636773701182400679733 10552184697534485850063725)
            ·
              refine ⟨3957069261575432193773897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10552184697534485850063725 3957069261575432193773897)
              ·
                refine ⟨2967801946181574145330423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3957069261575432193773897 2967801946181574145330423)
                ·
                  refine ⟨4451702919272361217995635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2967801946181574145330423 4451702919272361217995635)
                  ·
                    refine ⟨6677554378908541826993453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4451702919272361217995635 6677554378908541826993453)
                    ·
                      refine ⟨2504082892090703185122545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6677554378908541826993453 2504082892090703185122545)
                      ·
                        rfl

theorem cell23_4876684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 3, 2, 1, 1, 3].length) (baseStart_4876684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876684 prefixEnd_4876684 := by exact prefixLift 4876684
  have htrace : WordTrace (prefixWord ++ tailWord_4876684) baseStart_4876684 baseEnd_4876684 := by
    simpa [prefixWord, tailWord_4876684, baseEnd_4876684] using wordTrace_append hprefix tailTrace_4876684
  have hstable : (prefixWord ++ tailWord_4876684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876684).length < 2 ^ (prefixWord ++ tailWord_4876684).sum := by decide
  have hdescent : baseEnd_4876684 < baseStart_4876684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876693 : List Nat := [1, 3, 2, 1, 1, 2, 1, 4, 3, 2, 3]
def baseStart_4876693 : Nat := 118140960795 + 4876693 * 2 ^ 59
def prefixEnd_4876693 : Nat := 4983230072969 + 3 ^ 40 * 4876693 * 2
def baseEnd_4876693 : Nat := 2504087513416593649910003

theorem tailTrace_4876693 : CollatzResearch.WordTrace tailWord_4876693 prefixEnd_4876693 2504087513416593649910003 := by
  unfold tailWord_4876693
  simp only [CollatzResearch.WordTrace]
  refine ⟨177867606121581608701114733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118578404081054405800743155 177867606121581608701114733)
  ·
    refine ⟨66700352295593103262918025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177867606121581608701114733 66700352295593103262918025)
    ·
      refine ⟨50025264221694827447188519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66700352295593103262918025 50025264221694827447188519)
      ·
        refine ⟨75037896332542241170782779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50025264221694827447188519 75037896332542241170782779)
        ·
          refine ⟨112556844498813361756174169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75037896332542241170782779 112556844498813361756174169)
          ·
            refine ⟨84417633374110021317130627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112556844498813361756174169 84417633374110021317130627)
            ·
              refine ⟨126626450061165031975695941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84417633374110021317130627 126626450061165031975695941)
              ·
                refine ⟨23742459386468443495442989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126626450061165031975695941 23742459386468443495442989)
                ·
                  refine ⟨8903422269925666310791121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23742459386468443495442989 8903422269925666310791121)
                  ·
                    refine ⟨6677566702444249733093341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8903422269925666310791121 6677566702444249733093341)
                    ·
                      refine ⟨2504087513416593649910003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6677566702444249733093341 2504087513416593649910003)
                      ·
                        rfl

theorem cell23_4876693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_4876693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876693 prefixEnd_4876693 := by exact prefixLift 4876693
  have htrace : WordTrace (prefixWord ++ tailWord_4876693) baseStart_4876693 baseEnd_4876693 := by
    simpa [prefixWord, tailWord_4876693, baseEnd_4876693] using wordTrace_append hprefix tailTrace_4876693
  have hstable : (prefixWord ++ tailWord_4876693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876693).length < 2 ^ (prefixWord ++ tailWord_4876693).sum := by decide
  have hdescent : baseEnd_4876693 < baseStart_4876693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876703 : List Nat := [1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 4]
def baseStart_4876703 : Nat := 118140960795 + 4876703 * 2 ^ 59
def prefixEnd_4876703 : Nat := 4983230072969 + 3 ^ 40 * 4876703 * 2
def baseEnd_4876703 : Nat := 2504092648223138610784957

theorem tailTrace_4876703 : CollatzResearch.WordTrace tailWord_4876703 prefixEnd_4876703 2504092648223138610784957 := by
  unfold tailWord_4876703
  simp only [CollatzResearch.WordTrace]
  refine ⟨177867970851545380408978763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118578647234363586939319175 177867970851545380408978763)
  ·
    refine ⟨266801956277318070613468145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177867970851545380408978763 266801956277318070613468145)
    ·
      refine ⟨200101467207988552960101109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266801956277318070613468145 200101467207988552960101109)
      ·
        refine ⟨18759512550748926840009479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200101467207988552960101109 18759512550748926840009479)
        ·
          refine ⟨28139268826123390260014219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18759512550748926840009479 28139268826123390260014219)
          ·
            refine ⟨42208903239185085390021329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28139268826123390260014219 42208903239185085390021329)
            ·
              refine ⟨31656677429388814042515997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42208903239185085390021329 31656677429388814042515997)
              ·
                refine ⟨11871254036020805265943499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31656677429388814042515997 11871254036020805265943499)
                ·
                  refine ⟨17806881054031207898915249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11871254036020805265943499 17806881054031207898915249)
                  ·
                    refine ⟨13355160790523405924186437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17806881054031207898915249 13355160790523405924186437)
                    ·
                      refine ⟨2504092648223138610784957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13355160790523405924186437 2504092648223138610784957)
                      ·
                        rfl

theorem cell23_4876703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 4].length) (baseStart_4876703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876703 prefixEnd_4876703 := by exact prefixLift 4876703
  have htrace : WordTrace (prefixWord ++ tailWord_4876703) baseStart_4876703 baseEnd_4876703 := by
    simpa [prefixWord, tailWord_4876703, baseEnd_4876703] using wordTrace_append hprefix tailTrace_4876703
  have hstable : (prefixWord ++ tailWord_4876703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876703).length < 2 ^ (prefixWord ++ tailWord_4876703).sum := by decide
  have hdescent : baseEnd_4876703 < baseStart_4876703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876727 : List Nat := [1, 1, 3, 1, 3, 4, 3, 1, 1, 2, 3]
def baseStart_4876727 : Nat := 118140960795 + 4876727 * 2 ^ 59
def prefixEnd_4876727 : Nat := 4983230072969 + 3 ^ 40 * 4876727 * 2
def baseEnd_4876727 : Nat := 2504104971758846516884847

theorem tailTrace_4876727 : CollatzResearch.WordTrace tailWord_4876727 prefixEnd_4876727 2504104971758846516884847 := by
  unfold tailWord_4876727
  simp only [CollatzResearch.WordTrace]
  refine ⟨177868846203458432507852435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118579230802305621671901623 177868846203458432507852435)
  ·
    refine ⟨266803269305187648761778653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177868846203458432507852435 266803269305187648761778653)
    ·
      refine ⟨100051225989445368285666995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266803269305187648761778653 100051225989445368285666995)
      ·
        refine ⟨150076838984168052428500493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100051225989445368285666995 150076838984168052428500493)
        ·
          refine ⟨56278814619063019660687685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150076838984168052428500493 56278814619063019660687685)
          ·
            refine ⟨10552277741074316186378941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56278814619063019660687685 10552277741074316186378941)
            ·
              refine ⟨3957104152902868569892103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10552277741074316186378941 3957104152902868569892103)
              ·
                refine ⟨5935656229354302854838155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3957104152902868569892103 5935656229354302854838155)
                ·
                  refine ⟨8903484344031454282257233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5935656229354302854838155 8903484344031454282257233)
                  ·
                    refine ⟨6677613258023590711692925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8903484344031454282257233 6677613258023590711692925)
                    ·
                      refine ⟨2504104971758846516884847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6677613258023590711692925 2504104971758846516884847)
                      ·
                        rfl

theorem cell23_4876727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 4, 3, 1, 1, 2, 3].length) (baseStart_4876727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876727 prefixEnd_4876727 := by exact prefixLift 4876727
  have htrace : WordTrace (prefixWord ++ tailWord_4876727) baseStart_4876727 baseEnd_4876727 := by
    simpa [prefixWord, tailWord_4876727, baseEnd_4876727] using wordTrace_append hprefix tailTrace_4876727
  have hstable : (prefixWord ++ tailWord_4876727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876727).length < 2 ^ (prefixWord ++ tailWord_4876727).sum := by decide
  have hdescent : baseEnd_4876727 < baseStart_4876727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876757 : List Nat := [1, 3, 2, 3, 1, 2, 2, 3, 2, 1, 3]
def baseStart_4876757 : Nat := 118140960795 + 4876757 * 2 ^ 59
def prefixEnd_4876757 : Nat := 4983230072969 + 3 ^ 40 * 4876757 * 2
def baseEnd_4876757 : Nat := 2504120376178481399509709

theorem tailTrace_4876757 : CollatzResearch.WordTrace tailWord_4876757 prefixEnd_4876757 2504120376178481399509709 := by
  unfold tailWord_4876757
  simp only [CollatzResearch.WordTrace]
  refine ⟨177869940393349747631444525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118579960262233165087629683 177869940393349747631444525)
  ·
    refine ⟨66701227647506155361791697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177869940393349747631444525 66701227647506155361791697)
    ·
      refine ⟨50025920735629616521343773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66701227647506155361791697 50025920735629616521343773)
      ·
        refine ⟨18759720275861106195503915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50025920735629616521343773 18759720275861106195503915)
        ·
          refine ⟨28139580413791659293255873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18759720275861106195503915 28139580413791659293255873)
          ·
            refine ⟨21104685310343744469941905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28139580413791659293255873 21104685310343744469941905)
            ·
              refine ⟨15828513982757808352456429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21104685310343744469941905 15828513982757808352456429)
              ·
                refine ⟨5935692743534178132171161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15828513982757808352456429 5935692743534178132171161)
                ·
                  refine ⟨4451769557650633599128371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5935692743534178132171161 4451769557650633599128371)
                  ·
                    refine ⟨6677654336475950398692557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4451769557650633599128371 6677654336475950398692557)
                    ·
                      refine ⟨2504120376178481399509709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6677654336475950398692557 2504120376178481399509709)
                      ·
                        rfl

theorem cell23_4876757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_4876757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876757 prefixEnd_4876757 := by exact prefixLift 4876757
  have htrace : WordTrace (prefixWord ++ tailWord_4876757) baseStart_4876757 baseEnd_4876757 := by
    simpa [prefixWord, tailWord_4876757, baseEnd_4876757] using wordTrace_append hprefix tailTrace_4876757
  have hstable : (prefixWord ++ tailWord_4876757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876757).length < 2 ^ (prefixWord ++ tailWord_4876757).sum := by decide
  have hdescent : baseEnd_4876757 < baseStart_4876757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876780 : List Nat := [2, 2, 1, 1, 2, 1, 3, 4, 1, 4, 2]
def baseStart_4876780 : Nat := 118140960795 + 4876780 * 2 ^ 59
def prefixEnd_4876780 : Nat := 4983230072969 + 3 ^ 40 * 4876780 * 2
def baseEnd_4876780 : Nat := 2504132186233534809522103

theorem tailTrace_4876780 : CollatzResearch.WordTrace tailWord_4876780 prefixEnd_4876780 2504132186233534809522103 := by
  unfold tailWord_4876780
  simp only [CollatzResearch.WordTrace]
  refine ⟨88935389636133211279765897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118580519514844281706354529 88935389636133211279765897)
  ·
    refine ⟨66701542227099908459824423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88935389636133211279765897 66701542227099908459824423)
    ·
      refine ⟨100052313340649862689736635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66701542227099908459824423 100052313340649862689736635)
      ·
        refine ⟨150078470010974794034604953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100052313340649862689736635 150078470010974794034604953)
        ·
          refine ⟨112558852508231095525953715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150078470010974794034604953 112558852508231095525953715)
          ·
            refine ⟨168838278762346643288930573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112558852508231095525953715 168838278762346643288930573)
            ·
              refine ⟨63314354535879991233348965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168838278762346643288930573 63314354535879991233348965)
              ·
                refine ⟨11871441475477498356252931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63314354535879991233348965 11871441475477498356252931)
                ·
                  refine ⟨17807162213216247534379397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11871441475477498356252931 17807162213216247534379397)
                  ·
                    refine ⟨3338842914978046412696137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17807162213216247534379397 3338842914978046412696137)
                    ·
                      refine ⟨2504132186233534809522103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3338842914978046412696137 2504132186233534809522103)
                      ·
                        rfl

theorem cell23_4876780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 4, 2].length) (baseStart_4876780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876780 prefixEnd_4876780 := by exact prefixLift 4876780
  have htrace : WordTrace (prefixWord ++ tailWord_4876780) baseStart_4876780 baseEnd_4876780 := by
    simpa [prefixWord, tailWord_4876780, baseEnd_4876780] using wordTrace_append hprefix tailTrace_4876780
  have hstable : (prefixWord ++ tailWord_4876780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876780).length < 2 ^ (prefixWord ++ tailWord_4876780).sum := by decide
  have hdescent : baseEnd_4876780 < baseStart_4876780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876793 : List Nat := [1, 2, 1, 3, 1, 2, 3, 2, 2, 2, 4]
def baseStart_4876793 : Nat := 118140960795 + 4876793 * 2 ^ 59
def prefixEnd_4876793 : Nat := 4983230072969 + 3 ^ 40 * 4876793 * 2
def baseEnd_4876793 : Nat := 2504138861482043258659543

theorem tailTrace_4876793 : CollatzResearch.WordTrace tailWord_4876793 prefixEnd_4876793 2504138861482043258659543 := by
  unfold tailWord_4876793
  simp only [CollatzResearch.WordTrace]
  refine ⟨177871253421219325779755033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118580835614146217186503355 177871253421219325779755033)
  ·
    refine ⟨133403440065914494334816275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177871253421219325779755033 133403440065914494334816275)
    ·
      refine ⟨200105160098871741502224413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133403440065914494334816275 200105160098871741502224413)
      ·
        refine ⟨75039435037076903063334155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200105160098871741502224413 75039435037076903063334155)
        ·
          refine ⟨112559152555615354595001233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75039435037076903063334155 112559152555615354595001233)
          ·
            refine ⟨84419364416711515946250925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112559152555615354595001233 84419364416711515946250925)
            ·
              refine ⟨31657261656266818479844097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84419364416711515946250925 31657261656266818479844097)
              ·
                refine ⟨23742946242200113859883073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31657261656266818479844097 23742946242200113859883073)
                ·
                  refine ⟨17807209681650085394912305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23742946242200113859883073 17807209681650085394912305)
                  ·
                    refine ⟨13355407261237564046184229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17807209681650085394912305 13355407261237564046184229)
                    ·
                      refine ⟨2504138861482043258659543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13355407261237564046184229 2504138861482043258659543)
                      ·
                        rfl

theorem cell23_4876793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 3, 2, 2, 2, 4].length) (baseStart_4876793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876793 prefixEnd_4876793 := by exact prefixLift 4876793
  have htrace : WordTrace (prefixWord ++ tailWord_4876793) baseStart_4876793 baseEnd_4876793 := by
    simpa [prefixWord, tailWord_4876793, baseEnd_4876793] using wordTrace_append hprefix tailTrace_4876793
  have hstable : (prefixWord ++ tailWord_4876793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876793).length < 2 ^ (prefixWord ++ tailWord_4876793).sum := by decide
  have hdescent : baseEnd_4876793 < baseStart_4876793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876797 : List Nat := [1, 4, 1, 1, 1, 3, 3, 1, 4, 2, 2]
def baseStart_4876797 : Nat := 118140960795 + 4876797 * 2 ^ 59
def prefixEnd_4876797 : Nat := 4983230072969 + 3 ^ 40 * 4876797 * 2
def baseEnd_4876797 : Nat := 2504140915404661243009525

theorem tailTrace_4876797 : CollatzResearch.WordTrace tailWord_4876797 prefixEnd_4876797 2504140915404661243009525 := by
  unfold tailWord_4876797
  simp only [CollatzResearch.WordTrace]
  refine ⟨177871399313204834462900645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118580932875469889641933763 177871399313204834462900645)
  ·
    refine ⟨33350887371225906461793871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177871399313204834462900645 33350887371225906461793871)
    ·
      refine ⟨50026331056838859692690807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33350887371225906461793871 50026331056838859692690807)
      ·
        refine ⟨75039496585258289539036211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50026331056838859692690807 75039496585258289539036211)
        ·
          refine ⟨112559244877887434308554317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75039496585258289539036211 112559244877887434308554317)
          ·
            refine ⟨42209716829207787865707869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112559244877887434308554317 42209716829207787865707869)
            ·
              refine ⟨15828643810952920449640451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42209716829207787865707869 15828643810952920449640451)
              ·
                refine ⟨23742965716429380674460677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15828643810952920449640451 23742965716429380674460677)
                ·
                  refine ⟨4451806071830508876461377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23742965716429380674460677 4451806071830508876461377)
                  ·
                    refine ⟨3338854553872881657346033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4451806071830508876461377 3338854553872881657346033)
                    ·
                      refine ⟨2504140915404661243009525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3338854553872881657346033 2504140915404661243009525)
                      ·
                        rfl

theorem cell23_4876797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 3, 1, 4, 2, 2].length) (baseStart_4876797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876797 prefixEnd_4876797 := by exact prefixLift 4876797
  have htrace : WordTrace (prefixWord ++ tailWord_4876797) baseStart_4876797 baseEnd_4876797 := by
    simpa [prefixWord, tailWord_4876797, baseEnd_4876797] using wordTrace_append hprefix tailTrace_4876797
  have hstable : (prefixWord ++ tailWord_4876797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876797).length < 2 ^ (prefixWord ++ tailWord_4876797).sum := by decide
  have hdescent : baseEnd_4876797 < baseStart_4876797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876803 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 7]
def baseStart_4876803 : Nat := 118140960795 + 4876803 * 2 ^ 59
def prefixEnd_4876803 : Nat := 4983230072969 + 3 ^ 40 * 4876803 * 2
def baseEnd_4876803 : Nat := 278238221809843135503833

theorem tailTrace_4876803 : CollatzResearch.WordTrace tailWord_4876803 prefixEnd_4876803 278238221809843135503833 := by
  unfold tailWord_4876803
  simp only [CollatzResearch.WordTrace]
  refine ⟨177871618151183097487619063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118581078767455398325079375 177871618151183097487619063)
  ·
    refine ⟨266807427226774646231428595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177871618151183097487619063 266807427226774646231428595)
    ·
      refine ⟨400211140840161969347142893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266807427226774646231428595 400211140840161969347142893)
      ·
        refine ⟨150079177815060738505178585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 400211140840161969347142893 150079177815060738505178585)
        ·
          refine ⟨112559383361295553878883939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150079177815060738505178585 112559383361295553878883939)
          ·
            refine ⟨168839075041943330818325909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112559383361295553878883939 168839075041943330818325909)
            ·
              refine ⟨7914331642591093632109027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 168839075041943330818325909 7914331642591093632109027)
              ·
                refine ⟨11871497463886640448163541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7914331642591093632109027 11871497463886640448163541)
                ·
                  refine ⟨278238221809843135503833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11871497463886640448163541 278238221809843135503833)
                  ·
                    rfl

theorem cell23_4876803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 7].length) (baseStart_4876803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876803 prefixEnd_4876803 := by exact prefixLift 4876803
  have htrace : WordTrace (prefixWord ++ tailWord_4876803) baseStart_4876803 baseEnd_4876803 := by
    simpa [prefixWord, tailWord_4876803, baseEnd_4876803] using wordTrace_append hprefix tailTrace_4876803
  have hstable : (prefixWord ++ tailWord_4876803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876803).length < 2 ^ (prefixWord ++ tailWord_4876803).sum := by decide
  have hdescent : baseEnd_4876803 < baseStart_4876803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876814 : List Nat := [4, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2]
def baseStart_4876814 : Nat := 118140960795 + 4876814 * 2 ^ 59
def prefixEnd_4876814 : Nat := 4983230072969 + 3 ^ 40 * 4876814 * 2
def baseEnd_4876814 : Nat := 2504149644575787676496947

theorem tailTrace_4876814 : CollatzResearch.WordTrace tailWord_4876814 prefixEnd_4876814 2504149644575787676496947 := by
  unfold tailWord_4876814
  simp only [CollatzResearch.WordTrace]
  refine ⟨22234002419267905795783687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118581346236095497577512997 22234002419267905795783687)
  ·
    refine ⟨33351003628901858693675531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22234002419267905795783687 33351003628901858693675531)
    ·
      refine ⟨50026505443352788040513297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33351003628901858693675531 50026505443352788040513297)
      ·
        refine ⟨37519879082514591030384973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50026505443352788040513297 37519879082514591030384973)
        ·
          refine ⟨14069954655942971636394365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37519879082514591030384973 14069954655942971636394365)
          ·
            refine ⟨5276232995978614363647887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14069954655942971636394365 5276232995978614363647887)
            ·
              refine ⟨7914349493967921545471831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5276232995978614363647887 7914349493967921545471831)
              ·
                refine ⟨11871524240951882318207747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7914349493967921545471831 11871524240951882318207747)
                ·
                  refine ⟨17807286361427823477311621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11871524240951882318207747 17807286361427823477311621)
                  ·
                    refine ⟨3338866192767716901995929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17807286361427823477311621 3338866192767716901995929)
                    ·
                      refine ⟨2504149644575787676496947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3338866192767716901995929 2504149644575787676496947)
                      ·
                        rfl

theorem cell23_4876814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_4876814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876814 prefixEnd_4876814 := by exact prefixLift 4876814
  have htrace : WordTrace (prefixWord ++ tailWord_4876814) baseStart_4876814 baseEnd_4876814 := by
    simpa [prefixWord, tailWord_4876814, baseEnd_4876814] using wordTrace_append hprefix tailTrace_4876814
  have hstable : (prefixWord ++ tailWord_4876814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876814).length < 2 ^ (prefixWord ++ tailWord_4876814).sum := by decide
  have hdescent : baseEnd_4876814 < baseStart_4876814 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876833 : List Nat := [1, 2, 3, 2, 2, 1, 1, 3, 1, 7]
def baseStart_4876833 : Nat := 118140960795 + 4876833 * 2 ^ 59
def prefixEnd_4876833 : Nat := 4983230072969 + 3 ^ 40 * 4876833 * 2
def baseEnd_4876833 : Nat := 834719800236074367386453

theorem tailTrace_4876833 : CollatzResearch.WordTrace tailWord_4876833 prefixEnd_4876833 834719800236074367386453 := by
  unfold tailWord_4876833
  simp only [CollatzResearch.WordTrace]
  refine ⟨177872712341074412611211153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118581808227382941740807435 177872712341074412611211153)
  ·
    refine ⟨133404534255805809458408365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177872712341074412611211153 133404534255805809458408365)
    ·
      refine ⟨50026700345927178546903137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133404534255805809458408365 50026700345927178546903137)
      ·
        refine ⟨37520025259445383910177353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50026700345927178546903137 37520025259445383910177353)
        ·
          refine ⟨28140018944584037932633015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37520025259445383910177353 28140018944584037932633015)
          ·
            refine ⟨42210028416876056898949523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28140018944584037932633015 42210028416876056898949523)
            ·
              refine ⟨63315042625314085348424285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42210028416876056898949523 63315042625314085348424285)
              ·
                refine ⟨23743140984492782005659107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63315042625314085348424285 23743140984492782005659107)
                ·
                  refine ⟨35614711476739173008488661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23743140984492782005659107 35614711476739173008488661)
                  ·
                    refine ⟨834719800236074367386453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35614711476739173008488661 834719800236074367386453)
                    ·
                      rfl

theorem cell23_4876833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 3, 1, 7].length) (baseStart_4876833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876833 prefixEnd_4876833 := by exact prefixLift 4876833
  have htrace : WordTrace (prefixWord ++ tailWord_4876833) baseStart_4876833 baseEnd_4876833 := by
    simpa [prefixWord, tailWord_4876833, baseEnd_4876833] using wordTrace_append hprefix tailTrace_4876833
  have hstable : (prefixWord ++ tailWord_4876833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876833).length < 2 ^ (prefixWord ++ tailWord_4876833).sum := by decide
  have hdescent : baseEnd_4876833 < baseStart_4876833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4876860 : List Nat := [2, 2, 2, 2, 3, 2, 1, 1, 1, 2, 5]
def baseStart_4876860 : Nat := 118140960795 + 4876860 * 2 ^ 59
def prefixEnd_4876860 : Nat := 4983230072969 + 3 ^ 40 * 4876860 * 2
def baseEnd_4876860 : Nat := 2504173264685894496521735

theorem tailTrace_4876860 : CollatzResearch.WordTrace tailWord_4876860 prefixEnd_4876860 2504173264685894496521735 := by
  unfold tailWord_4876860
  simp only [CollatzResearch.WordTrace]
  refine ⟨88936848555988298111222017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118582464741317730814962689 88936848555988298111222017)
  ·
    refine ⟨66702636416991223583416513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88936848555988298111222017 66702636416991223583416513)
    ·
      refine ⟨50026977312743417687562385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66702636416991223583416513 50026977312743417687562385)
      ·
        refine ⟨37520232984557563265671789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50026977312743417687562385 37520232984557563265671789)
        ·
          refine ⟨14070087369209086224626921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37520232984557563265671789 14070087369209086224626921)
          ·
            refine ⟨10552565526906814668470191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14070087369209086224626921 10552565526906814668470191)
            ·
              refine ⟨15828848290360222002705287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10552565526906814668470191 15828848290360222002705287)
              ·
                refine ⟨23743272435540333004057931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15828848290360222002705287 23743272435540333004057931)
                ·
                  refine ⟨35614908653310499506086897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23743272435540333004057931 35614908653310499506086897)
                  ·
                    refine ⟨26711181489982874629565173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35614908653310499506086897 26711181489982874629565173)
                    ·
                      refine ⟨2504173264685894496521735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26711181489982874629565173 2504173264685894496521735)
                      ·
                        rfl

theorem cell23_4876860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_4876860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4876860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4876860 prefixEnd_4876860 := by exact prefixLift 4876860
  have htrace : WordTrace (prefixWord ++ tailWord_4876860) baseStart_4876860 baseEnd_4876860 := by
    simpa [prefixWord, tailWord_4876860, baseEnd_4876860] using wordTrace_append hprefix tailTrace_4876860
  have hstable : (prefixWord ++ tailWord_4876860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4876860).length < 2 ^ (prefixWord ++ tailWord_4876860).sum := by decide
  have hdescent : baseEnd_4876860 < baseStart_4876860 := by decide
  rcases family_descends (prefixWord ++ tailWord_4876860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877000 : List Nat := [2, 1, 3, 1, 2, 4, 1, 9]
def baseStart_4877000 : Nat := 118140960795 + 4877000 * 2 ^ 59
def prefixEnd_4877000 : Nat := 4983230072969 + 3 ^ 40 * 4877000 * 2
def baseEnd_4877000 : Nat := 92749820443611998102633

theorem tailTrace_4877000 : CollatzResearch.WordTrace tailWord_4877000 prefixEnd_4877000 92749820443611998102633 := by
  unfold tailWord_4877000
  simp only [CollatzResearch.WordTrace]
  refine ⟨88939401665734700066270227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118585868887646266755026969 88939401665734700066270227)
  ·
    refine ⟨133409102498602050099405341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88939401665734700066270227 133409102498602050099405341)
    ·
      refine ⟨50028413436975768787277003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133409102498602050099405341 50028413436975768787277003)
      ·
        refine ⟨75042620155463653180915505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50028413436975768787277003 75042620155463653180915505)
        ·
          refine ⟨56281965116597739885686629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75042620155463653180915505 56281965116597739885686629)
          ·
            refine ⟨10552868459362076228566243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56281965116597739885686629 10552868459362076228566243)
            ·
              refine ⟨15829302689043114342849365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10552868459362076228566243 15829302689043114342849365)
              ·
                refine ⟨92749820443611998102633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15829302689043114342849365 92749820443611998102633)
                ·
                  rfl

theorem cell23_4877000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 9].length) (baseStart_4877000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877000 prefixEnd_4877000 := by exact prefixLift 4877000
  have htrace : WordTrace (prefixWord ++ tailWord_4877000) baseStart_4877000 baseEnd_4877000 := by
    simpa [prefixWord, tailWord_4877000, baseEnd_4877000] using wordTrace_append hprefix tailTrace_4877000
  have hstable : (prefixWord ++ tailWord_4877000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877000).length < 2 ^ (prefixWord ++ tailWord_4877000).sum := by decide
  have hdescent : baseEnd_4877000 < baseStart_4877000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877045 : List Nat := [1, 3, 6, 1, 1, 2, 1, 2, 1, 1, 4]
def baseStart_4877045 : Nat := 118140960795 + 4877045 * 2 ^ 59
def prefixEnd_4877045 : Nat := 4983230072969 + 3 ^ 40 * 4877045 * 2
def baseEnd_4877045 : Nat := 2504268258606976272708385

theorem tailTrace_4877045 : CollatzResearch.WordTrace tailWord_4877045 prefixEnd_4877045 2504268258606976272708385 := by
  unfold tailWord_4877045
  simp only [CollatzResearch.WordTrace]
  refine ⟨177880444616306372817928589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118586963077537581878619059 177880444616306372817928589)
  ·
    refine ⟨66705166731114889806723221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177880444616306372817928589 66705166731114889806723221)
    ·
      refine ⟨3126804690521010459690151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 66705166731114889806723221 3126804690521010459690151)
      ·
        refine ⟨4690207035781515689535227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3126804690521010459690151 4690207035781515689535227)
        ·
          refine ⟨7035310553672273534302841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4690207035781515689535227 7035310553672273534302841)
          ·
            refine ⟨5276482915254205150727131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7035310553672273534302841 5276482915254205150727131)
            ·
              refine ⟨7914724372881307726090697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5276482915254205150727131 7914724372881307726090697)
              ·
                refine ⟨5936043279660980794568023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7914724372881307726090697 5936043279660980794568023)
                ·
                  refine ⟨8904064919491471191852035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5936043279660980794568023 8904064919491471191852035)
                  ·
                    refine ⟨13356097379237206787778053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8904064919491471191852035 13356097379237206787778053)
                    ·
                      refine ⟨2504268258606976272708385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13356097379237206787778053 2504268258606976272708385)
                      ·
                        rfl

theorem cell23_4877045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_4877045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877045 prefixEnd_4877045 := by exact prefixLift 4877045
  have htrace : WordTrace (prefixWord ++ tailWord_4877045) baseStart_4877045 baseEnd_4877045 := by
    simpa [prefixWord, tailWord_4877045, baseEnd_4877045] using wordTrace_append hprefix tailTrace_4877045
  have hstable : (prefixWord ++ tailWord_4877045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877045).length < 2 ^ (prefixWord ++ tailWord_4877045).sum := by decide
  have hdescent : baseEnd_4877045 < baseStart_4877045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877071 : List Nat := [1, 1, 2, 1, 1, 1, 9, 1, 1, 3, 2]
def baseStart_4877071 : Nat := 118140960795 + 4877071 * 2 ^ 59
def prefixEnd_4877071 : Nat := 4983230072969 + 3 ^ 40 * 4877071 * 2
def baseEnd_4877071 : Nat := 2504281609103993170983265

theorem tailTrace_4877071 : CollatzResearch.WordTrace tailWord_4877071 prefixEnd_4877071 2504281609103993170983265 := by
  unfold tailWord_4877071
  simp only [CollatzResearch.WordTrace]
  refine ⟨177881392914212179258375067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118587595276141452838916711 177881392914212179258375067)
  ·
    refine ⟨266822089371318268887562601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177881392914212179258375067 266822089371318268887562601)
    ·
      refine ⟨200116567028488701665671951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266822089371318268887562601 200116567028488701665671951)
      ·
        refine ⟨300174850542733052498507927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200116567028488701665671951 300174850542733052498507927)
        ·
          refine ⟨450262275814099578747761891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300174850542733052498507927 450262275814099578747761891)
          ·
            refine ⟨675393413721149368121642837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450262275814099578747761891 675393413721149368121642837)
            ·
              refine ⟨3957383283522359578837751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 675393413721149368121642837 3957383283522359578837751)
              ·
                refine ⟨5936074925283539368256627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3957383283522359578837751 5936074925283539368256627)
                ·
                  refine ⟨8904112387925309052384941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5936074925283539368256627 8904112387925309052384941)
                  ·
                    refine ⟨3339042145471990894644353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8904112387925309052384941 3339042145471990894644353)
                    ·
                      refine ⟨2504281609103993170983265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3339042145471990894644353 2504281609103993170983265)
                      ·
                        rfl

theorem cell23_4877071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 9, 1, 1, 3, 2].length) (baseStart_4877071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877071 prefixEnd_4877071 := by exact prefixLift 4877071
  have htrace : WordTrace (prefixWord ++ tailWord_4877071) baseStart_4877071 baseEnd_4877071 := by
    simpa [prefixWord, tailWord_4877071, baseEnd_4877071] using wordTrace_append hprefix tailTrace_4877071
  have hstable : (prefixWord ++ tailWord_4877071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877071).length < 2 ^ (prefixWord ++ tailWord_4877071).sum := by decide
  have hdescent : baseEnd_4877071 < baseStart_4877071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877080 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 2, 3, 6]
def baseStart_4877080 : Nat := 118140960795 + 4877080 * 2 ^ 59
def prefixEnd_4877080 : Nat := 4983230072969 + 3 ^ 40 * 4877080 * 2
def baseEnd_4877080 : Nat := 2504286230429883635770723

theorem tailTrace_4877080 : CollatzResearch.WordTrace tailWord_4877080 prefixEnd_4877080 2504286230429883635770723 := by
  unfold tailWord_4877080
  simp only [CollatzResearch.WordTrace]
  refine ⟨88940860585589786897726347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118587814114119715863635129 88940860585589786897726347)
  ·
    refine ⟨133411290878384680346589521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88940860585589786897726347 133411290878384680346589521)
    ·
      refine ⟨100058468158788510259942141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133411290878384680346589521 100058468158788510259942141)
      ·
        refine ⟨37521925559545691347478303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100058468158788510259942141 37521925559545691347478303)
        ·
          refine ⟨56282888339318537021217455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37521925559545691347478303 56282888339318537021217455)
          ·
            refine ⟨84424332508977805531826183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56282888339318537021217455 84424332508977805531826183)
            ·
              refine ⟨126636498763466708297739275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84424332508977805531826183 126636498763466708297739275)
              ·
                refine ⟨189954748145200062446608913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126636498763466708297739275 189954748145200062446608913)
                ·
                  refine ⟨142466061108900046834956685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 189954748145200062446608913 142466061108900046834956685)
                  ·
                    refine ⟨53424772915837517563108757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 142466061108900046834956685 53424772915837517563108757)
                    ·
                      refine ⟨2504286230429883635770723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53424772915837517563108757 2504286230429883635770723)
                      ·
                        rfl

theorem cell23_4877080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 2, 3, 6].length) (baseStart_4877080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877080 prefixEnd_4877080 := by exact prefixLift 4877080
  have htrace : WordTrace (prefixWord ++ tailWord_4877080) baseStart_4877080 baseEnd_4877080 := by
    simpa [prefixWord, tailWord_4877080, baseEnd_4877080] using wordTrace_append hprefix tailTrace_4877080
  have hstable : (prefixWord ++ tailWord_4877080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877080).length < 2 ^ (prefixWord ++ tailWord_4877080).sum := by decide
  have hdescent : baseEnd_4877080 < baseStart_4877080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877087 : List Nat := [1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 3]
def baseStart_4877087 : Nat := 118140960795 + 4877087 * 2 ^ 59
def prefixEnd_4877087 : Nat := 4983230072969 + 3 ^ 40 * 4877087 * 2
def baseEnd_4877087 : Nat := 2504289824794465108383191

theorem tailTrace_4877087 : CollatzResearch.WordTrace tailWord_4877087 prefixEnd_4877087 2504289824794465108383191 := by
  unfold tailWord_4877087
  simp only [CollatzResearch.WordTrace]
  refine ⟨177881976482154213990957515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118587984321436142660638343 177881976482154213990957515)
  ·
    refine ⟨266822964723231320986436273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177881976482154213990957515 266822964723231320986436273)
    ·
      refine ⟨200117223542423490739827205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266822964723231320986436273 200117223542423490739827205)
      ·
        refine ⟨37521979414204404513717601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200117223542423490739827205 37521979414204404513717601)
        ·
          refine ⟨28141484560653303385288201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37521979414204404513717601 28141484560653303385288201)
          ·
            refine ⟨21106113420489977538966151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28141484560653303385288201 21106113420489977538966151)
            ·
              refine ⟨31659170130734966308449227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21106113420489977538966151 31659170130734966308449227)
              ·
                refine ⟨47488755196102449462673841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31659170130734966308449227 47488755196102449462673841)
                ·
                  refine ⟨35616566397076837097005381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47488755196102449462673841 35616566397076837097005381)
                  ·
                    refine ⟨6678106199451906955688509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35616566397076837097005381 6678106199451906955688509)
                    ·
                      refine ⟨2504289824794465108383191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6678106199451906955688509 2504289824794465108383191)
                      ·
                        rfl

theorem cell23_4877087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 2, 4, 3].length) (baseStart_4877087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877087 prefixEnd_4877087 := by exact prefixLift 4877087
  have htrace : WordTrace (prefixWord ++ tailWord_4877087) baseStart_4877087 baseEnd_4877087 := by
    simpa [prefixWord, tailWord_4877087, baseEnd_4877087] using wordTrace_append hprefix tailTrace_4877087
  have hstable : (prefixWord ++ tailWord_4877087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877087).length < 2 ^ (prefixWord ++ tailWord_4877087).sum := by decide
  have hdescent : baseEnd_4877087 < baseStart_4877087 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877107 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 7]
def baseStart_4877107 : Nat := 118140960795 + 4877107 * 2 ^ 59
def prefixEnd_4877107 : Nat := 4983230072969 + 3 ^ 40 * 4877107 * 2
def baseEnd_4877107 : Nat := 278255566045283892237011

theorem tailTrace_4877107 : CollatzResearch.WordTrace tailWord_4877107 prefixEnd_4877107 278255566045283892237011 := by
  unfold tailWord_4877107
  simp only [CollatzResearch.WordTrace]
  refine ⟨177882705942081757406685575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118588470628054504937790383 177882705942081757406685575)
  ·
    refine ⟨266824058913122636110028363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177882705942081757406685575 266824058913122636110028363)
    ·
      refine ⟨400236088369683954165042545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266824058913122636110028363 400236088369683954165042545)
      ·
        refine ⟨300177066277262965623781909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400236088369683954165042545 300177066277262965623781909)
        ·
          refine ⟨14070799981746701513614777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 300177066277262965623781909 14070799981746701513614777)
          ·
            refine ⟨10553099986310026135211083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14070799981746701513614777 10553099986310026135211083)
            ·
              refine ⟨15829649979465039202816625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10553099986310026135211083 15829649979465039202816625)
              ·
                refine ⟨11872237484598779402112469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15829649979465039202816625 11872237484598779402112469)
                ·
                  refine ⟨278255566045283892237011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11872237484598779402112469 278255566045283892237011)
                  ·
                    rfl

theorem cell23_4877107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 7].length) (baseStart_4877107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877107 prefixEnd_4877107 := by exact prefixLift 4877107
  have htrace : WordTrace (prefixWord ++ tailWord_4877107) baseStart_4877107 baseEnd_4877107 := by
    simpa [prefixWord, tailWord_4877107, baseEnd_4877107] using wordTrace_append hprefix tailTrace_4877107
  have hstable : (prefixWord ++ tailWord_4877107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877107).length < 2 ^ (prefixWord ++ tailWord_4877107).sum := by decide
  have hdescent : baseEnd_4877107 < baseStart_4877107 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877157 : List Nat := [1, 3, 1, 3, 1, 1, 3, 2, 1, 3, 4]
def baseStart_4877157 : Nat := 118140960795 + 4877157 * 2 ^ 59
def prefixEnd_4877157 : Nat := 4983230072969 + 3 ^ 40 * 4877157 * 2
def baseEnd_4877157 : Nat := 2504325768440279834507869

theorem tailTrace_4877157 : CollatzResearch.WordTrace tailWord_4877157 prefixEnd_4877157 2504325768440279834507869 := by
  unfold tailWord_4877157
  simp only [CollatzResearch.WordTrace]
  refine ⟨177884529591900615946005725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118589686394600410630670483 177884529591900615946005725)
  ·
    refine ⟨66706698596962730979752147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177884529591900615946005725 66706698596962730979752147)
    ·
      refine ⟨100060047895444096469628221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66706698596962730979752147 100060047895444096469628221)
      ·
        refine ⟨37522517960791536176110583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100060047895444096469628221 37522517960791536176110583)
        ·
          refine ⟨56283776941187304264165875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37522517960791536176110583 56283776941187304264165875)
          ·
            refine ⟨84425665411780956396248813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56283776941187304264165875 84425665411780956396248813)
            ·
              refine ⟨31659624529417858648593305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84425665411780956396248813 31659624529417858648593305)
              ·
                refine ⟨23744718397063393986444979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31659624529417858648593305 23744718397063393986444979)
                ·
                  refine ⟨35617077595595090979667469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23744718397063393986444979 35617077595595090979667469)
                  ·
                    refine ⟨13356404098348159117375301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35617077595595090979667469 13356404098348159117375301)
                    ·
                      refine ⟨2504325768440279834507869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13356404098348159117375301 2504325768440279834507869)
                      ·
                        rfl

theorem cell23_4877157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_4877157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877157 prefixEnd_4877157 := by exact prefixLift 4877157
  have htrace : WordTrace (prefixWord ++ tailWord_4877157) baseStart_4877157 baseEnd_4877157 := by
    simpa [prefixWord, tailWord_4877157, baseEnd_4877157] using wordTrace_append hprefix tailTrace_4877157
  have hstable : (prefixWord ++ tailWord_4877157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877157).length < 2 ^ (prefixWord ++ tailWord_4877157).sum := by decide
  have hdescent : baseEnd_4877157 < baseStart_4877157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877227 : List Nat := [1, 1, 1, 1, 2, 1, 1, 7, 3, 5]
def baseStart_4877227 : Nat := 118140960795 + 4877227 * 2 ^ 59
def prefixEnd_4877227 : Nat := 4983230072969 + 3 ^ 40 * 4877227 * 2
def baseEnd_4877227 : Nat := 834787237362031520210849

theorem tailTrace_4877227 : CollatzResearch.WordTrace tailWord_4877227 prefixEnd_4877227 834787237362031520210849 := by
  unfold tailWord_4877227
  simp only [CollatzResearch.WordTrace]
  refine ⟨177887082701647017901053935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118591388467764678600702623 177887082701647017901053935)
  ·
    refine ⟨266830624052470526851580903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177887082701647017901053935 266830624052470526851580903)
    ·
      refine ⟨400245936078705790277371355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266830624052470526851580903 400245936078705790277371355)
      ·
        refine ⟨600368904118058685416057033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400245936078705790277371355 600368904118058685416057033)
        ·
          refine ⟨450276678088544014062042775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600368904118058685416057033 450276678088544014062042775)
          ·
            refine ⟨675415017132816021093064163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450276678088544014062042775 675415017132816021093064163)
            ·
              refine ⟨1013122525699224031639596245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675415017132816021093064163 1013122525699224031639596245)
              ·
                refine ⟨23745059196075563241553037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1013122525699224031639596245 23745059196075563241553037)
                ·
                  refine ⟨8904397198528336215582389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23745059196075563241553037 8904397198528336215582389)
                  ·
                    refine ⟨834787237362031520210849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8904397198528336215582389 834787237362031520210849)
                    ·
                      rfl

theorem cell23_4877227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 7, 3, 5].length) (baseStart_4877227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877227 prefixEnd_4877227 := by exact prefixLift 4877227
  have htrace : WordTrace (prefixWord ++ tailWord_4877227) baseStart_4877227 baseEnd_4877227 := by
    simpa [prefixWord, tailWord_4877227, baseEnd_4877227] using wordTrace_append hprefix tailTrace_4877227
  have hstable : (prefixWord ++ tailWord_4877227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877227).length < 2 ^ (prefixWord ++ tailWord_4877227).sum := by decide
  have hdescent : baseEnd_4877227 < baseStart_4877227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877264 : List Nat := [2, 1, 1, 1, 1, 2, 3, 2, 2, 6, 2]
def baseStart_4877264 : Nat := 118140960795 + 4877264 * 2 ^ 59
def prefixEnd_4877264 : Nat := 4983230072969 + 3 ^ 40 * 4877264 * 2
def baseEnd_4877264 : Nat := 2504380710870310915869877

theorem tailTrace_4877264 : CollatzResearch.WordTrace tailWord_4877264 prefixEnd_4877264 2504380710870310915869877 := by
  unfold tailWord_4877264
  simp only [CollatzResearch.WordTrace]
  refine ⟨88944216101256486610075423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118592288135008648813433897 88944216101256486610075423)
  ·
    refine ⟨133416324151884729915113135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88944216101256486610075423 133416324151884729915113135)
    ·
      refine ⟨200124486227827094872669703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133416324151884729915113135 200124486227827094872669703)
      ·
        refine ⟨300186729341740642309004555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200124486227827094872669703 300186729341740642309004555)
        ·
          refine ⟨450280094012610963463506833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300186729341740642309004555 450280094012610963463506833)
          ·
            refine ⟨337710070509458222597630125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450280094012610963463506833 337710070509458222597630125)
            ·
              refine ⟨126641276441046833474111297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337710070509458222597630125 126641276441046833474111297)
              ·
                refine ⟨94980957330785125105583473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126641276441046833474111297 94980957330785125105583473)
                ·
                  refine ⟨71235717998088843829187605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94980957330785125105583473 71235717998088843829187605)
                  ·
                    refine ⟨3339174281160414554493169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71235717998088843829187605 3339174281160414554493169)
                    ·
                      refine ⟨2504380710870310915869877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3339174281160414554493169 2504380710870310915869877)
                      ·
                        rfl

theorem cell23_4877264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 2, 2, 6, 2].length) (baseStart_4877264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877264 prefixEnd_4877264 := by exact prefixLift 4877264
  have htrace : WordTrace (prefixWord ++ tailWord_4877264) baseStart_4877264 baseEnd_4877264 := by
    simpa [prefixWord, tailWord_4877264, baseEnd_4877264] using wordTrace_append hprefix tailTrace_4877264
  have hstable : (prefixWord ++ tailWord_4877264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877264).length < 2 ^ (prefixWord ++ tailWord_4877264).sum := by decide
  have hdescent : baseEnd_4877264 < baseStart_4877264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877274 : List Nat := [3, 1, 1, 2, 4, 1, 1, 3, 1, 6]
def baseStart_4877274 : Nat := 118140960795 + 4877274 * 2 ^ 59
def prefixEnd_4877274 : Nat := 4983230072969 + 3 ^ 40 * 4877274 * 2
def baseEnd_4877274 : Nat := 834795281892285292248277

theorem tailTrace_4877274 : CollatzResearch.WordTrace tailWord_4877274 prefixEnd_4877274 834795281892285292248277 := by
  unfold tailWord_4877274
  simp only [CollatzResearch.WordTrace]
  refine ⟨44472199233119186232003719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118592531288317829952009917 44472199233119186232003719)
  ·
    refine ⟨66708298849678779348005579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44472199233119186232003719 66708298849678779348005579)
    ·
      refine ⟨100062448274518169022008369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66708298849678779348005579 100062448274518169022008369)
      ·
        refine ⟨75046836205888626766506277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100062448274518169022008369 75046836205888626766506277)
        ·
          refine ⟨14071281788604117518719927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75046836205888626766506277 14071281788604117518719927)
          ·
            refine ⟨21106922682906176278079891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14071281788604117518719927 21106922682906176278079891)
            ·
              refine ⟨31660384024359264417119837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21106922682906176278079891 31660384024359264417119837)
              ·
                refine ⟨11872644009134724156419939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31660384024359264417119837 11872644009134724156419939)
                ·
                  refine ⟨17808966013702086234629909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11872644009134724156419939 17808966013702086234629909)
                  ·
                    refine ⟨834795281892285292248277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17808966013702086234629909 834795281892285292248277)
                    ·
                      rfl

theorem cell23_4877274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_4877274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877274 prefixEnd_4877274 := by exact prefixLift 4877274
  have htrace : WordTrace (prefixWord ++ tailWord_4877274) baseStart_4877274 baseEnd_4877274 := by
    simpa [prefixWord, tailWord_4877274, baseEnd_4877274] using wordTrace_append hprefix tailTrace_4877274
  have hstable : (prefixWord ++ tailWord_4877274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877274).length < 2 ^ (prefixWord ++ tailWord_4877274).sum := by decide
  have hdescent : baseEnd_4877274 < baseStart_4877274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877307 : List Nat := [1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 6]
def baseStart_4877307 : Nat := 118140960795 + 4877307 * 2 ^ 59
def prefixEnd_4877307 : Nat := 4983230072969 + 3 ^ 40 * 4877307 * 2
def baseEnd_4877307 : Nat := 2504402790538454247632179

theorem tailTrace_4877307 : CollatzResearch.WordTrace tailWord_4877307 prefixEnd_4877307 2504402790538454247632179 := by
  unfold tailWord_4877307
  simp only [CollatzResearch.WordTrace]
  refine ⟨177890000541357191563966175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118593333694238127709310783 177890000541357191563966175)
  ·
    refine ⟨266835000812035787345949263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177890000541357191563966175 266835000812035787345949263)
    ·
      refine ⟨400252501218053681018923895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266835000812035787345949263 400252501218053681018923895)
      ·
        refine ⟨600378751827080521528385843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400252501218053681018923895 600378751827080521528385843)
        ·
          refine ⟨900568127740620782292578765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600378751827080521528385843 900568127740620782292578765)
          ·
            refine ⟨337713047902732793359717037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 900568127740620782292578765 337713047902732793359717037)
            ·
              refine ⟨126642392963524797509893889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337713047902732793359717037 126642392963524797509893889)
              ·
                refine ⟨94981794722643598132420417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 126642392963524797509893889 94981794722643598132420417)
                ·
                  refine ⟨71236346041982698599315313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94981794722643598132420417 71236346041982698599315313)
                  ·
                    refine ⟨53427259531487023949486485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71236346041982698599315313 53427259531487023949486485)
                    ·
                      refine ⟨2504402790538454247632179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53427259531487023949486485 2504402790538454247632179)
                      ·
                        rfl

theorem cell23_4877307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 2, 6].length) (baseStart_4877307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877307 prefixEnd_4877307 := by exact prefixLift 4877307
  have htrace : WordTrace (prefixWord ++ tailWord_4877307) baseStart_4877307 baseEnd_4877307 := by
    simpa [prefixWord, tailWord_4877307, baseEnd_4877307] using wordTrace_append hprefix tailTrace_4877307
  have hstable : (prefixWord ++ tailWord_4877307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877307).length < 2 ^ (prefixWord ++ tailWord_4877307).sum := by decide
  have hdescent : baseEnd_4877307 < baseStart_4877307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877308 : List Nat := [2, 2, 2, 1, 2, 5, 1, 2, 2, 4]
def baseStart_4877308 : Nat := 118140960795 + 4877308 * 2 ^ 59
def prefixEnd_4877308 : Nat := 4983230072969 + 3 ^ 40 * 4877308 * 2
def baseEnd_4877308 : Nat := 834801101339702914573225

theorem tailTrace_4877308 : CollatzResearch.WordTrace tailWord_4877308 prefixEnd_4877308 834801101339702914573225 := by
  unfold tailWord_4877308
  simp only [CollatzResearch.WordTrace]
  refine ⟨88945018507176784367376289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118593358009569045823168385 88945018507176784367376289)
  ·
    refine ⟨66708763880382588275532217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88945018507176784367376289 66708763880382588275532217)
    ·
      refine ⟨50031572910286941206649163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66708763880382588275532217 50031572910286941206649163)
      ·
        refine ⟨75047359365430411809973745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50031572910286941206649163 75047359365430411809973745)
        ·
          refine ⟨56285519524072808857480309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75047359365430411809973745 56285519524072808857480309)
          ·
            refine ⟨5276767455381825830388779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56285519524072808857480309 5276767455381825830388779)
            ·
              refine ⟨7915151183072738745583169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5276767455381825830388779 7915151183072738745583169)
              ·
                refine ⟨5936363387304554059187377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7915151183072738745583169 5936363387304554059187377)
                ·
                  refine ⟨4452272540478415544390533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5936363387304554059187377 4452272540478415544390533)
                  ·
                    refine ⟨834801101339702914573225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4452272540478415544390533 834801101339702914573225)
                    ·
                      rfl

theorem cell23_4877308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 2, 2, 4].length) (baseStart_4877308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877308 prefixEnd_4877308 := by exact prefixLift 4877308
  have htrace : WordTrace (prefixWord ++ tailWord_4877308) baseStart_4877308 baseEnd_4877308 := by
    simpa [prefixWord, tailWord_4877308, baseEnd_4877308] using wordTrace_append hprefix tailTrace_4877308
  have hstable : (prefixWord ++ tailWord_4877308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877308).length < 2 ^ (prefixWord ++ tailWord_4877308).sum := by decide
  have hdescent : baseEnd_4877308 < baseStart_4877308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877348 : List Nat := [2, 3, 1, 4, 1, 1, 1, 2, 4, 1, 3]
def baseStart_4877348 : Nat := 118140960795 + 4877348 * 2 ^ 59
def prefixEnd_4877348 : Nat := 4983230072969 + 3 ^ 40 * 4877348 * 2
def baseEnd_4877348 : Nat := 2504423843245288587219491

theorem tailTrace_4877348 : CollatzResearch.WordTrace tailWord_4877348 prefixEnd_4877348 2504423843245288587219491 := by
  unfold tailWord_4877348
  simp only [CollatzResearch.WordTrace]
  refine ⟨88945747967104327783104349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118594330622805770377472465 88945747967104327783104349)
  ·
    refine ⟨33354655487664122918664131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88945747967104327783104349 33354655487664122918664131)
    ·
      refine ⟨50031983231496184377996197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33354655487664122918664131 50031983231496184377996197)
      ·
        refine ⟨9380996855905534570874287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50031983231496184377996197 9380996855905534570874287)
        ·
          refine ⟨14071495283858301856311431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9380996855905534570874287 14071495283858301856311431)
          ·
            refine ⟨21107242925787452784467147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14071495283858301856311431 21107242925787452784467147)
            ·
              refine ⟨31660864388681179176700721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21107242925787452784467147 31660864388681179176700721)
              ·
                refine ⟨23745648291510884382525541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31660864388681179176700721 23745648291510884382525541)
                ·
                  refine ⟨4452309054658290821723539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23745648291510884382525541 4452309054658290821723539)
                  ·
                    refine ⟨6678463581987436232585309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4452309054658290821723539 6678463581987436232585309)
                    ·
                      refine ⟨2504423843245288587219491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6678463581987436232585309 2504423843245288587219491)
                      ·
                        rfl

theorem cell23_4877348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_4877348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877348 prefixEnd_4877348 := by exact prefixLift 4877348
  have htrace : WordTrace (prefixWord ++ tailWord_4877348) baseStart_4877348 baseEnd_4877348 := by
    simpa [prefixWord, tailWord_4877348, baseEnd_4877348] using wordTrace_append hprefix tailTrace_4877348
  have hstable : (prefixWord ++ tailWord_4877348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877348).length < 2 ^ (prefixWord ++ tailWord_4877348).sum := by decide
  have hdescent : baseEnd_4877348 < baseStart_4877348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877382 : List Nat := [6, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_4877382 : Nat := 118140960795 + 4877382 * 2 ^ 59
def prefixEnd_4877382 : Nat := 4983230072969 + 3 ^ 40 * 4877382 * 2
def baseEnd_4877382 : Nat := 2504441301587541454194335

theorem tailTrace_4877382 : CollatzResearch.WordTrace tailWord_4877382 prefixEnd_4877382 2504441301587541454194335 := by
  unfold tailWord_4877382
  simp only [CollatzResearch.WordTrace]
  refine ⟨5559148000502671230404575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118595157344056986248630933 5559148000502671230404575)
  ·
    refine ⟨8338722000754006845606863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5559148000502671230404575 8338722000754006845606863)
    ·
      refine ⟨12508083001131010268410295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8338722000754006845606863 12508083001131010268410295)
      ·
        refine ⟨18762124501696515402615443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12508083001131010268410295 18762124501696515402615443)
        ·
          refine ⟨28143186752544773103923165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18762124501696515402615443 28143186752544773103923165)
          ·
            refine ⟨10553695032204289913971187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28143186752544773103923165 10553695032204289913971187)
            ·
              refine ⟨15830542548306434870956781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10553695032204289913971187 15830542548306434870956781)
              ·
                refine ⟨5936453455614913076608793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15830542548306434870956781 5936453455614913076608793)
                ·
                  refine ⟨4452340091711184807456595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5936453455614913076608793 4452340091711184807456595)
                  ·
                    refine ⟨6678510137566777211184893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4452340091711184807456595 6678510137566777211184893)
                    ·
                      refine ⟨2504441301587541454194335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6678510137566777211184893 2504441301587541454194335)
                      ·
                        rfl

theorem cell23_4877382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_4877382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877382 prefixEnd_4877382 := by exact prefixLift 4877382
  have htrace : WordTrace (prefixWord ++ tailWord_4877382) baseStart_4877382 baseEnd_4877382 := by
    simpa [prefixWord, tailWord_4877382, baseEnd_4877382] using wordTrace_append hprefix tailTrace_4877382
  have hstable : (prefixWord ++ tailWord_4877382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877382).length < 2 ^ (prefixWord ++ tailWord_4877382).sum := by decide
  have hdescent : baseEnd_4877382 < baseStart_4877382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877384 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 1, 4, 4]
def baseStart_4877384 : Nat := 118140960795 + 4877384 * 2 ^ 59
def prefixEnd_4877384 : Nat := 4983230072969 + 3 ^ 40 * 4877384 * 2
def baseEnd_4877384 : Nat := 2504442328548850446369325

theorem tailTrace_4877384 : CollatzResearch.WordTrace tailWord_4877384 prefixEnd_4877384 2504442328548850446369325 := by
  unfold tailWord_4877384
  simp only [CollatzResearch.WordTrace]
  refine ⟨88946404481039116857259603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118595205974718822476346137 88946404481039116857259603)
  ·
    refine ⟨133419606721558675285889405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88946404481039116857259603 133419606721558675285889405)
    ·
      refine ⟨50032352520584503232208527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133419606721558675285889405 50032352520584503232208527)
      ·
        refine ⟨75048528780876754848312791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50032352520584503232208527 75048528780876754848312791)
        ·
          refine ⟨112572793171315132272469187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75048528780876754848312791 112572793171315132272469187)
          ·
            refine ⟨168859189756972698408703781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112572793171315132272469187 168859189756972698408703781)
            ·
              refine ⟨31661098079432380951631959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168859189756972698408703781 31661098079432380951631959)
              ·
                refine ⟨47491647119148571427447939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31661098079432380951631959 47491647119148571427447939)
                ·
                  refine ⟨71237470678722857141171909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47491647119148571427447939 71237470678722857141171909)
                  ·
                    refine ⟨13357025752260535713969733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71237470678722857141171909 13357025752260535713969733)
                    ·
                      refine ⟨2504442328548850446369325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13357025752260535713969733 2504442328548850446369325)
                      ·
                        rfl

theorem cell23_4877384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 1, 4, 4].length) (baseStart_4877384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877384 prefixEnd_4877384 := by exact prefixLift 4877384
  have htrace : WordTrace (prefixWord ++ tailWord_4877384) baseStart_4877384 baseEnd_4877384 := by
    simpa [prefixWord, tailWord_4877384, baseEnd_4877384] using wordTrace_append hprefix tailTrace_4877384
  have hstable : (prefixWord ++ tailWord_4877384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877384).length < 2 ^ (prefixWord ++ tailWord_4877384).sum := by decide
  have hdescent : baseEnd_4877384 < baseStart_4877384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877411 : List Nat := [1, 1, 1, 5, 1, 1, 1, 7, 5]
def baseStart_4877411 : Nat := 118140960795 + 4877411 * 2 ^ 59
def prefixEnd_4877411 : Nat := 4983230072969 + 3 ^ 40 * 4877411 * 2
def baseEnd_4877411 : Nat := 278272910280724648970189

theorem tailTrace_4877411 : CollatzResearch.WordTrace tailWord_4877411 prefixEnd_4877411 278272910280724648970189 := by
  unfold tailWord_4877411
  simp only [CollatzResearch.WordTrace]
  refine ⟨177893793732980417325752087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118595862488653611550501391 177893793732980417325752087)
  ·
    refine ⟨266840690599470625988628131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177893793732980417325752087 266840690599470625988628131)
    ·
      refine ⟨400261035899205938982942197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266840690599470625988628131 400261035899205938982942197)
      ·
        refine ⟨37524472115550556779650831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 400261035899205938982942197 37524472115550556779650831)
        ·
          refine ⟨56286708173325835169476247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37524472115550556779650831 56286708173325835169476247)
          ·
            refine ⟨84430062259988752754214371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56286708173325835169476247 84430062259988752754214371)
            ·
              refine ⟨126645093389983129131321557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84430062259988752754214371 126645093389983129131321557)
              ·
                refine ⟨2968244376327729589015349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 126645093389983129131321557 2968244376327729589015349)
                ·
                  refine ⟨278272910280724648970189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2968244376327729589015349 278272910280724648970189)
                  ·
                    rfl

theorem cell23_4877411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 7, 5].length) (baseStart_4877411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877411 prefixEnd_4877411 := by exact prefixLift 4877411
  have htrace : WordTrace (prefixWord ++ tailWord_4877411) baseStart_4877411 baseEnd_4877411 := by
    simpa [prefixWord, tailWord_4877411, baseEnd_4877411] using wordTrace_append hprefix tailTrace_4877411
  have hstable : (prefixWord ++ tailWord_4877411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877411).length < 2 ^ (prefixWord ++ tailWord_4877411).sum := by decide
  have hdescent : baseEnd_4877411 < baseStart_4877411 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877422 : List Nat := [4, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2]
def baseStart_4877422 : Nat := 118140960795 + 4877422 * 2 ^ 59
def prefixEnd_4877422 : Nat := 4983230072969 + 3 ^ 40 * 4877422 * 2
def baseEnd_4877422 : Nat := 2504461840813721297694151

theorem tailTrace_4877422 : CollatzResearch.WordTrace tailWord_4877422 prefixEnd_4877422 2504461840813721297694151 := by
  unfold tailWord_4877422
  simp only [CollatzResearch.WordTrace]
  refine ⟨22236774366992570775550315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118596129957293710802935013 22236774366992570775550315)
  ·
    refine ⟨33355161550488856163325473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22236774366992570775550315 33355161550488856163325473)
    ·
      refine ⟨25016371162866642122494105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33355161550488856163325473 25016371162866642122494105)
      ·
        refine ⟨18762278372149981591870579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25016371162866642122494105 18762278372149981591870579)
        ·
          refine ⟨28143417558224972387805869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18762278372149981591870579 28143417558224972387805869)
          ·
            refine ⟨10553781584334364645427201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28143417558224972387805869 10553781584334364645427201)
            ·
              refine ⟨7915336188250773484070401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10553781584334364645427201 7915336188250773484070401)
              ·
                refine ⟨5936502141188080113052801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7915336188250773484070401 5936502141188080113052801)
                ·
                  refine ⟨4452376605891060084789601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5936502141188080113052801 4452376605891060084789601)
                  ·
                    refine ⟨3339282454418295063592201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4452376605891060084789601 3339282454418295063592201)
                    ·
                      refine ⟨2504461840813721297694151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3339282454418295063592201 2504461840813721297694151)
                      ·
                        rfl

theorem cell23_4877422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_4877422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877422 prefixEnd_4877422 := by exact prefixLift 4877422
  have htrace : WordTrace (prefixWord ++ tailWord_4877422) baseStart_4877422 baseEnd_4877422 := by
    simpa [prefixWord, tailWord_4877422, baseEnd_4877422] using wordTrace_append hprefix tailTrace_4877422
  have hstable : (prefixWord ++ tailWord_4877422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877422).length < 2 ^ (prefixWord ++ tailWord_4877422).sum := by decide
  have hdescent : baseEnd_4877422 < baseStart_4877422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877431 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 1, 7, 2]
def baseStart_4877431 : Nat := 118140960795 + 4877431 * 2 ^ 59
def prefixEnd_4877431 : Nat := 4983230072969 + 3 ^ 40 * 4877431 * 2
def baseEnd_4877431 : Nat := 2504466462139611762481609

theorem tailTrace_4877431 : CollatzResearch.WordTrace tailWord_4877431 prefixEnd_4877431 2504466462139611762481609 := by
  unfold tailWord_4877431
  simp only [CollatzResearch.WordTrace]
  refine ⟨177894523192907960741480147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118596348795271973827653431 177894523192907960741480147)
  ·
    refine ⟨266841784789361941112220221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177894523192907960741480147 266841784789361941112220221)
    ·
      refine ⟨100065669296010727917082583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266841784789361941112220221 100065669296010727917082583)
      ·
        refine ⟨150098503944016091875623875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100065669296010727917082583 150098503944016091875623875)
        ·
          refine ⟨225147755916024137813435813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150098503944016091875623875 225147755916024137813435813)
          ·
            refine ⟨42215204234254525840019215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225147755916024137813435813 42215204234254525840019215)
            ·
              refine ⟨63322806351381788760028823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42215204234254525840019215 63322806351381788760028823)
              ·
                refine ⟨94984209527072683140043235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63322806351381788760028823 94984209527072683140043235)
                ·
                  refine ⟨142476314290609024710064853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94984209527072683140043235 142476314290609024710064853)
                  ·
                    refine ⟨3339288616186149016642145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 142476314290609024710064853 3339288616186149016642145)
                    ·
                      refine ⟨2504466462139611762481609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3339288616186149016642145 2504466462139611762481609)
                      ·
                        rfl

theorem cell23_4877431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 7, 2].length) (baseStart_4877431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877431 prefixEnd_4877431 := by exact prefixLift 4877431
  have htrace : WordTrace (prefixWord ++ tailWord_4877431) baseStart_4877431 baseEnd_4877431 := by
    simpa [prefixWord, tailWord_4877431, baseEnd_4877431] using wordTrace_append hprefix tailTrace_4877431
  have hstable : (prefixWord ++ tailWord_4877431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877431).length < 2 ^ (prefixWord ++ tailWord_4877431).sum := by decide
  have hdescent : baseEnd_4877431 < baseStart_4877431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877458 : List Nat := [3, 2, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_4877458 : Nat := 118140960795 + 4877458 * 2 ^ 59
def prefixEnd_4877458 : Nat := 4983230072969 + 3 ^ 40 * 4877458 * 2
def baseEnd_4877458 : Nat := 834826775372427718947995

theorem tailTrace_4877458 : CollatzResearch.WordTrace tailWord_4877458 prefixEnd_4877458 834826775372427718947995 := by
  unfold tailWord_4877458
  simp only [CollatzResearch.WordTrace]
  refine ⟨44473876990952536088178257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118597005309206762901808685 44473876990952536088178257)
  ·
    refine ⟨33355407743214402066133693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44473876990952536088178257 33355407743214402066133693)
    ·
      refine ⟨12508277903705400774800135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33355407743214402066133693 12508277903705400774800135)
      ·
        refine ⟨18762416855558101162200203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12508277903705400774800135 18762416855558101162200203)
        ·
          refine ⟨28143625283337151743300305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18762416855558101162200203 28143625283337151743300305)
          ·
            refine ⟨21107718962502863807475229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28143625283337151743300305 21107718962502863807475229)
            ·
              refine ⟨7915394610938573927803211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21107718962502863807475229 7915394610938573927803211)
              ·
                refine ⟨11873091916407860891704817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7915394610938573927803211 11873091916407860891704817)
                ·
                  refine ⟨8904818937305895668778613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11873091916407860891704817 8904818937305895668778613)
                  ·
                    refine ⟨834826775372427718947995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8904818937305895668778613 834826775372427718947995)
                    ·
                      rfl

theorem cell23_4877458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_4877458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877458 prefixEnd_4877458 := by exact prefixLift 4877458
  have htrace : WordTrace (prefixWord ++ tailWord_4877458) baseStart_4877458 baseEnd_4877458 := by
    simpa [prefixWord, tailWord_4877458, baseEnd_4877458] using wordTrace_append hprefix tailTrace_4877458
  have hstable : (prefixWord ++ tailWord_4877458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877458).length < 2 ^ (prefixWord ++ tailWord_4877458).sum := by decide
  have hdescent : baseEnd_4877458 < baseStart_4877458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877461 : List Nat := [1, 3, 2, 1, 1, 1, 2, 5, 2, 1, 4]
def baseStart_4877461 : Nat := 118140960795 + 4877461 * 2 ^ 59
def prefixEnd_4877461 : Nat := 4983230072969 + 3 ^ 40 * 4877461 * 2
def baseEnd_4877461 : Nat := 2504481866559246645106471

theorem tailTrace_4877461 : CollatzResearch.WordTrace tailWord_4877461 prefixEnd_4877461 2504481866559246645106471 := by
  unfold tailWord_4877461
  simp only [CollatzResearch.WordTrace]
  refine ⟨177895617382799275865072237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118597078255199517243381491 177895617382799275865072237)
  ·
    refine ⟨66710856518549728449402089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177895617382799275865072237 66710856518549728449402089)
    ·
      refine ⟨50033142388912296337051567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66710856518549728449402089 50033142388912296337051567)
      ·
        refine ⟨75049713583368444505577351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50033142388912296337051567 75049713583368444505577351)
        ·
          refine ⟨112574570375052666758366027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75049713583368444505577351 112574570375052666758366027)
          ·
            refine ⟨168861855562579000137549041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112574570375052666758366027 168861855562579000137549041)
            ·
              refine ⟨126646391671934250103161781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168861855562579000137549041 126646391671934250103161781)
              ·
                refine ⟨11873099219243835947171417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126646391671934250103161781 11873099219243835947171417)
                ·
                  refine ⟨8904824414432876960378563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11873099219243835947171417 8904824414432876960378563)
                  ·
                    refine ⟨13357236621649315440567845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8904824414432876960378563 13357236621649315440567845)
                    ·
                      refine ⟨2504481866559246645106471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13357236621649315440567845 2504481866559246645106471)
                      ·
                        rfl

theorem cell23_4877461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_4877461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877461 prefixEnd_4877461 := by exact prefixLift 4877461
  have htrace : WordTrace (prefixWord ++ tailWord_4877461) baseStart_4877461 baseEnd_4877461 := by
    simpa [prefixWord, tailWord_4877461, baseEnd_4877461] using wordTrace_append hprefix tailTrace_4877461
  have hstable : (prefixWord ++ tailWord_4877461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877461).length < 2 ^ (prefixWord ++ tailWord_4877461).sum := by decide
  have hdescent : baseEnd_4877461 < baseStart_4877461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877501 : List Nat := [1, 4, 1, 2, 1, 1, 2, 5, 6]
def baseStart_4877501 : Nat := 118140960795 + 4877501 * 2 ^ 59
def prefixEnd_4877501 : Nat := 4983230072969 + 3 ^ 40 * 4877501 * 2
def baseEnd_4877501 : Nat := 278278045087269609845143

theorem tailTrace_4877501 : CollatzResearch.WordTrace tailWord_4877501 prefixEnd_4877501 278278045087269609845143 := by
  unfold tailWord_4877501
  simp only [CollatzResearch.WordTrace]
  refine ⟨177897076302654362696528357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118598050868436241797685571 177897076302654362696528357)
  ·
    refine ⟨33355701806747693005599067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177897076302654362696528357 33355701806747693005599067)
    ·
      refine ⟨50033552710121539508398601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33355701806747693005599067 50033552710121539508398601)
      ·
        refine ⟨37525164532591154631298951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50033552710121539508398601 37525164532591154631298951)
        ·
          refine ⟨56287746798886731946948427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37525164532591154631298951 56287746798886731946948427)
          ·
            refine ⟨84431620198330097920422641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56287746798886731946948427 84431620198330097920422641)
            ·
              refine ⟨63323715148747573440316981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84431620198330097920422641 63323715148747573440316981)
              ·
                refine ⟨5936598295195085010029717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63323715148747573440316981 5936598295195085010029717)
                ·
                  refine ⟨278278045087269609845143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5936598295195085010029717 278278045087269609845143)
                  ·
                    rfl

theorem cell23_4877501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 2, 5, 6].length) (baseStart_4877501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877501 prefixEnd_4877501 := by exact prefixLift 4877501
  have htrace : WordTrace (prefixWord ++ tailWord_4877501) baseStart_4877501 baseEnd_4877501 := by
    simpa [prefixWord, tailWord_4877501, baseEnd_4877501] using wordTrace_append hprefix tailTrace_4877501
  have hstable : (prefixWord ++ tailWord_4877501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877501).length < 2 ^ (prefixWord ++ tailWord_4877501).sum := by decide
  have hdescent : baseEnd_4877501 < baseStart_4877501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877505 : List Nat := [1, 2, 6, 1, 1, 1, 2, 2, 3, 4]
def baseStart_4877505 : Nat := 118140960795 + 4877505 * 2 ^ 59
def prefixEnd_4877505 : Nat := 4983230072969 + 3 ^ 40 * 4877505 * 2
def baseEnd_4877505 : Nat := 834834819902681490985423

theorem tailTrace_4877505 : CollatzResearch.WordTrace tailWord_4877505 prefixEnd_4877505 834834819902681490985423 := by
  unfold tailWord_4877505
  simp only [CollatzResearch.WordTrace]
  refine ⟨177897222194639871379673969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118598148129759914253115979 177897222194639871379673969)
  ·
    refine ⟨133422916645979903534755477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177897222194639871379673969 133422916645979903534755477)
    ·
      refine ⟨6254199217780307978191663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 133422916645979903534755477 6254199217780307978191663)
      ·
        refine ⟨9381298826670461967287495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6254199217780307978191663 9381298826670461967287495)
        ·
          refine ⟨14071948240005692950931243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9381298826670461967287495 14071948240005692950931243)
          ·
            refine ⟨21107922360008539426396865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14071948240005692950931243 21107922360008539426396865)
            ·
              refine ⟨15830941770006404569797649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21107922360008539426396865 15830941770006404569797649)
              ·
                refine ⟨11873206327504803427348237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15830941770006404569797649 11873206327504803427348237)
                ·
                  refine ⟨4452452372814301285255589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11873206327504803427348237 4452452372814301285255589)
                  ·
                    refine ⟨834834819902681490985423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4452452372814301285255589 834834819902681490985423)
                    ·
                      rfl

theorem cell23_4877505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_4877505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877505 prefixEnd_4877505 := by exact prefixLift 4877505
  have htrace : WordTrace (prefixWord ++ tailWord_4877505) baseStart_4877505 baseEnd_4877505 := by
    simpa [prefixWord, tailWord_4877505, baseEnd_4877505] using wordTrace_append hprefix tailTrace_4877505
  have hstable : (prefixWord ++ tailWord_4877505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877505).length < 2 ^ (prefixWord ++ tailWord_4877505).sum := by decide
  have hdescent : baseEnd_4877505 < baseStart_4877505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877561 : List Nat := [1, 2, 1, 3, 1, 1, 4, 3, 1, 6]
def baseStart_4877561 : Nat := 118140960795 + 4877561 * 2 ^ 59
def prefixEnd_4877561 : Nat := 4983230072969 + 3 ^ 40 * 4877561 * 2
def baseEnd_4877561 : Nat := 834844404874898751285337

theorem tailTrace_4877561 : CollatzResearch.WordTrace tailWord_4877561 prefixEnd_4877561 834844404874898751285337 := by
  unfold tailWord_4877561
  simp only [CollatzResearch.WordTrace]
  refine ⟨177899264682436992943712537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118599509788291328629141691 177899264682436992943712537)
  ·
    refine ⟨133424448511827744707784403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177899264682436992943712537 133424448511827744707784403)
    ·
      refine ⟨200136672767741617061676605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133424448511827744707784403 200136672767741617061676605)
      ·
        refine ⟨75051252287903106398128727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200136672767741617061676605 75051252287903106398128727)
        ·
          refine ⟨112576878431854659597193091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75051252287903106398128727 112576878431854659597193091)
          ·
            refine ⟨168865317647781989395789637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112576878431854659597193091 168865317647781989395789637)
            ·
              refine ⟨31662247058959123011710557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 168865317647781989395789637 31662247058959123011710557)
              ·
                refine ⟨11873342647109671129391459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31662247058959123011710557 11873342647109671129391459)
                ·
                  refine ⟨17810013970664506694087189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11873342647109671129391459 17810013970664506694087189)
                  ·
                    refine ⟨834844404874898751285337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17810013970664506694087189 834844404874898751285337)
                    ·
                      rfl

theorem cell23_4877561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 3, 1, 6].length) (baseStart_4877561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877561 prefixEnd_4877561 := by exact prefixLift 4877561
  have htrace : WordTrace (prefixWord ++ tailWord_4877561) baseStart_4877561 baseEnd_4877561 := by
    simpa [prefixWord, tailWord_4877561, baseEnd_4877561] using wordTrace_append hprefix tailTrace_4877561
  have hstable : (prefixWord ++ tailWord_4877561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877561).length < 2 ^ (prefixWord ++ tailWord_4877561).sum := by decide
  have hdescent : baseEnd_4877561 < baseStart_4877561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877572 : List Nat := [2, 3, 2, 2, 2, 2, 2, 1, 2, 3, 2]
def baseStart_4877572 : Nat := 118140960795 + 4877572 * 2 ^ 59
def prefixEnd_4877572 : Nat := 4983230072969 + 3 ^ 40 * 4877572 * 2
def baseEnd_4877572 : Nat := 2504538862911895710818461

theorem tailTrace_4877572 : CollatzResearch.WordTrace tailWord_4877572 prefixEnd_4877572 2504538862911895710818461 := by
  unfold tailWord_4877572
  simp only [CollatzResearch.WordTrace]
  refine ⟨88949832942698570911181485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118599777256931427881575313 88949832942698570911181485)
  ·
    refine ⟨33356187353511964091693057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88949832942698570911181485 33356187353511964091693057)
    ·
      refine ⟨25017140515133973068769793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33356187353511964091693057 25017140515133973068769793)
      ·
        refine ⟨18762855386350479801577345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25017140515133973068769793 18762855386350479801577345)
        ·
          refine ⟨14072141539762859851183009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18762855386350479801577345 14072141539762859851183009)
          ·
            refine ⟨10554106154822144888387257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14072141539762859851183009 10554106154822144888387257)
            ·
              refine ⟨7915579616116608666290443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10554106154822144888387257 7915579616116608666290443)
              ·
                refine ⟨11873369424174912999435665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7915579616116608666290443 11873369424174912999435665)
                ·
                  refine ⟨8905027068131184749576749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11873369424174912999435665 8905027068131184749576749)
                  ·
                    refine ⟨3339385150549194281091281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8905027068131184749576749 3339385150549194281091281)
                    ·
                      refine ⟨2504538862911895710818461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3339385150549194281091281 2504538862911895710818461)
                      ·
                        rfl

theorem cell23_4877572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_4877572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877572 prefixEnd_4877572 := by exact prefixLift 4877572
  have htrace : WordTrace (prefixWord ++ tailWord_4877572) baseStart_4877572 baseEnd_4877572 := by
    simpa [prefixWord, tailWord_4877572, baseEnd_4877572] using wordTrace_append hprefix tailTrace_4877572
  have hstable : (prefixWord ++ tailWord_4877572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877572).length < 2 ^ (prefixWord ++ tailWord_4877572).sum := by decide
  have hdescent : baseEnd_4877572 < baseStart_4877572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877585 : List Nat := [1, 2, 2, 1, 1, 4, 5, 1, 1, 1, 4]
def baseStart_4877585 : Nat := 118140960795 + 4877585 * 2 ^ 59
def prefixEnd_4877585 : Nat := 4983230072969 + 3 ^ 40 * 4877585 * 2
def baseEnd_4877585 : Nat := 2504545538160404159955901

theorem tailTrace_4877585 : CollatzResearch.WordTrace tailWord_4877585 prefixEnd_4877585 2504545538160404159955901 := by
  unfold tailWord_4877585
  simp only [CollatzResearch.WordTrace]
  refine ⟨177900140034350045042586209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118600093356233363361724139 177900140034350045042586209)
  ·
    refine ⟨133425105025762533781939657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177900140034350045042586209 133425105025762533781939657)
    ·
      refine ⟨100068828769321900336454743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133425105025762533781939657 100068828769321900336454743)
      ·
        refine ⟨150103243153982850504682115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100068828769321900336454743 150103243153982850504682115)
        ·
          refine ⟨225154864730974275757023173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150103243153982850504682115 225154864730974275757023173)
          ·
            refine ⟨42216537137057676704441845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225154864730974275757023173 42216537137057676704441845)
            ·
              refine ⟨3957800356599157191041423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42216537137057676704441845 3957800356599157191041423)
              ·
                refine ⟨5936700534898735786562135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3957800356599157191041423 5936700534898735786562135)
                ·
                  refine ⟨8905050802348103679843203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5936700534898735786562135 8905050802348103679843203)
                  ·
                    refine ⟨13357576203522155519764805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8905050802348103679843203 13357576203522155519764805)
                    ·
                      refine ⟨2504545538160404159955901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13357576203522155519764805 2504545538160404159955901)
                      ·
                        rfl

theorem cell23_4877585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 5, 1, 1, 1, 4].length) (baseStart_4877585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877585 prefixEnd_4877585 := by exact prefixLift 4877585
  have htrace : WordTrace (prefixWord ++ tailWord_4877585) baseStart_4877585 baseEnd_4877585 := by
    simpa [prefixWord, tailWord_4877585, baseEnd_4877585] using wordTrace_append hprefix tailTrace_4877585
  have hstable : (prefixWord ++ tailWord_4877585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877585).length < 2 ^ (prefixWord ++ tailWord_4877585).sum := by decide
  have hdescent : baseEnd_4877585 < baseStart_4877585 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877608 : List Nat := [2, 1, 5, 1, 2, 1, 3, 8]
def baseStart_4877608 : Nat := 118140960795 + 4877608 * 2 ^ 59
def prefixEnd_4877608 : Nat := 4983230072969 + 3 ^ 40 * 4877608 * 2
def baseEnd_4877608 : Nat := 92761383267239169258085

theorem tailTrace_4877608 : CollatzResearch.WordTrace tailWord_4877608 prefixEnd_4877608 92761383267239169258085 := by
  unfold tailWord_4877608
  simp only [CollatzResearch.WordTrace]
  refine ⟨88950489456633359985336739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118600652608844479980448985 88950489456633359985336739)
  ·
    refine ⟨133425734184950039978005109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88950489456633359985336739 133425734184950039978005109)
    ·
      refine ⟨12508662579839066247937979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133425734184950039978005109 12508662579839066247937979)
      ·
        refine ⟨18762993869758599371906969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12508662579839066247937979 18762993869758599371906969)
        ·
          refine ⟨14072245402318949528930227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18762993869758599371906969 14072245402318949528930227)
          ·
            refine ⟨21108368103478424293395341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14072245402318949528930227 21108368103478424293395341)
            ·
              refine ⟨7915638038804409110023253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21108368103478424293395341 7915638038804409110023253)
              ·
                refine ⟨92761383267239169258085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7915638038804409110023253 92761383267239169258085)
                ·
                  rfl

theorem cell23_4877608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 3, 8].length) (baseStart_4877608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877608 prefixEnd_4877608 := by exact prefixLift 4877608
  have htrace : WordTrace (prefixWord ++ tailWord_4877608) baseStart_4877608 baseEnd_4877608 := by
    simpa [prefixWord, tailWord_4877608, baseEnd_4877608] using wordTrace_append hprefix tailTrace_4877608
  have hstable : (prefixWord ++ tailWord_4877608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877608).length < 2 ^ (prefixWord ++ tailWord_4877608).sum := by decide
  have hdescent : baseEnd_4877608 < baseStart_4877608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877625 : List Nat := [1, 2, 1, 6, 2, 1, 3, 7]
def baseStart_4877625 : Nat := 118140960795 + 4877625 * 2 ^ 59
def prefixEnd_4877625 : Nat := 4983230072969 + 3 ^ 40 * 4877625 * 2
def baseEnd_4877625 : Nat := 92761706569873481609471

theorem tailTrace_4877625 : CollatzResearch.WordTrace tailWord_4877625 prefixEnd_4877625 92761706569873481609471 := by
  unfold tailWord_4877625
  simp only [CollatzResearch.WordTrace]
  refine ⟨177901598954205131874042329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118601065969470087916028219 177901598954205131874042329)
  ·
    refine ⟨133426199215653848905531747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177901598954205131874042329 133426199215653848905531747)
    ·
      refine ⟨200139298823480773358297621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133426199215653848905531747 200139298823480773358297621)
      ·
        refine ⟨9381529632350661251170201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 200139298823480773358297621 9381529632350661251170201)
        ·
          refine ⟨7036147224262995938377651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9381529632350661251170201 7036147224262995938377651)
          ·
            refine ⟨10554220836394493907566477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7036147224262995938377651 10554220836394493907566477)
            ·
              refine ⟨3957832813647935215337429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10554220836394493907566477 3957832813647935215337429)
              ·
                refine ⟨92761706569873481609471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3957832813647935215337429 92761706569873481609471)
                ·
                  rfl

theorem cell23_4877625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 3, 7].length) (baseStart_4877625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877625 prefixEnd_4877625 := by exact prefixLift 4877625
  have htrace : WordTrace (prefixWord ++ tailWord_4877625) baseStart_4877625 baseEnd_4877625 := by
    simpa [prefixWord, tailWord_4877625, baseEnd_4877625] using wordTrace_append hprefix tailTrace_4877625
  have hstable : (prefixWord ++ tailWord_4877625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877625).length < 2 ^ (prefixWord ++ tailWord_4877625).sum := by decide
  have hdescent : baseEnd_4877625 < baseStart_4877625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877636 : List Nat := [2, 3, 4, 1, 1, 1, 1, 5, 1, 2, 2]
def baseStart_4877636 : Nat := 118140960795 + 4877636 * 2 ^ 59
def prefixEnd_4877636 : Nat := 4983230072969 + 3 ^ 40 * 4877636 * 2
def baseEnd_4877636 : Nat := 2504571725673783460418167

theorem tailTrace_4877636 : CollatzResearch.WordTrace tailWord_4877636 prefixEnd_4877636 2504571725673783460418167 := by
  unfold tailWord_4877636
  simp only [CollatzResearch.WordTrace]
  refine ⟨88951000078582640376346381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118601333438110187168461841 88951000078582640376346381)
  ·
    refine ⟨33356625029468490141129893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88951000078582640376346381 33356625029468490141129893)
    ·
      refine ⟨6254367193025341901461855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33356625029468490141129893 6254367193025341901461855)
      ·
        refine ⟨9381550789538012852192783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6254367193025341901461855 9381550789538012852192783)
        ·
          refine ⟨14072326184307019278289175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9381550789538012852192783 14072326184307019278289175)
          ·
            refine ⟨21108489276460528917433763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14072326184307019278289175 21108489276460528917433763)
            ·
              refine ⟨31662733914690793376150645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21108489276460528917433763 31662733914690793376150645)
              ·
                refine ⟨2968381304502261879014123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31662733914690793376150645 2968381304502261879014123)
                ·
                  refine ⟨4452571956753392818521185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968381304502261879014123 4452571956753392818521185)
                  ·
                    refine ⟨3339428967565044613890889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4452571956753392818521185 3339428967565044613890889)
                    ·
                      refine ⟨2504571725673783460418167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3339428967565044613890889 2504571725673783460418167)
                      ·
                        rfl

theorem cell23_4877636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_4877636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877636 prefixEnd_4877636 := by exact prefixLift 4877636
  have htrace : WordTrace (prefixWord ++ tailWord_4877636) baseStart_4877636 baseEnd_4877636 := by
    simpa [prefixWord, tailWord_4877636, baseEnd_4877636] using wordTrace_append hprefix tailTrace_4877636
  have hstable : (prefixWord ++ tailWord_4877636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877636).length < 2 ^ (prefixWord ++ tailWord_4877636).sum := by decide
  have hdescent : baseEnd_4877636 < baseStart_4877636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877651 : List Nat := [1, 1, 1, 2, 1, 1, 5, 1, 4, 6]
def baseStart_4877651 : Nat := 118140960795 + 4877651 * 2 ^ 59
def prefixEnd_4877651 : Nat := 4983230072969 + 3 ^ 40 * 4877651 * 2
def baseEnd_4877651 : Nat := 834859809294533633910199

theorem tailTrace_4877651 : CollatzResearch.WordTrace tailWord_4877651 prefixEnd_4877651 834859809294533633910199 := by
  unfold tailWord_4877651
  simp only [CollatzResearch.WordTrace]
  refine ⟨177902547252110938314488807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118601698168073958876325871 177902547252110938314488807)
  ·
    refine ⟨266853820878166407471733211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177902547252110938314488807 266853820878166407471733211)
    ·
      refine ⟨400280731317249611207599817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266853820878166407471733211 400280731317249611207599817)
      ·
        refine ⟨300210548487937208405699863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400280731317249611207599817 300210548487937208405699863)
        ·
          refine ⟨450315822731905812608549795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300210548487937208405699863 450315822731905812608549795)
          ·
            refine ⟨675473734097858718912824693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450315822731905812608549795 675473734097858718912824693)
            ·
              refine ⟨63325662571674254898077315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 675473734097858718912824693 63325662571674254898077315)
              ·
                refine ⟨94988493857511382347115973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63325662571674254898077315 94988493857511382347115973)
                ·
                  refine ⟨17810342598283384190084245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 94988493857511382347115973 17810342598283384190084245)
                  ·
                    refine ⟨834859809294533633910199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17810342598283384190084245 834859809294533633910199)
                    ·
                      rfl

theorem cell23_4877651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 1, 4, 6].length) (baseStart_4877651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877651 prefixEnd_4877651 := by exact prefixLift 4877651
  have htrace : WordTrace (prefixWord ++ tailWord_4877651) baseStart_4877651 baseEnd_4877651 := by
    simpa [prefixWord, tailWord_4877651, baseEnd_4877651] using wordTrace_append hprefix tailTrace_4877651
  have hstable : (prefixWord ++ tailWord_4877651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877651).length < 2 ^ (prefixWord ++ tailWord_4877651).sum := by decide
  have hdescent : baseEnd_4877651 < baseStart_4877651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877668 : List Nat := [2, 3, 1, 1, 3, 2, 2, 1, 2, 6]
def baseStart_4877668 : Nat := 118140960795 + 4877668 * 2 ^ 59
def prefixEnd_4877668 : Nat := 4983230072969 + 3 ^ 40 * 4877668 * 2
def baseEnd_4877668 : Nat := 834862719018242445072673

theorem tailTrace_4877668 : CollatzResearch.WordTrace tailWord_4877668 prefixEnd_4877668 834862719018242445072673 := by
  unfold tailWord_4877668
  simp only [CollatzResearch.WordTrace]
  refine ⟨88951583646524675108928829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118602111528699566811905105 88951583646524675108928829)
  ·
    refine ⟨33356843867446753165848311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88951583646524675108928829 33356843867446753165848311)
    ·
      refine ⟨50035265801170129748772467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33356843867446753165848311 50035265801170129748772467)
      ·
        refine ⟨75052898701755194623158701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50035265801170129748772467 75052898701755194623158701)
        ·
          refine ⟨28144837013158197983684513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75052898701755194623158701 28144837013158197983684513)
          ·
            refine ⟨21108627759868648487763385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28144837013158197983684513 21108627759868648487763385)
            ·
              refine ⟨15831470819901486365822539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21108627759868648487763385 15831470819901486365822539)
              ·
                refine ⟨23747206229852229548733809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15831470819901486365822539 23747206229852229548733809)
                ·
                  refine ⟨17810404672389172161550357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23747206229852229548733809 17810404672389172161550357)
                  ·
                    refine ⟨834862719018242445072673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17810404672389172161550357 834862719018242445072673)
                    ·
                      rfl

theorem cell23_4877668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 2, 1, 2, 6].length) (baseStart_4877668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877668 prefixEnd_4877668 := by exact prefixLift 4877668
  have htrace : WordTrace (prefixWord ++ tailWord_4877668) baseStart_4877668 baseEnd_4877668 := by
    simpa [prefixWord, tailWord_4877668, baseEnd_4877668] using wordTrace_append hprefix tailTrace_4877668
  have hstable : (prefixWord ++ tailWord_4877668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877668).length < 2 ^ (prefixWord ++ tailWord_4877668).sum := by decide
  have hdescent : baseEnd_4877668 < baseStart_4877668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877675 : List Nat := [1, 1, 1, 1, 2, 2, 2, 1, 8, 2, 2]
def baseStart_4877675 : Nat := 118140960795 + 4877675 * 2 ^ 59
def prefixEnd_4877675 : Nat := 4983230072969 + 3 ^ 40 * 4877675 * 2
def baseEnd_4877675 : Nat := 2504591751419308807830487

theorem tailTrace_4877675 : CollatzResearch.WordTrace tailWord_4877675 prefixEnd_4877675 2504591751419308807830487 := by
  unfold tailWord_4877675
  simp only [CollatzResearch.WordTrace]
  refine ⟨177903422604023990413362479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118602281736015993608908319 177903422604023990413362479)
  ·
    refine ⟨266855133906035985620043719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177903422604023990413362479 266855133906035985620043719)
    ·
      refine ⟨400282700859053978430065579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266855133906035985620043719 400282700859053978430065579)
      ·
        refine ⟨600424051288580967645098369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400282700859053978430065579 600424051288580967645098369)
        ·
          refine ⟨450318038466435725733823777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600424051288580967645098369 450318038466435725733823777)
          ·
            refine ⟨337738528849826794300367833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450318038466435725733823777 337738528849826794300367833)
            ·
              refine ⟨253303896637370095725275875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 337738528849826794300367833 253303896637370095725275875)
              ·
                refine ⟨379955844956055143587913813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253303896637370095725275875 379955844956055143587913813)
                ·
                  refine ⟨4452607558078771213920865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 379955844956055143587913813 4452607558078771213920865)
                  ·
                    refine ⟨3339455668559078410440649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4452607558078771213920865 3339455668559078410440649)
                    ·
                      refine ⟨2504591751419308807830487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3339455668559078410440649 2504591751419308807830487)
                      ·
                        rfl

theorem cell23_4877675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 8, 2, 2].length) (baseStart_4877675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877675 prefixEnd_4877675 := by exact prefixLift 4877675
  have htrace : WordTrace (prefixWord ++ tailWord_4877675) baseStart_4877675 baseEnd_4877675 := by
    simpa [prefixWord, tailWord_4877675, baseEnd_4877675] using wordTrace_append hprefix tailTrace_4877675
  have hstable : (prefixWord ++ tailWord_4877675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877675).length < 2 ^ (prefixWord ++ tailWord_4877675).sum := by decide
  have hdescent : baseEnd_4877675 < baseStart_4877675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877711 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 1, 13]
def baseStart_4877711 : Nat := 118140960795 + 4877711 * 2 ^ 59
def prefixEnd_4877711 : Nat := 4983230072969 + 3 ^ 40 * 4877711 * 2
def baseEnd_4877711 : Nat := 834870078907623555660107

theorem tailTrace_4877711 : CollatzResearch.WordTrace tailWord_4877711 prefixEnd_4877711 834870078907623555660107 := by
  unfold tailWord_4877711
  simp only [CollatzResearch.WordTrace]
  refine ⟨177904735631893568561672987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118603157087929045707781991 177904735631893568561672987)
  ·
    refine ⟨266857103447840352842509481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177904735631893568561672987 266857103447840352842509481)
    ·
      refine ⟨200142827585880264631882111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266857103447840352842509481 200142827585880264631882111)
      ·
        refine ⟨300214241378820396947823167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200142827585880264631882111 300214241378820396947823167)
        ·
          refine ⟨450321362068230595421734751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300214241378820396947823167 450321362068230595421734751)
          ·
            refine ⟨675482043102345893132602127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450321362068230595421734751 675482043102345893132602127)
            ·
              refine ⟨1013223064653518839698903191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675482043102345893132602127 1013223064653518839698903191)
              ·
                refine ⟨1519834596980278259548354787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013223064653518839698903191 1519834596980278259548354787)
                ·
                  refine ⟨2279751895470417389322532181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519834596980278259548354787 2279751895470417389322532181)
                  ·
                    refine ⟨834870078907623555660107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 13 2279751895470417389322532181 834870078907623555660107)
                    ·
                      rfl

theorem cell23_4877711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_4877711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877711 prefixEnd_4877711 := by exact prefixLift 4877711
  have htrace : WordTrace (prefixWord ++ tailWord_4877711) baseStart_4877711 baseEnd_4877711 := by
    simpa [prefixWord, tailWord_4877711, baseEnd_4877711] using wordTrace_append hprefix tailTrace_4877711
  have hstable : (prefixWord ++ tailWord_4877711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877711).length < 2 ^ (prefixWord ++ tailWord_4877711).sum := by decide
  have hdescent : baseEnd_4877711 < baseStart_4877711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877728 : List Nat := [2, 1, 1, 4, 1, 2, 1, 2, 4, 5]
def baseStart_4877728 : Nat := 118140960795 + 4877728 * 2 ^ 59
def prefixEnd_4877728 : Nat := 4983230072969 + 3 ^ 40 * 4877728 * 2
def baseEnd_4877728 : Nat := 834872988631332366822581

theorem tailTrace_4877728 : CollatzResearch.WordTrace tailWord_4877728 prefixEnd_4877728 834872988631332366822581 := by
  unfold tailWord_4877728
  simp only [CollatzResearch.WordTrace]
  refine ⟨88952677836415990232520919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118603570448554653643361225 88952677836415990232520919)
  ·
    refine ⟨133429016754623985348781379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88952677836415990232520919 133429016754623985348781379)
    ·
      refine ⟨200143525131935978023172069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133429016754623985348781379 200143525131935978023172069)
      ·
        refine ⟨37526910962237995879344763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200143525131935978023172069 37526910962237995879344763)
        ·
          refine ⟨56290366443356993819017145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37526910962237995879344763 56290366443356993819017145)
          ·
            refine ⟨42217774832517745364262859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56290366443356993819017145 42217774832517745364262859)
            ·
              refine ⟨63326662248776618046394289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42217774832517745364262859 63326662248776618046394289)
              ·
                refine ⟨47494996686582463534795717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63326662248776618046394289 47494996686582463534795717)
                ·
                  refine ⟨8905311878734211912774197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47494996686582463534795717 8905311878734211912774197)
                  ·
                    refine ⟨834872988631332366822581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8905311878734211912774197 834872988631332366822581)
                    ·
                      rfl

theorem cell23_4877728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 1, 2, 4, 5].length) (baseStart_4877728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877728 prefixEnd_4877728 := by exact prefixLift 4877728
  have htrace : WordTrace (prefixWord ++ tailWord_4877728) baseStart_4877728 baseEnd_4877728 := by
    simpa [prefixWord, tailWord_4877728, baseEnd_4877728] using wordTrace_append hprefix tailTrace_4877728
  have hstable : (prefixWord ++ tailWord_4877728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877728).length < 2 ^ (prefixWord ++ tailWord_4877728).sum := by decide
  have hdescent : baseEnd_4877728 < baseStart_4877728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877745 : List Nat := [1, 2, 2, 4, 1, 1, 4, 1, 2, 5]
def baseStart_4877745 : Nat := 118140960795 + 4877745 * 2 ^ 59
def prefixEnd_4877745 : Nat := 4983230072969 + 3 ^ 40 * 4877745 * 2
def baseEnd_4877745 : Nat := 834875898355041177985055

theorem tailTrace_4877745 : CollatzResearch.WordTrace tailWord_4877745 prefixEnd_4877745 834875898355041177985055 := by
  unfold tailWord_4877745
  simp only [CollatzResearch.WordTrace]
  refine ⟨177905975713770392368410689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118603983809180261578940459 177905975713770392368410689)
  ·
    refine ⟨133429481785327794276308017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177905975713770392368410689 133429481785327794276308017)
    ·
      refine ⟨100072111338995845707231013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133429481785327794276308017 100072111338995845707231013)
      ·
        refine ⟨18763520876061721070105815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100072111338995845707231013 18763520876061721070105815)
        ·
          refine ⟨28145281314092581605158723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18763520876061721070105815 28145281314092581605158723)
          ·
            refine ⟨42217921971138872407738085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28145281314092581605158723 42217921971138872407738085)
            ·
              refine ⟨7915860369588538576450891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42217921971138872407738085 7915860369588538576450891)
              ·
                refine ⟨11873790554382807864676337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7915860369588538576450891 11873790554382807864676337)
                ·
                  refine ⟨8905342915787105898507253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11873790554382807864676337 8905342915787105898507253)
                  ·
                    refine ⟨834875898355041177985055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8905342915787105898507253 834875898355041177985055)
                    ·
                      rfl

theorem cell23_4877745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 4, 1, 2, 5].length) (baseStart_4877745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877745 prefixEnd_4877745 := by exact prefixLift 4877745
  have htrace : WordTrace (prefixWord ++ tailWord_4877745) baseStart_4877745 baseEnd_4877745 := by
    simpa [prefixWord, tailWord_4877745, baseEnd_4877745] using wordTrace_append hprefix tailTrace_4877745
  have hstable : (prefixWord ++ tailWord_4877745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877745).length < 2 ^ (prefixWord ++ tailWord_4877745).sum := by decide
  have hdescent : baseEnd_4877745 < baseStart_4877745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877768 : List Nat := [2, 1, 3, 1, 3, 1, 1, 1, 2, 3, 5]
def baseStart_4877768 : Nat := 118140960795 + 4877768 * 2 ^ 59
def prefixEnd_4877768 : Nat := 4983230072969 + 3 ^ 40 * 4877768 * 2
def baseEnd_4877768 : Nat := 2504639505120176943967559

theorem tailTrace_4877768 : CollatzResearch.WordTrace tailWord_4877768 prefixEnd_4877768 2504639505120176943967559 := by
  unfold tailWord_4877768
  simp only [CollatzResearch.WordTrace]
  refine ⟨88953407296343533648248979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118604543061791378197665305 88953407296343533648248979)
  ·
    refine ⟨133430110944515300472373469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88953407296343533648248979 133430110944515300472373469)
    ·
      refine ⟨50036291604193237677140051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133430110944515300472373469 50036291604193237677140051)
      ·
        refine ⟨75054437406289856515710077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50036291604193237677140051 75054437406289856515710077)
        ·
          refine ⟨28145414027358696193391279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75054437406289856515710077 28145414027358696193391279)
          ·
            refine ⟨42218121041038044290086919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28145414027358696193391279 42218121041038044290086919)
            ·
              refine ⟨63327181561557066435130379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42218121041038044290086919 63327181561557066435130379)
              ·
                refine ⟨94990772342335599652695569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63327181561557066435130379 94990772342335599652695569)
                ·
                  refine ⟨71243079256751699739521677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 94990772342335599652695569 71243079256751699739521677)
                  ·
                    refine ⟨26716154721281887402320629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71243079256751699739521677 26716154721281887402320629)
                    ·
                      refine ⟨2504639505120176943967559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26716154721281887402320629 2504639505120176943967559)
                      ·
                        rfl

theorem cell23_4877768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_4877768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877768 prefixEnd_4877768 := by exact prefixLift 4877768
  have htrace : WordTrace (prefixWord ++ tailWord_4877768) baseStart_4877768 baseEnd_4877768 := by
    simpa [prefixWord, tailWord_4877768, baseEnd_4877768] using wordTrace_append hprefix tailTrace_4877768
  have hstable : (prefixWord ++ tailWord_4877768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877768).length < 2 ^ (prefixWord ++ tailWord_4877768).sum := by decide
  have hdescent : baseEnd_4877768 < baseStart_4877768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877802 : List Nat := [3, 1, 3, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_4877802 : Nat := 118140960795 + 4877802 * 2 ^ 59
def prefixEnd_4877802 : Nat := 4983230072969 + 3 ^ 40 * 4877802 * 2
def baseEnd_4877802 : Nat := 2504656963462429810942403

theorem tailTrace_4877802 : CollatzResearch.WordTrace tailWord_4877802 prefixEnd_4877802 2504656963462429810942403 := by
  unfold tailWord_4877802
  simp only [CollatzResearch.WordTrace]
  refine ⟨44477013668640972775808915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118605369783042594068823773 44477013668640972775808915)
  ·
    refine ⟨66715520502961459163713373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44477013668640972775808915 66715520502961459163713373)
    ·
      refine ⟨25018320188610547186392515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66715520502961459163713373 25018320188610547186392515)
      ·
        refine ⟨37527480282915820779588773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25018320188610547186392515 37527480282915820779588773)
        ·
          refine ⟨7036402553046716396172895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37527480282915820779588773 7036402553046716396172895)
          ·
            refine ⟨10554603829570074594259343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7036402553046716396172895 10554603829570074594259343)
            ·
              refine ⟨15831905744355111891389015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10554603829570074594259343 15831905744355111891389015)
              ·
                refine ⟨23747858616532667837083523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15831905744355111891389015 23747858616532667837083523)
                ·
                  refine ⟨35621787924799001755625285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23747858616532667837083523 35621787924799001755625285)
                  ·
                    refine ⟨6679085235899812829179741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35621787924799001755625285 6679085235899812829179741)
                    ·
                      refine ⟨2504656963462429810942403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6679085235899812829179741 2504656963462429810942403)
                      ·
                        rfl

theorem cell23_4877802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_4877802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877802 prefixEnd_4877802 := by exact prefixLift 4877802
  have htrace : WordTrace (prefixWord ++ tailWord_4877802) baseStart_4877802 baseEnd_4877802 := by
    simpa [prefixWord, tailWord_4877802, baseEnd_4877802] using wordTrace_append hprefix tailTrace_4877802
  have hstable : (prefixWord ++ tailWord_4877802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877802).length < 2 ^ (prefixWord ++ tailWord_4877802).sum := by decide
  have hdescent : baseEnd_4877802 < baseStart_4877802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877809 : List Nat := [1, 2, 2, 2, 3, 3, 2, 3, 1, 4]
def baseStart_4877809 : Nat := 118140960795 + 4877809 * 2 ^ 59
def prefixEnd_4877809 : Nat := 4983230072969 + 3 ^ 40 * 4877809 * 2
def baseEnd_4877809 : Nat := 834886852609003761184957

theorem tailTrace_4877809 : CollatzResearch.WordTrace tailWord_4877809 prefixEnd_4877809 834886852609003761184957 := by
  unfold tailWord_4877809
  simp only [CollatzResearch.WordTrace]
  refine ⟨177908309985538531298740481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118605539990359020865826987 177908309985538531298740481)
  ·
    refine ⟨133431232489153898474055361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177908309985538531298740481 133431232489153898474055361)
    ·
      refine ⟨100073424366865423855541521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133431232489153898474055361 100073424366865423855541521)
      ·
        refine ⟨75055068275149067891656141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100073424366865423855541521 75055068275149067891656141)
        ·
          refine ⟨28145650603180900459371053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75055068275149067891656141 28145650603180900459371053)
          ·
            refine ⟨10554618976192837672264145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28145650603180900459371053 10554618976192837672264145)
            ·
              refine ⟨7915964232144628254198109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10554618976192837672264145 7915964232144628254198109)
              ·
                refine ⟨2968486587054235595324291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7915964232144628254198109 2968486587054235595324291)
                ·
                  refine ⟨4452729880581353392986437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968486587054235595324291 4452729880581353392986437)
                  ·
                    refine ⟨834886852609003761184957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4452729880581353392986437 834886852609003761184957)
                    ·
                      rfl

theorem cell23_4877809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 3, 1, 4].length) (baseStart_4877809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877809 prefixEnd_4877809 := by exact prefixLift 4877809
  have htrace : WordTrace (prefixWord ++ tailWord_4877809) baseStart_4877809 baseEnd_4877809 := by
    simpa [prefixWord, tailWord_4877809, baseEnd_4877809] using wordTrace_append hprefix tailTrace_4877809
  have hstable : (prefixWord ++ tailWord_4877809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877809).length < 2 ^ (prefixWord ++ tailWord_4877809).sum := by decide
  have hdescent : baseEnd_4877809 < baseStart_4877809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877826 : List Nat := [3, 4, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_4877826 : Nat := 118140960795 + 4877826 * 2 ^ 59
def prefixEnd_4877826 : Nat := 4983230072969 + 3 ^ 40 * 4877826 * 2
def baseEnd_4877826 : Nat := 834889762332712572347431

theorem tailTrace_4877826 : CollatzResearch.WordTrace tailWord_4877826 prefixEnd_4877826 834889762332712572347431 := by
  unfold tailWord_4877826
  simp only [CollatzResearch.WordTrace]
  refine ⟨44477232506619235800527333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118605953350984628801406221 44477232506619235800527333)
  ·
    refine ⟨8339481094991106712598875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44477232506619235800527333 8339481094991106712598875)
    ·
      refine ⟨12509221642486660068898313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8339481094991106712598875 12509221642486660068898313)
      ·
        refine ⟨9381916231864995051673735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12509221642486660068898313 9381916231864995051673735)
        ·
          refine ⟨14072874347797492577510603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9381916231864995051673735 14072874347797492577510603)
          ·
            refine ⟨21109311521696238866265905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14072874347797492577510603 21109311521696238866265905)
            ·
              refine ⟨15831983641272179149699429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21109311521696238866265905 15831983641272179149699429)
              ·
                refine ⟨2968496932738533590568643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15831983641272179149699429 2968496932738533590568643)
                ·
                  refine ⟨4452745399107800385852965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968496932738533590568643 4452745399107800385852965)
                  ·
                    refine ⟨834889762332712572347431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4452745399107800385852965 834889762332712572347431)
                    ·
                      rfl

theorem cell23_4877826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_4877826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877826 prefixEnd_4877826 := by exact prefixLift 4877826
  have htrace : WordTrace (prefixWord ++ tailWord_4877826) baseStart_4877826 baseEnd_4877826 := by
    simpa [prefixWord, tailWord_4877826, baseEnd_4877826] using wordTrace_append hprefix tailTrace_4877826
  have hstable : (prefixWord ++ tailWord_4877826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877826).length < 2 ^ (prefixWord ++ tailWord_4877826).sum := by decide
  have hdescent : baseEnd_4877826 < baseStart_4877826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877832 : List Nat := [2, 1, 3, 2, 1, 1, 3, 3, 3, 1, 3]
def baseStart_4877832 : Nat := 118140960795 + 4877832 * 2 ^ 59
def prefixEnd_4877832 : Nat := 4983230072969 + 3 ^ 40 * 4877832 * 2
def baseEnd_4877832 : Nat := 2504672367882064693567265

theorem tailTrace_4877832 : CollatzResearch.WordTrace tailWord_4877832 prefixEnd_4877832 2504672367882064693567265 := by
  unfold tailWord_4877832
  simp only [CollatzResearch.WordTrace]
  refine ⟨88954574432227603113413875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118606099242970137484551833 88954574432227603113413875)
  ·
    refine ⟨133431861648341404670120813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88954574432227603113413875 133431861648341404670120813)
    ·
      refine ⟨50036948118128026751295305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133431861648341404670120813 50036948118128026751295305)
      ·
        refine ⟨37527711088596020063471479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50036948118128026751295305 37527711088596020063471479)
        ·
          refine ⟨56291566632894030095207219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37527711088596020063471479 56291566632894030095207219)
          ·
            refine ⟨84437349949341045142810829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56291566632894030095207219 84437349949341045142810829)
            ·
              refine ⟨31664006231002891928554061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84437349949341045142810829 31664006231002891928554061)
              ·
                refine ⟨11874002336626084473207773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31664006231002891928554061 11874002336626084473207773)
                ·
                  refine ⟨4452750876234781677452915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11874002336626084473207773 4452750876234781677452915)
                  ·
                    refine ⟨6679126314352172516179373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4452750876234781677452915 6679126314352172516179373)
                    ·
                      refine ⟨2504672367882064693567265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6679126314352172516179373 2504672367882064693567265)
                      ·
                        rfl

theorem cell23_4877832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 3, 3, 3, 1, 3].length) (baseStart_4877832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877832 prefixEnd_4877832 := by exact prefixLift 4877832
  have htrace : WordTrace (prefixWord ++ tailWord_4877832) baseStart_4877832 baseEnd_4877832 := by
    simpa [prefixWord, tailWord_4877832, baseEnd_4877832] using wordTrace_append hprefix tailTrace_4877832
  have hstable : (prefixWord ++ tailWord_4877832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877832).length < 2 ^ (prefixWord ++ tailWord_4877832).sum := by decide
  have hdescent : baseEnd_4877832 < baseStart_4877832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877852 : List Nat := [2, 2, 3, 1, 2, 1, 4, 2, 1, 5]
def baseStart_4877852 : Nat := 118140960795 + 4877852 * 2 ^ 59
def prefixEnd_4877852 : Nat := 4983230072969 + 3 ^ 40 * 4877852 * 2
def baseEnd_4877852 : Nat := 834894212498384871772391

theorem tailTrace_4877852 : CollatzResearch.WordTrace tailWord_4877852 prefixEnd_4877852 834894212498384871772391 := by
  unfold tailWord_4877852
  simp only [CollatzResearch.WordTrace]
  refine ⟨88954939162191374821277905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118606585549588499761703873 88954939162191374821277905)
  ·
    refine ⟨66716204371643531115958429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88954939162191374821277905 66716204371643531115958429)
    ·
      refine ⟨25018576639366324168484411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66716204371643531115958429 25018576639366324168484411)
      ·
        refine ⟨37527864959049486252726617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25018576639366324168484411 37527864959049486252726617)
        ·
          refine ⟨28145898719287114689544963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37527864959049486252726617 28145898719287114689544963)
          ·
            refine ⟨42218848078930672034317445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28145898719287114689544963 42218848078930672034317445)
            ·
              refine ⟨7916034014799501006434521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42218848078930672034317445 7916034014799501006434521)
              ·
                refine ⟨5937025511099625754825891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7916034014799501006434521 5937025511099625754825891)
                ·
                  refine ⟨8905538266649438632238837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5937025511099625754825891 8905538266649438632238837)
                  ·
                    refine ⟨834894212498384871772391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8905538266649438632238837 834894212498384871772391)
                    ·
                      rfl

theorem cell23_4877852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 4, 2, 1, 5].length) (baseStart_4877852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877852 prefixEnd_4877852 := by exact prefixLift 4877852
  have htrace : WordTrace (prefixWord ++ tailWord_4877852) baseStart_4877852 baseEnd_4877852 := by
    simpa [prefixWord, tailWord_4877852, baseEnd_4877852] using wordTrace_append hprefix tailTrace_4877852
  have hstable : (prefixWord ++ tailWord_4877852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877852).length < 2 ^ (prefixWord ++ tailWord_4877852).sum := by decide
  have hdescent : baseEnd_4877852 < baseStart_4877852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877855 : List Nat := [1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 4]
def baseStart_4877855 : Nat := 118140960795 + 4877855 * 2 ^ 59
def prefixEnd_4877855 : Nat := 4983230072969 + 3 ^ 40 * 4877855 * 2
def baseEnd_4877855 : Nat := 2504684177937118103579659

theorem tailTrace_4877855 : CollatzResearch.WordTrace tailWord_4877855 prefixEnd_4877855 2504684177937118103579659 := by
  unfold tailWord_4877855
  simp only [CollatzResearch.WordTrace]
  refine ⟨177909987743371881154915019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118606658495581254103276679 177909987743371881154915019)
  ·
    refine ⟨266864981615057821732372529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177909987743371881154915019 266864981615057821732372529)
    ·
      refine ⟨200148736211293366299279397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266864981615057821732372529 200148736211293366299279397)
      ·
        refine ⟨37527888039617506181114887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200148736211293366299279397 37527888039617506181114887)
        ·
          refine ⟨56291832059426259271672331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37527888039617506181114887 56291832059426259271672331)
          ·
            refine ⟨84437748089139388907508497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56291832059426259271672331 84437748089139388907508497)
            ·
              refine ⟨63328311066854541680631373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84437748089139388907508497 63328311066854541680631373)
              ·
                refine ⟨23748116650070453130236765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63328311066854541680631373 23748116650070453130236765)
                ·
                  refine ⟨8905543743776419923838787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23748116650070453130236765 8905543743776419923838787)
                  ·
                    refine ⟨13358315615664629885758181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8905543743776419923838787 13358315615664629885758181)
                    ·
                      refine ⟨2504684177937118103579659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13358315615664629885758181 2504684177937118103579659)
                      ·
                        rfl

theorem cell23_4877855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 3, 3, 1, 4].length) (baseStart_4877855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877855 prefixEnd_4877855 := by exact prefixLift 4877855
  have htrace : WordTrace (prefixWord ++ tailWord_4877855) baseStart_4877855 baseEnd_4877855 := by
    simpa [prefixWord, tailWord_4877855, baseEnd_4877855] using wordTrace_append hprefix tailTrace_4877855
  have hstable : (prefixWord ++ tailWord_4877855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877855).length < 2 ^ (prefixWord ++ tailWord_4877855).sum := by decide
  have hdescent : baseEnd_4877855 < baseStart_4877855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877875 : List Nat := [1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 5]
def baseStart_4877875 : Nat := 118140960795 + 4877875 * 2 ^ 59
def prefixEnd_4877875 : Nat := 4983230072969 + 3 ^ 40 * 4877875 * 2
def baseEnd_4877875 : Nat := 2504694447550208025329567

theorem tailTrace_4877875 : CollatzResearch.WordTrace tailWord_4877875 prefixEnd_4877875 2504694447550208025329567 := by
  unfold tailWord_4877875
  simp only [CollatzResearch.WordTrace]
  refine ⟨177910717203299424570643079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118607144802199616380428719 177910717203299424570643079)
  ·
    refine ⟨266866075804949136855964619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177910717203299424570643079 266866075804949136855964619)
    ·
      refine ⟨400299113707423705283946929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266866075804949136855964619 400299113707423705283946929)
      ·
        refine ⟨300224335280567778962960197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400299113707423705283946929 300224335280567778962960197)
        ·
          refine ⟨56292062865106458555555037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 300224335280567778962960197 56292062865106458555555037)
          ·
            refine ⟨21109523574414921958333139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56292062865106458555555037 21109523574414921958333139)
            ·
              refine ⟨31664285361622382937499709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21109523574414921958333139 31664285361622382937499709)
              ·
                refine ⟨11874107010608393601562391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31664285361622382937499709 11874107010608393601562391)
                ·
                  refine ⟨17811160515912590402343587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11874107010608393601562391 17811160515912590402343587)
                  ·
                    refine ⟨26716740773868885603515381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17811160515912590402343587 26716740773868885603515381)
                    ·
                      refine ⟨2504694447550208025329567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26716740773868885603515381 2504694447550208025329567)
                      ·
                        rfl

theorem cell23_4877875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 1, 5].length) (baseStart_4877875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877875 prefixEnd_4877875 := by exact prefixLift 4877875
  have htrace : WordTrace (prefixWord ++ tailWord_4877875) baseStart_4877875 baseEnd_4877875 := by
    simpa [prefixWord, tailWord_4877875, baseEnd_4877875] using wordTrace_append hprefix tailTrace_4877875
  have hstable : (prefixWord ++ tailWord_4877875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877875).length < 2 ^ (prefixWord ++ tailWord_4877875).sum := by decide
  have hdescent : baseEnd_4877875 < baseStart_4877875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877882 : List Nat := [3, 1, 1, 1, 3, 2, 2, 4, 2, 4]
def baseStart_4877882 : Nat := 118140960795 + 4877882 * 2 ^ 59
def prefixEnd_4877882 : Nat := 4983230072969 + 3 ^ 40 * 4877882 * 2
def baseEnd_4877882 : Nat := 834899347304929832647345

theorem tailTrace_4877882 : CollatzResearch.WordTrace tailWord_4877882 prefixEnd_4877882 834899347304929832647345 := by
  unfold tailWord_4877882
  simp only [CollatzResearch.WordTrace]
  refine ⟨44477743128568516191536975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118607315009516043177431933 44477743128568516191536975)
  ·
    refine ⟨66716614692852774287305463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44477743128568516191536975 66716614692852774287305463)
    ·
      refine ⟨100074922039279161430958195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66716614692852774287305463 100074922039279161430958195)
      ·
        refine ⟨150112383058918742146437293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100074922039279161430958195 150112383058918742146437293)
        ·
          refine ⟨56292143647094528304913985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150112383058918742146437293 56292143647094528304913985)
          ·
            refine ⟨42219107735320896228685489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56292143647094528304913985 42219107735320896228685489)
            ·
              refine ⟨31664330801490672171514117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42219107735320896228685489 31664330801490672171514117)
              ·
                refine ⟨5937062025279501032158897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31664330801490672171514117 5937062025279501032158897)
                ·
                  refine ⟨4452796518959625774119173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5937062025279501032158897 4452796518959625774119173)
                  ·
                    refine ⟨834899347304929832647345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4452796518959625774119173 834899347304929832647345)
                    ·
                      rfl

theorem cell23_4877882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_4877882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877882 prefixEnd_4877882 := by exact prefixLift 4877882
  have htrace : WordTrace (prefixWord ++ tailWord_4877882) baseStart_4877882 baseEnd_4877882 := by
    simpa [prefixWord, tailWord_4877882, baseEnd_4877882] using wordTrace_append hprefix tailTrace_4877882
  have hstable : (prefixWord ++ tailWord_4877882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877882).length < 2 ^ (prefixWord ++ tailWord_4877882).sum := by decide
  have hdescent : baseEnd_4877882 < baseStart_4877882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877910 : List Nat := [5, 2, 2, 2, 1, 1, 2, 1, 2, 3, 2]
def baseStart_4877910 : Nat := 118140960795 + 4877910 * 2 ^ 59
def prefixEnd_4877910 : Nat := 4983230072969 + 3 ^ 40 * 4877910 * 2
def baseEnd_4877910 : Nat := 2504712419373115388391907

theorem tailTrace_4877910 : CollatzResearch.WordTrace tailWord_4877910 prefixEnd_4877910 2504712419373115388391907 := by
  unfold tailWord_4877910
  simp only [CollatzResearch.WordTrace]
  refine ⟨11119499609885789096760449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118607995838781750365444789 11119499609885789096760449)
  ·
    refine ⟨8339624707414341822570337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11119499609885789096760449 8339624707414341822570337)
    ·
      refine ⟨6254718530560756366927753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8339624707414341822570337 6254718530560756366927753)
      ·
        refine ⟨4691038897920567275195815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6254718530560756366927753 4691038897920567275195815)
        ·
          refine ⟨7036558346880850912793723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4691038897920567275195815 7036558346880850912793723)
          ·
            refine ⟨10554837520321276369190585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7036558346880850912793723 10554837520321276369190585)
            ·
              refine ⟨7916128140240957276892939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10554837520321276369190585 7916128140240957276892939)
              ·
                refine ⟨11874192210361435915339409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7916128140240957276892939 11874192210361435915339409)
                ·
                  refine ⟨8905644157771076936504557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11874192210361435915339409 8905644157771076936504557)
                  ·
                    refine ⟨3339616559164153851189209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8905644157771076936504557 3339616559164153851189209)
                    ·
                      refine ⟨2504712419373115388391907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3339616559164153851189209 2504712419373115388391907)
                      ·
                        rfl

theorem cell23_4877910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_4877910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877910 prefixEnd_4877910 := by exact prefixLift 4877910
  have htrace : WordTrace (prefixWord ++ tailWord_4877910) baseStart_4877910 baseEnd_4877910 := by
    simpa [prefixWord, tailWord_4877910, baseEnd_4877910] using wordTrace_append hprefix tailTrace_4877910
  have hstable : (prefixWord ++ tailWord_4877910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877910).length < 2 ^ (prefixWord ++ tailWord_4877910).sum := by decide
  have hdescent : baseEnd_4877910 < baseStart_4877910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877942 : List Nat := [5, 1, 1, 2, 2, 1, 1, 1, 2, 7]
def baseStart_4877942 : Nat := 118140960795 + 4877942 * 2 ^ 59
def prefixEnd_4877942 : Nat := 4983230072969 + 3 ^ 40 * 4877942 * 2
def baseEnd_4877942 : Nat := 834909616918019754397253

theorem tailTrace_4877942 : CollatzResearch.WordTrace tailWord_4877942 prefixEnd_4877942 834909616918019754397253 := by
  unfold tailWord_4877942
  simp only [CollatzResearch.WordTrace]
  refine ⟨11119572555878543438333255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118608773929371130008888053 11119572555878543438333255)
  ·
    refine ⟨16679358833817815157499883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11119572555878543438333255 16679358833817815157499883)
    ·
      refine ⟨25019038250726722736249825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16679358833817815157499883 25019038250726722736249825)
      ·
        refine ⟨18764278688045042052187369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25019038250726722736249825 18764278688045042052187369)
        ·
          refine ⟨14073209016033781539140527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18764278688045042052187369 14073209016033781539140527)
          ·
            refine ⟨21109813524050672308710791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14073209016033781539140527 21109813524050672308710791)
            ·
              refine ⟨31664720286076008463066187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21109813524050672308710791 31664720286076008463066187)
              ·
                refine ⟨47497080429114012694599281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31664720286076008463066187 47497080429114012694599281)
                ·
                  refine ⟨35622810321835509520949461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47497080429114012694599281 35622810321835509520949461)
                  ·
                    refine ⟨834909616918019754397253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35622810321835509520949461 834909616918019754397253)
                    ·
                      rfl

theorem cell23_4877942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 1, 1, 2, 7].length) (baseStart_4877942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877942 prefixEnd_4877942 := by exact prefixLift 4877942
  have htrace : WordTrace (prefixWord ++ tailWord_4877942) baseStart_4877942 baseEnd_4877942 := by
    simpa [prefixWord, tailWord_4877942, baseEnd_4877942] using wordTrace_append hprefix tailTrace_4877942
  have hstable : (prefixWord ++ tailWord_4877942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877942).length < 2 ^ (prefixWord ++ tailWord_4877942).sum := by decide
  have hdescent : baseEnd_4877942 < baseStart_4877942 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877945 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 1, 5, 4]
def baseStart_4877945 : Nat := 118140960795 + 4877945 * 2 ^ 59
def prefixEnd_4877945 : Nat := 4983230072969 + 3 ^ 40 * 4877945 * 2
def baseEnd_4877945 : Nat := 2504730391196022751454245

theorem tailTrace_4877945 : CollatzResearch.WordTrace tailWord_4877945 prefixEnd_4877945 2504730391196022751454245 := by
  unfold tailWord_4877945
  simp only [CollatzResearch.WordTrace]
  refine ⟨177913270313045826525691289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118608846875363884350460859 177913270313045826525691289)
  ·
    refine ⟨133434952734784369894268467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177913270313045826525691289 133434952734784369894268467)
    ·
      refine ⟨200152429102176554841402701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133434952734784369894268467 200152429102176554841402701)
      ·
        refine ⟨75057160913316208065526013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200152429102176554841402701 75057160913316208065526013)
        ·
          refine ⟨28146435342493578024572255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75057160913316208065526013 28146435342493578024572255)
          ·
            refine ⟨42219653013740367036858383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28146435342493578024572255 42219653013740367036858383)
            ·
              refine ⟨63329479520610550555287575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42219653013740367036858383 63329479520610550555287575)
              ·
                refine ⟨94994219280915825832931363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63329479520610550555287575 94994219280915825832931363)
                ·
                  refine ⟨142491328921373738749397045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 94994219280915825832931363 142491328921373738749397045)
                  ·
                    refine ⟨13358562086378788007755973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 142491328921373738749397045 13358562086378788007755973)
                    ·
                      refine ⟨2504730391196022751454245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13358562086378788007755973 2504730391196022751454245)
                      ·
                        rfl

theorem cell23_4877945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 1, 5, 4].length) (baseStart_4877945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877945 prefixEnd_4877945 := by exact prefixLift 4877945
  have htrace : WordTrace (prefixWord ++ tailWord_4877945) baseStart_4877945 baseEnd_4877945 := by
    simpa [prefixWord, tailWord_4877945, baseEnd_4877945] using wordTrace_append hprefix tailTrace_4877945
  have hstable : (prefixWord ++ tailWord_4877945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877945).length < 2 ^ (prefixWord ++ tailWord_4877945).sum := by decide
  have hdescent : baseEnd_4877945 < baseStart_4877945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877949 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 3, 3, 2]
def baseStart_4877949 : Nat := 118140960795 + 4877949 * 2 ^ 59
def prefixEnd_4877949 : Nat := 4983230072969 + 3 ^ 40 * 4877949 * 2
def baseEnd_4877949 : Nat := 2504732445118640735804227

theorem tailTrace_4877949 : CollatzResearch.WordTrace tailWord_4877949 prefixEnd_4877949 2504732445118640735804227 := by
  unfold tailWord_4877949
  simp only [CollatzResearch.WordTrace]
  refine ⟨177913416205031335208836901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118608944136687556805891267 177913416205031335208836901)
  ·
    refine ⟨33358765538443375351656919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177913416205031335208836901 33358765538443375351656919)
    ·
      refine ⟨50038148307665063027485379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33358765538443375351656919 50038148307665063027485379)
      ·
        refine ⟨75057222461497594541228069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50038148307665063027485379 75057222461497594541228069)
        ·
          refine ⟨14073229211530798976480263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75057222461497594541228069 14073229211530798976480263)
          ·
            refine ⟨21109843817296198464720395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14073229211530798976480263 21109843817296198464720395)
            ·
              refine ⟨31664765725944297697080593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21109843817296198464720395 31664765725944297697080593)
              ·
                refine ⟨23748574294458223272810445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31664765725944297697080593 23748574294458223272810445)
                ·
                  refine ⟨8905715360421833727303917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23748574294458223272810445 8905715360421833727303917)
                  ·
                    refine ⟨3339643260158187647738969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8905715360421833727303917 3339643260158187647738969)
                    ·
                      refine ⟨2504732445118640735804227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3339643260158187647738969 2504732445118640735804227)
                      ·
                        rfl

theorem cell23_4877949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 3, 3, 2].length) (baseStart_4877949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877949 prefixEnd_4877949 := by exact prefixLift 4877949
  have htrace : WordTrace (prefixWord ++ tailWord_4877949) baseStart_4877949 baseEnd_4877949 := by
    simpa [prefixWord, tailWord_4877949, baseEnd_4877949] using wordTrace_append hprefix tailTrace_4877949
  have hstable : (prefixWord ++ tailWord_4877949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877949).length < 2 ^ (prefixWord ++ tailWord_4877949).sum := by decide
  have hdescent : baseEnd_4877949 < baseStart_4877949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4877983 : List Nat := [1, 1, 2, 7, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4877983 : Nat := 118140960795 + 4877983 * 2 ^ 59
def prefixEnd_4877983 : Nat := 4983230072969 + 3 ^ 40 * 4877983 * 2
def baseEnd_4877983 : Nat := 2504749903460893602779071

theorem tailTrace_4877983 : CollatzResearch.WordTrace tailWord_4877983 prefixEnd_4877983 2504749903460893602779071 := by
  unfold tailWord_4877983
  simp only [CollatzResearch.WordTrace]
  refine ⟨177914656286908159015574603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118609770857938772677049735 177914656286908159015574603)
  ·
    refine ⟨266871984430362238523361905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177914656286908159015574603 266871984430362238523361905)
    ·
      refine ⟨200153988322771678892521429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266871984430362238523361905 200153988322771678892521429)
      ·
        refine ⟨4691109101314961224043471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 200153988322771678892521429 4691109101314961224043471)
        ·
          refine ⟨7036663651972441836065207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4691109101314961224043471 7036663651972441836065207)
          ·
            refine ⟨10554995477958662754097811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7036663651972441836065207 10554995477958662754097811)
            ·
              refine ⟨15832493216937994131146717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10554995477958662754097811 15832493216937994131146717)
              ·
                refine ⟨5937184956351747799180019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15832493216937994131146717 5937184956351747799180019)
                ·
                  refine ⟨8905777434527621698770029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5937184956351747799180019 8905777434527621698770029)
                  ·
                    refine ⟨3339666537947858137038761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8905777434527621698770029 3339666537947858137038761)
                    ·
                      refine ⟨2504749903460893602779071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3339666537947858137038761 2504749903460893602779071)
                      ·
                        rfl

theorem cell23_4877983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4877983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4877983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4877983 prefixEnd_4877983 := by exact prefixLift 4877983
  have htrace : WordTrace (prefixWord ++ tailWord_4877983) baseStart_4877983 baseEnd_4877983 := by
    simpa [prefixWord, tailWord_4877983, baseEnd_4877983] using wordTrace_append hprefix tailTrace_4877983
  have hstable : (prefixWord ++ tailWord_4877983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4877983).length < 2 ^ (prefixWord ++ tailWord_4877983).sum := by decide
  have hdescent : baseEnd_4877983 < baseStart_4877983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4877983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878013 : List Nat := [1, 4, 1, 2, 1, 2, 5, 1, 2, 2, 2]
def baseStart_4878013 : Nat := 118140960795 + 4878013 * 2 ^ 59
def prefixEnd_4878013 : Nat := 4983230072969 + 3 ^ 40 * 4878013 * 2
def baseEnd_4878013 : Nat := 2504765307880528485403933

theorem tailTrace_4878013 : CollatzResearch.WordTrace tailWord_4878013 prefixEnd_4878013 2504765307880528485403933 := by
  unfold tailWord_4878013
  simp only [CollatzResearch.WordTrace]
  refine ⟨177915750476799474139166693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118610500317866316092777795 177915750476799474139166693)
  ·
    refine ⟨33359203214399901401093755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177915750476799474139166693 33359203214399901401093755)
    ·
      refine ⟨50038804821599852101640633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33359203214399901401093755 50038804821599852101640633)
      ·
        refine ⟨37529103616199889076230475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50038804821599852101640633 37529103616199889076230475)
        ·
          refine ⟨56293655424299833614345713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37529103616199889076230475 56293655424299833614345713)
          ·
            refine ⟨42220241568224875210759285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56293655424299833614345713 42220241568224875210759285)
            ·
              refine ⟨3958147647021082051008683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42220241568224875210759285 3958147647021082051008683)
              ·
                refine ⟨5937221470531623076513025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3958147647021082051008683 5937221470531623076513025)
                ·
                  refine ⟨4452916102898717307384769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5937221470531623076513025 4452916102898717307384769)
                  ·
                    refine ⟨3339687077174037980538577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4452916102898717307384769 3339687077174037980538577)
                    ·
                      refine ⟨2504765307880528485403933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3339687077174037980538577 2504765307880528485403933)
                      ·
                        rfl

theorem cell23_4878013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 5, 1, 2, 2, 2].length) (baseStart_4878013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878013 prefixEnd_4878013 := by exact prefixLift 4878013
  have htrace : WordTrace (prefixWord ++ tailWord_4878013) baseStart_4878013 baseEnd_4878013 := by
    simpa [prefixWord, tailWord_4878013, baseEnd_4878013] using wordTrace_append hprefix tailTrace_4878013
  have hstable : (prefixWord ++ tailWord_4878013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878013).length < 2 ^ (prefixWord ++ tailWord_4878013).sum := by decide
  have hdescent : baseEnd_4878013 < baseStart_4878013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878015 : List Nat := [1, 1, 2, 2, 2, 3, 1, 1, 3, 7]
def baseStart_4878015 : Nat := 118140960795 + 4878015 * 2 ^ 59
def prefixEnd_4878015 : Nat := 4983230072969 + 3 ^ 40 * 4878015 * 2
def baseEnd_4878015 : Nat := 834922111613945825859641

theorem tailTrace_4878015 : CollatzResearch.WordTrace tailWord_4878015 prefixEnd_4878015 834922111613945825859641 := by
  unfold tailWord_4878015
  simp only [CollatzResearch.WordTrace]
  refine ⟨177915823422792228480739499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118610548948528152320492999 177915823422792228480739499)
  ·
    refine ⟨266873735134188342721109249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177915823422792228480739499 266873735134188342721109249)
    ·
      refine ⟨200155301350641257040831937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266873735134188342721109249 200155301350641257040831937)
      ·
        refine ⟨150116476012980942780623953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200155301350641257040831937 150116476012980942780623953)
        ·
          refine ⟨112587357009735707085467965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150116476012980942780623953 112587357009735707085467965)
          ·
            refine ⟨42220258878650890157050487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112587357009735707085467965 42220258878650890157050487)
            ·
              refine ⟨63330388317976335235575731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42220258878650890157050487 63330388317976335235575731)
              ·
                refine ⟨94995582476964502853363597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63330388317976335235575731 94995582476964502853363597)
                ·
                  refine ⟨35623343428861688570011349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 94995582476964502853363597 35623343428861688570011349)
                  ·
                    refine ⟨834922111613945825859641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35623343428861688570011349 834922111613945825859641)
                    ·
                      rfl

theorem cell23_4878015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_4878015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878015 prefixEnd_4878015 := by exact prefixLift 4878015
  have htrace : WordTrace (prefixWord ++ tailWord_4878015) baseStart_4878015 baseEnd_4878015 := by
    simpa [prefixWord, tailWord_4878015, baseEnd_4878015] using wordTrace_append hprefix tailTrace_4878015
  have hstable : (prefixWord ++ tailWord_4878015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878015).length < 2 ^ (prefixWord ++ tailWord_4878015).sum := by decide
  have hdescent : baseEnd_4878015 < baseStart_4878015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878036 : List Nat := [2, 4, 1, 3, 1, 1, 3, 3, 5]
def baseStart_4878036 : Nat := 118140960795 + 4878036 * 2 ^ 59
def prefixEnd_4878036 : Nat := 4983230072969 + 3 ^ 40 * 4878036 * 2
def baseEnd_4878036 : Nat := 278308568659509099490703

theorem tailTrace_4878036 : CollatzResearch.WordTrace tailWord_4878036 prefixEnd_4878036 278308568659509099490703 := by
  unfold tailWord_4878036
  simp only [CollatzResearch.WordTrace]
  refine ⟨88958294677858074533626981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118611059570477432711502641 88958294677858074533626981)
  ·
    refine ⟨16679680252098388975055059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88958294677858074533626981 16679680252098388975055059)
    ·
      refine ⟨25019520378147583462582589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16679680252098388975055059 25019520378147583462582589)
      ·
        refine ⟨9382320141805343798468471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25019520378147583462582589 9382320141805343798468471)
        ·
          refine ⟨14073480212708015697702707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9382320141805343798468471 14073480212708015697702707)
          ·
            refine ⟨21110220319062023546554061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14073480212708015697702707 21110220319062023546554061)
            ·
              refine ⟨7916332619648258829957773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21110220319062023546554061 7916332619648258829957773)
              ·
                refine ⟨2968624732368097061234165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7916332619648258829957773 2968624732368097061234165)
                ·
                  refine ⟨278308568659509099490703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2968624732368097061234165 278308568659509099490703)
                  ·
                    rfl

theorem cell23_4878036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_4878036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878036 prefixEnd_4878036 := by exact prefixLift 4878036
  have htrace : WordTrace (prefixWord ++ tailWord_4878036) baseStart_4878036 baseEnd_4878036 := by
    simpa [prefixWord, tailWord_4878036, baseEnd_4878036] using wordTrace_append hprefix tailTrace_4878036
  have hstable : (prefixWord ++ tailWord_4878036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878036).length < 2 ^ (prefixWord ++ tailWord_4878036).sum := by decide
  have hdescent : baseEnd_4878036 < baseStart_4878036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878049 : List Nat := [1, 2, 3, 1, 5, 1, 1, 2, 2, 5]
def baseStart_4878049 : Nat := 118140960795 + 4878049 * 2 ^ 59
def prefixEnd_4878049 : Nat := 4983230072969 + 3 ^ 40 * 4878049 * 2
def baseEnd_4878049 : Nat := 834927931061363448184589

theorem tailTrace_4878049 : CollatzResearch.WordTrace tailWord_4878049 prefixEnd_4878049 834927931061363448184589 := by
  unfold tailWord_4878049
  simp only [CollatzResearch.WordTrace]
  refine ⟨177917063504669052287477201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118611375669779368191651467 177917063504669052287477201)
  ·
    refine ⟨133437797628501789215607901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177917063504669052287477201 133437797628501789215607901)
    ·
      refine ⟨50039174110688170955852963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133437797628501789215607901 50039174110688170955852963)
      ·
        refine ⟨75058761166032256433779445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50039174110688170955852963 75058761166032256433779445)
        ·
          refine ⟨7036758859315524040666823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75058761166032256433779445 7036758859315524040666823)
          ·
            refine ⟨10555138288973286061000235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7036758859315524040666823 10555138288973286061000235)
            ·
              refine ⟨15832707433459929091500353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10555138288973286061000235 15832707433459929091500353)
              ·
                refine ⟨11874530575094946818625265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15832707433459929091500353 11874530575094946818625265)
                ·
                  refine ⟨8905897931321210113968949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11874530575094946818625265 8905897931321210113968949)
                  ·
                    refine ⟨834927931061363448184589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8905897931321210113968949 834927931061363448184589)
                    ·
                      rfl

theorem cell23_4878049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_4878049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878049 prefixEnd_4878049 := by exact prefixLift 4878049
  have htrace : WordTrace (prefixWord ++ tailWord_4878049) baseStart_4878049 baseEnd_4878049 := by
    simpa [prefixWord, tailWord_4878049, baseEnd_4878049] using wordTrace_append hprefix tailTrace_4878049
  have hstable : (prefixWord ++ tailWord_4878049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878049).length < 2 ^ (prefixWord ++ tailWord_4878049).sum := by decide
  have hdescent : baseEnd_4878049 < baseStart_4878049 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878072 : List Nat := [2, 1, 2, 1, 1, 2, 2, 4, 1, 4, 3]
def baseStart_4878072 : Nat := 118140960795 + 4878072 * 2 ^ 59
def prefixEnd_4878072 : Nat := 4983230072969 + 3 ^ 40 * 4878072 * 2
def baseEnd_4878072 : Nat := 2504795603239143754566161

theorem tailTrace_4878072 : CollatzResearch.WordTrace tailWord_4878072 prefixEnd_4878072 2504795603239143754566161 := by
  unfold tailWord_4878072
  simp only [CollatzResearch.WordTrace]
  refine ⟨88958951191792863607782235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118611934922390484810376313 88958951191792863607782235)
  ·
    refine ⟨133438426787689295411673353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88958951191792863607782235 133438426787689295411673353)
    ·
      refine ⟨100078820090766971558755015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133438426787689295411673353 100078820090766971558755015)
      ·
        refine ⟨150118230136150457338132523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100078820090766971558755015 150118230136150457338132523)
        ·
          refine ⟨225177345204225686007198785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150118230136150457338132523 225177345204225686007198785)
          ·
            refine ⟨168883008903169264505399089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 225177345204225686007198785 168883008903169264505399089)
            ·
              refine ⟨126662256677376948379049317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168883008903169264505399089 126662256677376948379049317)
              ·
                refine ⟨23749173127008177821071747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126662256677376948379049317 23749173127008177821071747)
                ·
                  refine ⟨35623759690512266731607621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23749173127008177821071747 35623759690512266731607621)
                  ·
                    refine ⟨6679454941971050012176429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35623759690512266731607621 6679454941971050012176429)
                    ·
                      refine ⟨2504795603239143754566161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6679454941971050012176429 2504795603239143754566161)
                      ·
                        rfl

theorem cell23_4878072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 4, 1, 4, 3].length) (baseStart_4878072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878072 prefixEnd_4878072 := by exact prefixLift 4878072
  have htrace : WordTrace (prefixWord ++ tailWord_4878072) baseStart_4878072 baseEnd_4878072 := by
    simpa [prefixWord, tailWord_4878072, baseEnd_4878072] using wordTrace_append hprefix tailTrace_4878072
  have hstable : (prefixWord ++ tailWord_4878072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878072).length < 2 ^ (prefixWord ++ tailWord_4878072).sum := by decide
  have hdescent : baseEnd_4878072 < baseStart_4878072 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878075 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 10]
def baseStart_4878075 : Nat := 118140960795 + 4878075 * 2 ^ 59
def prefixEnd_4878075 : Nat := 4983230072969 + 3 ^ 40 * 4878075 * 2
def baseEnd_4878075 : Nat := 278310793742345249203183

theorem tailTrace_4878075 : CollatzResearch.WordTrace tailWord_4878075 prefixEnd_4878075 278310793742345249203183 := by
  unfold tailWord_4878075
  simp only [CollatzResearch.WordTrace]
  refine ⟨177918011802574858727923679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118612007868383239151949119 177918011802574858727923679)
  ·
    refine ⟨266877017703862288091885519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177918011802574858727923679 266877017703862288091885519)
    ·
      refine ⟨400315526555793432137828279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266877017703862288091885519 400315526555793432137828279)
      ·
        refine ⟨600473289833690148206742419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400315526555793432137828279 600473289833690148206742419)
        ·
          refine ⟨900709934750535222310113629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600473289833690148206742419 900709934750535222310113629)
          ·
            refine ⟨337766225531450708366292611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 900709934750535222310113629 337766225531450708366292611)
            ·
              refine ⟨506649338297176062549438917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337766225531450708366292611 506649338297176062549438917)
              ·
                refine ⟨94996750930720511728019797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 506649338297176062549438917 94996750930720511728019797)
                ·
                  refine ⟨278310793742345249203183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 94996750930720511728019797 278310793742345249203183)
                  ·
                    rfl

theorem cell23_4878075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 10].length) (baseStart_4878075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878075 prefixEnd_4878075 := by exact prefixLift 4878075
  have htrace : WordTrace (prefixWord ++ tailWord_4878075) baseStart_4878075 baseEnd_4878075 := by
    simpa [prefixWord, tailWord_4878075, baseEnd_4878075] using wordTrace_append hprefix tailTrace_4878075
  have hstable : (prefixWord ++ tailWord_4878075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878075).length < 2 ^ (prefixWord ++ tailWord_4878075).sum := by decide
  have hdescent : baseEnd_4878075 < baseStart_4878075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878112 : List Nat := [2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 6]
def baseStart_4878112 : Nat := 118140960795 + 4878112 * 2 ^ 59
def prefixEnd_4878112 : Nat := 4983230072969 + 3 ^ 40 * 4878112 * 2
def baseEnd_4878112 : Nat := 2504816142465323598065977

theorem tailTrace_4878112 : CollatzResearch.WordTrace tailWord_4878112 prefixEnd_4878112 2504816142465323598065977 := by
  unfold tailWord_4878112
  simp only [CollatzResearch.WordTrace]
  refine ⟨88959680651720407023510295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118612907535627209364680393 88959680651720407023510295)
  ·
    refine ⟨133439520977580610535265443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88959680651720407023510295 133439520977580610535265443)
    ·
      refine ⟨200159281466370915802898165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133439520977580610535265443 200159281466370915802898165)
      ·
        refine ⟨18764932637472273356521703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200159281466370915802898165 18764932637472273356521703)
        ·
          refine ⟨28147398956208410034782555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18764932637472273356521703 28147398956208410034782555)
          ·
            refine ⟨42221098434312615052173833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28147398956208410034782555 42221098434312615052173833)
            ·
              refine ⟨31665823825734461289130375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42221098434312615052173833 31665823825734461289130375)
              ·
                refine ⟨47498735738601691933695563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31665823825734461289130375 47498735738601691933695563)
                ·
                  refine ⟨71248103607902537900543345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47498735738601691933695563 71248103607902537900543345)
                  ·
                    refine ⟨53436077705926903425407509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 71248103607902537900543345 53436077705926903425407509)
                    ·
                      refine ⟨2504816142465323598065977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53436077705926903425407509 2504816142465323598065977)
                      ·
                        rfl

theorem cell23_4878112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_4878112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878112 prefixEnd_4878112 := by exact prefixLift 4878112
  have htrace : WordTrace (prefixWord ++ tailWord_4878112) baseStart_4878112 baseEnd_4878112 := by
    simpa [prefixWord, tailWord_4878112, baseEnd_4878112] using wordTrace_append hprefix tailTrace_4878112
  have hstable : (prefixWord ++ tailWord_4878112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878112).length < 2 ^ (prefixWord ++ tailWord_4878112).sum := by decide
  have hdescent : baseEnd_4878112 < baseStart_4878112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878113 : List Nat := [1, 2, 3, 2, 1, 3, 4, 2, 1, 4]
def baseStart_4878113 : Nat := 118140960795 + 4878113 * 2 ^ 59
def prefixEnd_4878113 : Nat := 4983230072969 + 3 ^ 40 * 4878113 * 2
def baseEnd_4878113 : Nat := 834938885315326031384491

theorem tailTrace_4878113 : CollatzResearch.WordTrace tailWord_4878113 prefixEnd_4878113 834938885315326031384491 := by
  unfold tailWord_4878113
  simp only [CollatzResearch.WordTrace]
  refine ⟨177919397776437191217806993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118612931850958127478537995 177919397776437191217806993)
  ·
    refine ⟨133439548332327893413355245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177919397776437191217806993 133439548332327893413355245)
    ·
      refine ⟨50039830624622960030008217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133439548332327893413355245 50039830624622960030008217)
      ·
        refine ⟨37529872968467220022506163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50039830624622960030008217 37529872968467220022506163)
        ·
          refine ⟨56294809452700830033759245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37529872968467220022506163 56294809452700830033759245)
          ·
            refine ⟨21110553544762811262659717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56294809452700830033759245 21110553544762811262659717)
            ·
              refine ⟨3958228789643027111748697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21110553544762811262659717 3958228789643027111748697)
              ·
                refine ⟨2968671592232270333811523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3958228789643027111748697 2968671592232270333811523)
                ·
                  refine ⟨4453007388348405500717285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968671592232270333811523 4453007388348405500717285)
                  ·
                    refine ⟨834938885315326031384491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4453007388348405500717285 834938885315326031384491)
                    ·
                      rfl

theorem cell23_4878113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 2, 1, 4].length) (baseStart_4878113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878113 prefixEnd_4878113 := by exact prefixLift 4878113
  have htrace : WordTrace (prefixWord ++ tailWord_4878113) baseStart_4878113 baseEnd_4878113 := by
    simpa [prefixWord, tailWord_4878113, baseEnd_4878113] using wordTrace_append hprefix tailTrace_4878113
  have hstable : (prefixWord ++ tailWord_4878113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878113).length < 2 ^ (prefixWord ++ tailWord_4878113).sum := by decide
  have hdescent : baseEnd_4878113 < baseStart_4878113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878136 : List Nat := [2, 1, 2, 1, 3, 4, 1, 2, 3, 1, 3]
def baseStart_4878136 : Nat := 118140960795 + 4878136 * 2 ^ 59
def prefixEnd_4878136 : Nat := 4983230072969 + 3 ^ 40 * 4878136 * 2
def baseEnd_4878136 : Nat := 2504828466001031504165867

theorem tailTrace_4878136 : CollatzResearch.WordTrace tailWord_4878136 prefixEnd_4878136 2504828466001031504165867 := by
  unfold tailWord_4878136
  simp only [CollatzResearch.WordTrace]
  refine ⟨88960118327676933072947131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118613491103569244097262841 88960118327676933072947131)
  ·
    refine ⟨133440177491515399609420697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88960118327676933072947131 133440177491515399609420697)
    ·
      refine ⟨100080133118636549707065523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133440177491515399609420697 100080133118636549707065523)
      ·
        refine ⟨150120199677954824560598285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100080133118636549707065523 150120199677954824560598285)
        ·
          refine ⟨56295074879233059210224357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150120199677954824560598285 56295074879233059210224357)
          ·
            refine ⟨10555326539856198601917067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56295074879233059210224357 10555326539856198601917067)
            ·
              refine ⟨15832989809784297902875601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10555326539856198601917067 15832989809784297902875601)
              ·
                refine ⟨11874742357338223427156701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15832989809784297902875601 11874742357338223427156701)
                ·
                  refine ⟨4453028384001833785183763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11874742357338223427156701 4453028384001833785183763)
                  ·
                    refine ⟨6679542576002750677775645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4453028384001833785183763 6679542576002750677775645)
                    ·
                      refine ⟨2504828466001031504165867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6679542576002750677775645 2504828466001031504165867)
                      ·
                        rfl

theorem cell23_4878136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 1, 2, 3, 1, 3].length) (baseStart_4878136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878136 prefixEnd_4878136 := by exact prefixLift 4878136
  have htrace : WordTrace (prefixWord ++ tailWord_4878136) baseStart_4878136 baseEnd_4878136 := by
    simpa [prefixWord, tailWord_4878136, baseEnd_4878136] using wordTrace_append hprefix tailTrace_4878136
  have hstable : (prefixWord ++ tailWord_4878136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878136).length < 2 ^ (prefixWord ++ tailWord_4878136).sum := by decide
  have hdescent : baseEnd_4878136 < baseStart_4878136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878153 : List Nat := [1, 2, 1, 1, 2, 4, 4, 3, 1, 1, 3]
def baseStart_4878153 : Nat := 118140960795 + 4878153 * 2 ^ 59
def prefixEnd_4878153 : Nat := 4983230072969 + 3 ^ 40 * 4878153 * 2
def baseEnd_4878153 : Nat := 2504837195172157937653289

theorem tailTrace_4878153 : CollatzResearch.WordTrace tailWord_4878153 prefixEnd_4878153 2504837195172157937653289 := by
  unfold tailWord_4878153
  simp only [CollatzResearch.WordTrace]
  refine ⟨177920856696292278049263113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118613904464194852032842075 177920856696292278049263113)
  ·
    refine ⟨133440642522219208536947335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177920856696292278049263113 133440642522219208536947335)
    ·
      refine ⟨200160963783328812805421003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133440642522219208536947335 200160963783328812805421003)
      ·
        refine ⟨300241445674993219208131505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200160963783328812805421003 300241445674993219208131505)
        ·
          refine ⟨225181084256244914406098629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300241445674993219208131505 225181084256244914406098629)
          ·
            refine ⟨42221453298045921451143493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225181084256244914406098629 42221453298045921451143493)
            ·
              refine ⟨7916522493383610272089405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42221453298045921451143493 7916522493383610272089405)
              ·
                refine ⟨2968695935018853852033527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7916522493383610272089405 2968695935018853852033527)
                ·
                  refine ⟨4453043902528280778050291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968695935018853852033527 4453043902528280778050291)
                  ·
                    refine ⟨6679565853792421167075437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4453043902528280778050291 6679565853792421167075437)
                    ·
                      refine ⟨2504837195172157937653289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6679565853792421167075437 2504837195172157937653289)
                      ·
                        rfl

theorem cell23_4878153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 3, 1, 1, 3].length) (baseStart_4878153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878153 prefixEnd_4878153 := by exact prefixLift 4878153
  have htrace : WordTrace (prefixWord ++ tailWord_4878153) baseStart_4878153 baseEnd_4878153 := by
    simpa [prefixWord, tailWord_4878153, baseEnd_4878153] using wordTrace_append hprefix tailTrace_4878153
  have hstable : (prefixWord ++ tailWord_4878153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878153).length < 2 ^ (prefixWord ++ tailWord_4878153).sum := by decide
  have hdescent : baseEnd_4878153 < baseStart_4878153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878156 : List Nat := [2, 2, 1, 3, 4, 1, 1, 3, 1, 5]
def baseStart_4878156 : Nat := 118140960795 + 4878156 * 2 ^ 59
def prefixEnd_4878156 : Nat := 4983230072969 + 3 ^ 40 * 4878156 * 2
def baseEnd_4878156 : Nat := 834946245204707141971925

theorem tailTrace_4878156 : CollatzResearch.WordTrace tailWord_4878156 prefixEnd_4878156 834946245204707141971925 := by
  unfold tailWord_4878156
  simp only [CollatzResearch.WordTrace]
  refine ⟨88960483057640704780811161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118613977410187606374414881 88960483057640704780811161)
  ·
    refine ⟨66720362293230528585608371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88960483057640704780811161 66720362293230528585608371)
    ·
      refine ⟨100080543439845792878412557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66720362293230528585608371 100080543439845792878412557)
      ·
        refine ⟨37530203789942172329404709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100080543439845792878412557 37530203789942172329404709)
        ·
          refine ⟨7036913210614157311763383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37530203789942172329404709 7036913210614157311763383)
          ·
            refine ⟨10555369815921235967645075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7036913210614157311763383 10555369815921235967645075)
            ·
              refine ⟨15833054723881853951467613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10555369815921235967645075 15833054723881853951467613)
              ·
                refine ⟨5937395521455695231800355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15833054723881853951467613 5937395521455695231800355)
                ·
                  refine ⟨8906093282183542847700533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5937395521455695231800355 8906093282183542847700533)
                  ·
                    refine ⟨834946245204707141971925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8906093282183542847700533 834946245204707141971925)
                    ·
                      rfl

theorem cell23_4878156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 3, 1, 5].length) (baseStart_4878156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878156 prefixEnd_4878156 := by exact prefixLift 4878156
  have htrace : WordTrace (prefixWord ++ tailWord_4878156) baseStart_4878156 baseEnd_4878156 := by
    simpa [prefixWord, tailWord_4878156, baseEnd_4878156] using wordTrace_append hprefix tailTrace_4878156
  have hstable : (prefixWord ++ tailWord_4878156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878156).length < 2 ^ (prefixWord ++ tailWord_4878156).sum := by decide
  have hdescent : baseEnd_4878156 < baseStart_4878156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878169 : List Nat := [1, 2, 1, 2, 2, 3, 3, 1, 4, 4]
def baseStart_4878169 : Nat := 118140960795 + 4878169 * 2 ^ 59
def prefixEnd_4878169 : Nat := 4983230072969 + 3 ^ 40 * 4878169 * 2
def baseEnd_4878169 : Nat := 834948470287543291684405

theorem tailTrace_4878169 : CollatzResearch.WordTrace tailWord_4878169 prefixEnd_4878169 834948470287543291684405 := by
  unfold tailWord_4878169
  simp only [CollatzResearch.WordTrace]
  refine ⟨177921440264234312781845561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118614293509489541854563707 177921440264234312781845561)
  ·
    refine ⟨133441080198175734586384171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177921440264234312781845561 133441080198175734586384171)
    ·
      refine ⟨200161620297263601879576257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133441080198175734586384171 200161620297263601879576257)
      ·
        refine ⟨150121215222947701409682193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200161620297263601879576257 150121215222947701409682193)
        ·
          refine ⟨112590911417210776057261645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150121215222947701409682193 112590911417210776057261645)
          ·
            refine ⟨42221591781454041021473117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112590911417210776057261645 42221591781454041021473117)
            ·
              refine ⟨15833096918045265383052419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42221591781454041021473117 15833096918045265383052419)
              ·
                refine ⟨23749645377067898074578629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15833096918045265383052419 23749645377067898074578629)
                ·
                  refine ⟨4453058508200230888983493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23749645377067898074578629 4453058508200230888983493)
                  ·
                    refine ⟨834948470287543291684405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4453058508200230888983493 834948470287543291684405)
                    ·
                      rfl

theorem cell23_4878169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 1, 4, 4].length) (baseStart_4878169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878169 prefixEnd_4878169 := by exact prefixLift 4878169
  have htrace : WordTrace (prefixWord ++ tailWord_4878169) baseStart_4878169 baseEnd_4878169 := by
    simpa [prefixWord, tailWord_4878169, baseEnd_4878169] using wordTrace_append hprefix tailTrace_4878169
  have hstable : (prefixWord ++ tailWord_4878169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878169).length < 2 ^ (prefixWord ++ tailWord_4878169).sum := by decide
  have hdescent : baseEnd_4878169 < baseStart_4878169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878216 : List Nat := [2, 1, 3, 3, 4, 1, 9]
def baseStart_4878216 : Nat := 118140960795 + 4878216 * 2 ^ 59
def prefixEnd_4878216 : Nat := 4983230072969 + 3 ^ 40 * 4878216 * 2
def baseEnd_4878216 : Nat := 30924315363622113471179

theorem tailTrace_4878216 : CollatzResearch.WordTrace tailWord_4878216 prefixEnd_4878216 30924315363622113471179 := by
  unfold tailWord_4878216
  simp only [CollatzResearch.WordTrace]
  refine ⟨88961577247532019904403251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118615436330042693205871001 88961577247532019904403251)
  ·
    refine ⟨133442365871298029856604877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88961577247532019904403251 133442365871298029856604877)
    ·
      refine ⟨50040887201736761196226829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133442365871298029856604877 50040887201736761196226829)
      ·
        refine ⟨18765332700651285448585061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50040887201736761196226829 18765332700651285448585061)
        ·
          refine ⟨3518499881372116021609699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18765332700651285448585061 3518499881372116021609699)
          ·
            refine ⟨5277749822058174032414549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3518499881372116021609699 5277749822058174032414549)
            ·
              refine ⟨30924315363622113471179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5277749822058174032414549 30924315363622113471179)
              ·
                rfl

theorem cell23_4878216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 9].length) (baseStart_4878216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878216 prefixEnd_4878216 := by exact prefixLift 4878216
  have htrace : WordTrace (prefixWord ++ tailWord_4878216) baseStart_4878216 baseEnd_4878216 := by
    simpa [prefixWord, tailWord_4878216, baseEnd_4878216] using wordTrace_append hprefix tailTrace_4878216
  have hstable : (prefixWord ++ tailWord_4878216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878216).length < 2 ^ (prefixWord ++ tailWord_4878216).sum := by decide
  have hdescent : baseEnd_4878216 < baseStart_4878216 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878260 : List Nat := [2, 5, 2, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_4878260 : Nat := 118140960795 + 4878260 * 2 ^ 59
def prefixEnd_4878260 : Nat := 4983230072969 + 3 ^ 40 * 4878260 * 2
def baseEnd_4878260 : Nat := 2504892137602189019015297

theorem tailTrace_4878260 : CollatzResearch.WordTrace tailWord_4878260 prefixEnd_4878260 2504892137602189019015297 := by
  unfold tailWord_4878260
  simp only [CollatzResearch.WordTrace]
  refine ⟨88962379653452317661704117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118616506204603090215605489 88962379653452317661704117)
  ·
    refine ⟨8340223092511154780784761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88962379653452317661704117 8340223092511154780784761)
    ·
      refine ⟨6255167319383366085588571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8340223092511154780784761 6255167319383366085588571)
      ·
        refine ⟨9382750979075049128382857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6255167319383366085588571 9382750979075049128382857)
        ·
          refine ⟨7037063234306286846287143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9382750979075049128382857 7037063234306286846287143)
          ·
            refine ⟨10555594851459430269430715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7037063234306286846287143 10555594851459430269430715)
            ·
              refine ⟨15833392277189145404146073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10555594851459430269430715 15833392277189145404146073)
              ·
                refine ⟨11875044207891859053109555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15833392277189145404146073 11875044207891859053109555)
                ·
                  refine ⟨17812566311837788579664333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11875044207891859053109555 17812566311837788579664333)
                  ·
                    refine ⟨6679712366939170717374125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17812566311837788579664333 6679712366939170717374125)
                    ·
                      refine ⟨2504892137602189019015297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6679712366939170717374125 2504892137602189019015297)
                      ·
                        rfl

theorem cell23_4878260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_4878260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878260 prefixEnd_4878260 := by exact prefixLift 4878260
  have htrace : WordTrace (prefixWord ++ tailWord_4878260) baseStart_4878260 baseEnd_4878260 := by
    simpa [prefixWord, tailWord_4878260, baseEnd_4878260] using wordTrace_append hprefix tailTrace_4878260
  have hstable : (prefixWord ++ tailWord_4878260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878260).length < 2 ^ (prefixWord ++ tailWord_4878260).sum := by decide
  have hdescent : baseEnd_4878260 < baseStart_4878260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878279 : List Nat := [1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 4]
def baseStart_4878279 : Nat := 118140960795 + 4878279 * 2 ^ 59
def prefixEnd_4878279 : Nat := 4983230072969 + 3 ^ 40 * 4878279 * 2
def baseEnd_4878279 : Nat := 2504901893734624444677709

theorem tailTrace_4878279 : CollatzResearch.WordTrace tailWord_4878279 prefixEnd_4878279 2504901893734624444677709 := by
  unfold tailWord_4878279
  simp only [CollatzResearch.WordTrace]
  refine ⟨177925452293835801568349891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118616968195890534378899927 177925452293835801568349891)
  ·
    refine ⟨266888178440753702352524837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177925452293835801568349891 266888178440753702352524837)
    ·
      refine ⟨50041533457641319191098407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266888178440753702352524837 50041533457641319191098407)
      ·
        refine ⟨75062300186461978786647611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50041533457641319191098407 75062300186461978786647611)
        ·
          refine ⟨112593450279692968179971417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75062300186461978786647611 112593450279692968179971417)
          ·
            refine ⟨84445087709769726134978563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112593450279692968179971417 84445087709769726134978563)
            ·
              refine ⟨126667631564654589202467845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84445087709769726134978563 126667631564654589202467845)
              ·
                refine ⟨23750180918372735475462721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126667631564654589202467845 23750180918372735475462721)
                ·
                  refine ⟨17812635688779551606597041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23750180918372735475462721 17812635688779551606597041)
                  ·
                    refine ⟨13359476766584663704947781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17812635688779551606597041 13359476766584663704947781)
                    ·
                      refine ⟨2504901893734624444677709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13359476766584663704947781 2504901893734624444677709)
                      ·
                        rfl

theorem cell23_4878279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 4, 2, 2, 4].length) (baseStart_4878279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878279 prefixEnd_4878279 := by exact prefixLift 4878279
  have htrace : WordTrace (prefixWord ++ tailWord_4878279) baseStart_4878279 baseEnd_4878279 := by
    simpa [prefixWord, tailWord_4878279, baseEnd_4878279] using wordTrace_append hprefix tailTrace_4878279
  have hstable : (prefixWord ++ tailWord_4878279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878279).length < 2 ^ (prefixWord ++ tailWord_4878279).sum := by decide
  have hdescent : baseEnd_4878279 < baseStart_4878279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878319 : List Nat := [1, 1, 2, 1, 4, 2, 3, 1, 1, 7]
def baseStart_4878319 : Nat := 118140960795 + 4878319 * 2 ^ 59
def prefixEnd_4878319 : Nat := 4983230072969 + 3 ^ 40 * 4878319 * 2
def baseEnd_4878319 : Nat := 834974144320268096059175

theorem tailTrace_4878319 : CollatzResearch.WordTrace tailWord_4878319 prefixEnd_4878319 834974144320268096059175 := by
  unfold tailWord_4878319
  simp only [CollatzResearch.WordTrace]
  refine ⟨177926911213690888399806011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118617940809127258933204007 177926911213690888399806011)
  ·
    refine ⟨266890366820536332599709017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177926911213690888399806011 266890366820536332599709017)
    ·
      refine ⟨200167775115402249449781763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266890366820536332599709017 200167775115402249449781763)
      ·
        refine ⟨300251662673103374174672645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200167775115402249449781763 300251662673103374174672645)
        ·
          refine ⟨56297186751206882657751121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 300251662673103374174672645 56297186751206882657751121)
          ·
            refine ⟨42222890063405161993313341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56297186751206882657751121 42222890063405161993313341)
            ·
              refine ⟨15833583773776935747492503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42222890063405161993313341 15833583773776935747492503)
              ·
                refine ⟨23750375660665403621238755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15833583773776935747492503 23750375660665403621238755)
                ·
                  refine ⟨35625563490998105431858133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23750375660665403621238755 35625563490998105431858133)
                  ·
                    refine ⟨834974144320268096059175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35625563490998105431858133 834974144320268096059175)
                    ·
                      rfl

theorem cell23_4878319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_4878319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878319 prefixEnd_4878319 := by exact prefixLift 4878319
  have htrace : WordTrace (prefixWord ++ tailWord_4878319) baseStart_4878319 baseEnd_4878319 := by
    simpa [prefixWord, tailWord_4878319, baseEnd_4878319] using wordTrace_append hprefix tailTrace_4878319
  have hstable : (prefixWord ++ tailWord_4878319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878319).length < 2 ^ (prefixWord ++ tailWord_4878319).sum := by decide
  have hdescent : baseEnd_4878319 < baseStart_4878319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878334 : List Nat := [4, 2, 2, 2, 1, 3, 1, 2, 2, 2, 2]
def baseStart_4878334 : Nat := 118140960795 + 4878334 * 2 ^ 59
def prefixEnd_4878334 : Nat := 4983230072969 + 3 ^ 40 * 4878334 * 2
def baseEnd_4878334 : Nat := 2504930135170621729489957

theorem tailTrace_4878334 : CollatzResearch.WordTrace tailWord_4878334 prefixEnd_4878334 2504930135170621729489957 := by
  unfold tailWord_4878334
  simp only [CollatzResearch.WordTrace]
  refine ⟨22240932288579568245200257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118618305539091030641068037 22240932288579568245200257)
  ·
    refine ⟨16680699216434676183900193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22240932288579568245200257 16680699216434676183900193)
    ·
      refine ⟨12510524412326007137925145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16680699216434676183900193 12510524412326007137925145)
      ·
        refine ⟨9382893309244505353443859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12510524412326007137925145 9382893309244505353443859)
        ·
          refine ⟨14074339963866758030165789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9382893309244505353443859 14074339963866758030165789)
          ·
            refine ⟨5277877486450034261312171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14074339963866758030165789 5277877486450034261312171)
            ·
              refine ⟨7916816229675051391968257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5277877486450034261312171 7916816229675051391968257)
              ·
                refine ⟨5937612172256288543976193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7916816229675051391968257 5937612172256288543976193)
                ·
                  refine ⟨4453209129192216407982145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5937612172256288543976193 4453209129192216407982145)
                  ·
                    refine ⟨3339906846894162305986609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4453209129192216407982145 3339906846894162305986609)
                    ·
                      refine ⟨2504930135170621729489957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3339906846894162305986609 2504930135170621729489957)
                      ·
                        rfl

theorem cell23_4878334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_4878334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878334 prefixEnd_4878334 := by exact prefixLift 4878334
  have htrace : WordTrace (prefixWord ++ tailWord_4878334) baseStart_4878334 baseEnd_4878334 := by
    simpa [prefixWord, tailWord_4878334, baseEnd_4878334] using wordTrace_append hprefix tailTrace_4878334
  have hstable : (prefixWord ++ tailWord_4878334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878334).length < 2 ^ (prefixWord ++ tailWord_4878334).sum := by decide
  have hdescent : baseEnd_4878334 < baseStart_4878334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878383 : List Nat := [1, 1, 2, 1, 2, 1, 1, 9, 1, 4]
def baseStart_4878383 : Nat := 118140960795 + 4878383 * 2 ^ 59
def prefixEnd_4878383 : Nat := 4983230072969 + 3 ^ 40 * 4878383 * 2
def baseEnd_4878383 : Nat := 834985098574230679259077

theorem tailTrace_4878383 : CollatzResearch.WordTrace tailWord_4878383 prefixEnd_4878383 834985098574230679259077 := by
  unfold tailWord_4878383
  simp only [CollatzResearch.WordTrace]
  refine ⟨177929245485459027330135803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118619496990306018220090535 177929245485459027330135803)
  ·
    refine ⟨266893868228188540995203705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177929245485459027330135803 266893868228188540995203705)
    ·
      refine ⟨200170401171141405746402779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266893868228188540995203705 200170401171141405746402779)
      ·
        refine ⟨300255601756712108619604169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200170401171141405746402779 300255601756712108619604169)
        ·
          refine ⟨225191701317534081464703127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300255601756712108619604169 225191701317534081464703127)
          ·
            refine ⟨337787551976301122197054691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225191701317534081464703127 337787551976301122197054691)
            ·
              refine ⟨506681327964451683295582037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337787551976301122197054691 506681327964451683295582037)
              ·
                refine ⟨2968835906041709081810051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 506681327964451683295582037 2968835906041709081810051)
                ·
                  refine ⟨4453253859062563622715077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968835906041709081810051 4453253859062563622715077)
                  ·
                    refine ⟨834985098574230679259077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4453253859062563622715077 834985098574230679259077)
                    ·
                      rfl

theorem cell23_4878383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 9, 1, 4].length) (baseStart_4878383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878383 prefixEnd_4878383 := by exact prefixLift 4878383
  have htrace : WordTrace (prefixWord ++ tailWord_4878383) baseStart_4878383 baseEnd_4878383 := by
    simpa [prefixWord, tailWord_4878383, baseEnd_4878383] using wordTrace_append hprefix tailTrace_4878383
  have hstable : (prefixWord ++ tailWord_4878383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878383).length < 2 ^ (prefixWord ++ tailWord_4878383).sum := by decide
  have hdescent : baseEnd_4878383 < baseStart_4878383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878396 : List Nat := [2, 2, 2, 2, 2, 1, 2, 4, 6]
def baseStart_4878396 : Nat := 118140960795 + 4878396 * 2 ^ 59
def prefixEnd_4878396 : Nat := 4983230072969 + 3 ^ 40 * 4878396 * 2
def baseEnd_4878396 : Nat := 278329107885688942990519

theorem tailTrace_4878396 : CollatzResearch.WordTrace tailWord_4878396 prefixEnd_4878396 278329107885688942990519 := by
  unfold tailWord_4878396
  simp only [CollatzResearch.WordTrace]
  refine ⟨88964859817205965275179521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118619813089607953700239361 88964859817205965275179521)
  ·
    refine ⟨66723644862904473956384641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88964859817205965275179521 66723644862904473956384641)
    ·
      refine ⟨50042733647178355467288481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66723644862904473956384641 50042733647178355467288481)
      ·
        refine ⟨37532050235383766600466361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50042733647178355467288481 37532050235383766600466361)
        ·
          refine ⟨28149037676537824950349771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37532050235383766600466361 28149037676537824950349771)
          ·
            refine ⟨42223556514806737425524657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28149037676537824950349771 42223556514806737425524657)
            ·
              refine ⟨31667667386105053069143493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42223556514806737425524657 31667667386105053069143493)
              ·
                refine ⟨5937687634894697450464405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31667667386105053069143493 5937687634894697450464405)
                ·
                  refine ⟨278329107885688942990519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5937687634894697450464405 278329107885688942990519)
                  ·
                    rfl

theorem cell23_4878396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 2, 4, 6].length) (baseStart_4878396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878396 prefixEnd_4878396 := by exact prefixLift 4878396
  have htrace : WordTrace (prefixWord ++ tailWord_4878396) baseStart_4878396 baseEnd_4878396 := by
    simpa [prefixWord, tailWord_4878396, baseEnd_4878396] using wordTrace_append hprefix tailTrace_4878396
  have hstable : (prefixWord ++ tailWord_4878396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878396).length < 2 ^ (prefixWord ++ tailWord_4878396).sum := by decide
  have hdescent : baseEnd_4878396 < baseStart_4878396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878399 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 8]
def baseStart_4878399 : Nat := 118140960795 + 4878399 * 2 ^ 59
def prefixEnd_4878399 : Nat := 4983230072969 + 3 ^ 40 * 4878399 * 2
def baseEnd_4878399 : Nat := 2504963511413163975177157

theorem tailTrace_4878399 : CollatzResearch.WordTrace tailWord_4878399 prefixEnd_4878399 2504963511413163975177157 := by
  unfold tailWord_4878399
  simp only [CollatzResearch.WordTrace]
  refine ⟨177929829053401062062718251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118619886035600708041812167 177929829053401062062718251)
  ·
    refine ⟨266894743580101593094077377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177929829053401062062718251 266894743580101593094077377)
    ·
      refine ⟨200171057685076194820558033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266894743580101593094077377 200171057685076194820558033)
      ·
        refine ⟨150128293263807146115418525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200171057685076194820558033 150128293263807146115418525)
        ·
          refine ⟨56298109973927679793281947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150128293263807146115418525 56298109973927679793281947)
          ·
            refine ⟨84447164960891519689922921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56298109973927679793281947 84447164960891519689922921)
            ·
              refine ⟨63335373720668639767442191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84447164960891519689922921 63335373720668639767442191)
              ·
                refine ⟨95003060581002959651163287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63335373720668639767442191 95003060581002959651163287)
                ·
                  refine ⟨142504590871504439476744931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95003060581002959651163287 142504590871504439476744931)
                  ·
                    refine ⟨213756886307256659215117397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142504590871504439476744931 213756886307256659215117397)
                    ·
                      refine ⟨2504963511413163975177157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 213756886307256659215117397 2504963511413163975177157)
                      ·
                        rfl

theorem cell23_4878399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_4878399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878399 prefixEnd_4878399 := by exact prefixLift 4878399
  have htrace : WordTrace (prefixWord ++ tailWord_4878399) baseStart_4878399 baseEnd_4878399 := by
    simpa [prefixWord, tailWord_4878399, baseEnd_4878399] using wordTrace_append hprefix tailTrace_4878399
  have hstable : (prefixWord ++ tailWord_4878399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878399).length < 2 ^ (prefixWord ++ tailWord_4878399).sum := by decide
  have hdescent : baseEnd_4878399 < baseStart_4878399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878413 : List Nat := [1, 6, 1, 1, 1, 1, 3, 3, 6]
def baseStart_4878413 : Nat := 118140960795 + 4878413 * 2 ^ 59
def prefixEnd_4878413 : Nat := 4983230072969 + 3 ^ 40 * 4878413 * 2
def baseEnd_4878413 : Nat := 278330077793591880044677

theorem tailTrace_4878413 : CollatzResearch.WordTrace tailWord_4878413 prefixEnd_4878413 278330077793591880044677 := by
  unfold tailWord_4878413
  simp only [CollatzResearch.WordTrace]
  refine ⟨177930339675350342453727893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118620226450233561635818595 177930339675350342453727893)
  ·
    refine ⟨8340484672282047302518495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 177930339675350342453727893 8340484672282047302518495)
    ·
      refine ⟨12510727008423070953777743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8340484672282047302518495 12510727008423070953777743)
      ·
        refine ⟨18766090512634606430666615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12510727008423070953777743 18766090512634606430666615)
        ·
          refine ⟨28149135768951909645999923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18766090512634606430666615 28149135768951909645999923)
          ·
            refine ⟨42223703653427864468999885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28149135768951909645999923 42223703653427864468999885)
            ·
              refine ⟨15833888870035449175874957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42223703653427864468999885 15833888870035449175874957)
              ·
                refine ⟨5937708326263293440953109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15833888870035449175874957 5937708326263293440953109)
                ·
                  refine ⟨278330077793591880044677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5937708326263293440953109 278330077793591880044677)
                  ·
                    rfl

theorem cell23_4878413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_4878413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878413 prefixEnd_4878413 := by exact prefixLift 4878413
  have htrace : WordTrace (prefixWord ++ tailWord_4878413) baseStart_4878413 baseEnd_4878413 := by
    simpa [prefixWord, tailWord_4878413, baseEnd_4878413] using wordTrace_append hprefix tailTrace_4878413
  have hstable : (prefixWord ++ tailWord_4878413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878413).length < 2 ^ (prefixWord ++ tailWord_4878413).sum := by decide
  have hdescent : baseEnd_4878413 < baseStart_4878413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878419 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 5]
def baseStart_4878419 : Nat := 118140960795 + 4878419 * 2 ^ 59
def prefixEnd_4878419 : Nat := 4983230072969 + 3 ^ 40 * 4878419 * 2
def baseEnd_4878419 : Nat := 2504973781026253896927065

theorem tailTrace_4878419 : CollatzResearch.WordTrace tailWord_4878419 prefixEnd_4878419 2504973781026253896927065 := by
  unfold tailWord_4878419
  simp only [CollatzResearch.WordTrace]
  refine ⟨177930558513328605478446311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118620372342219070318964207 177930558513328605478446311)
  ·
    refine ⟨266895837769992908217669467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177930558513328605478446311 266895837769992908217669467)
    ·
      refine ⟨400343756654989362326504201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266895837769992908217669467 400343756654989362326504201)
      ·
        refine ⟨300257817491242021744878151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400343756654989362326504201 300257817491242021744878151)
        ·
          refine ⟨450386726236863032617317227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300257817491242021744878151 450386726236863032617317227)
          ·
            refine ⟨675580089355294548925975841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450386726236863032617317227 675580089355294548925975841)
            ·
              refine ⟨506685067016470911694481881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675580089355294548925975841 506685067016470911694481881)
              ·
                refine ⟨380013800262353183770861411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506685067016470911694481881 380013800262353183770861411)
                ·
                  refine ⟨570020700393529775656292117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 380013800262353183770861411 570020700393529775656292117)
                  ·
                    refine ⟨26719720330946708233888693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 570020700393529775656292117 26719720330946708233888693)
                    ·
                      refine ⟨2504973781026253896927065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26719720330946708233888693 2504973781026253896927065)
                      ·
                        rfl

theorem cell23_4878419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 6, 5].length) (baseStart_4878419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878419 prefixEnd_4878419 := by exact prefixLift 4878419
  have htrace : WordTrace (prefixWord ++ tailWord_4878419) baseStart_4878419 baseEnd_4878419 := by
    simpa [prefixWord, tailWord_4878419, baseEnd_4878419] using wordTrace_append hprefix tailTrace_4878419
  have hstable : (prefixWord ++ tailWord_4878419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878419).length < 2 ^ (prefixWord ++ tailWord_4878419).sum := by decide
  have hdescent : baseEnd_4878419 < baseStart_4878419 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878423 : List Nat := [1, 1, 3, 2, 2, 1, 2, 4, 3, 1, 3]
def baseStart_4878423 : Nat := 118140960795 + 4878423 * 2 ^ 59
def prefixEnd_4878423 : Nat := 4983230072969 + 3 ^ 40 * 4878423 * 2
def baseEnd_4878423 : Nat := 2504975834948871881277047

theorem tailTrace_4878423 : CollatzResearch.WordTrace tailWord_4878423 prefixEnd_4878423 2504975834948871881277047 := by
  unfold tailWord_4878423
  simp only [CollatzResearch.WordTrace]
  refine ⟨177930704405314114161591923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118620469603542742774394615 177930704405314114161591923)
  ·
    refine ⟨266896056607971171242387885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177930704405314114161591923 266896056607971171242387885)
    ·
      refine ⟨100086021227989189215895457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266896056607971171242387885 100086021227989189215895457)
      ·
        refine ⟨75064515920991891911921593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100086021227989189215895457 75064515920991891911921593)
        ·
          refine ⟨56298386940743918933941195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75064515920991891911921593 56298386940743918933941195)
          ·
            refine ⟨84447580411115878400911793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56298386940743918933941195 84447580411115878400911793)
            ·
              refine ⟨63335685308336908800683845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84447580411115878400911793 63335685308336908800683845)
              ·
                refine ⟨11875440995313170400128221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63335685308336908800683845 11875440995313170400128221)
                ·
                  refine ⟨4453290373242438900048083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11875440995313170400128221 4453290373242438900048083)
                  ·
                    refine ⟨6679935559863658350072125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4453290373242438900048083 6679935559863658350072125)
                    ·
                      refine ⟨2504975834948871881277047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6679935559863658350072125 2504975834948871881277047)
                      ·
                        rfl

theorem cell23_4878423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 2, 4, 3, 1, 3].length) (baseStart_4878423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878423 prefixEnd_4878423 := by exact prefixLift 4878423
  have htrace : WordTrace (prefixWord ++ tailWord_4878423) baseStart_4878423 baseEnd_4878423 := by
    simpa [prefixWord, tailWord_4878423, baseEnd_4878423] using wordTrace_append hprefix tailTrace_4878423
  have hstable : (prefixWord ++ tailWord_4878423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878423).length < 2 ^ (prefixWord ++ tailWord_4878423).sum := by decide
  have hdescent : baseEnd_4878423 < baseStart_4878423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878426 : List Nat := [3, 1, 1, 2, 1, 1, 5, 1, 3, 5]
def baseStart_4878426 : Nat := 118140960795 + 4878426 * 2 ^ 59
def prefixEnd_4878426 : Nat := 4983230072969 + 3 ^ 40 * 4878426 * 2
def baseEnd_4878426 : Nat := 834992458463611789846511

theorem tailTrace_4878426 : CollatzResearch.WordTrace tailWord_4878426 prefixEnd_4878426 834992458463611789846511 := by
  unfold tailWord_4878426
  simp only [CollatzResearch.WordTrace]
  refine ⟨44482703456075811418487783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118620542549535497115967421 44482703456075811418487783)
  ·
    refine ⟨66724055184113717127731675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44482703456075811418487783 66724055184113717127731675)
    ·
      refine ⟨100086082776170575691597513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66724055184113717127731675 100086082776170575691597513)
      ·
        refine ⟨75064562082127931768698135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100086082776170575691597513 75064562082127931768698135)
        ·
          refine ⟨112596843123191897653047203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75064562082127931768698135 112596843123191897653047203)
          ·
            refine ⟨168895264684787846479570805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112596843123191897653047203 168895264684787846479570805)
            ·
              refine ⟨15833931064198860607459763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 168895264684787846479570805 15833931064198860607459763)
              ·
                refine ⟨23750896596298290911189645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15833931064198860607459763 23750896596298290911189645)
                ·
                  refine ⟨8906586223611859091696117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23750896596298290911189645 8906586223611859091696117)
                  ·
                    refine ⟨834992458463611789846511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8906586223611859091696117 834992458463611789846511)
                    ·
                      rfl

theorem cell23_4878426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_4878426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878426 prefixEnd_4878426 := by exact prefixLift 4878426
  have htrace : WordTrace (prefixWord ++ tailWord_4878426) baseStart_4878426 baseEnd_4878426 := by
    simpa [prefixWord, tailWord_4878426, baseEnd_4878426] using wordTrace_append hprefix tailTrace_4878426
  have hstable : (prefixWord ++ tailWord_4878426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878426).length < 2 ^ (prefixWord ++ tailWord_4878426).sum := by decide
  have hdescent : baseEnd_4878426 < baseStart_4878426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878450 : List Nat := [3, 2, 1, 2, 2, 2, 2, 2, 2, 3, 2]
def baseStart_4878450 : Nat := 118140960795 + 4878450 * 2 ^ 59
def prefixEnd_4878450 : Nat := 4983230072969 + 3 ^ 40 * 4878450 * 2
def baseEnd_4878450 : Nat := 2504989698926543275639423

theorem tailTrace_4878450 : CollatzResearch.WordTrace tailWord_4878450 prefixEnd_4878450 2504989698926543275639423 := by
  unfold tailWord_4878450
  simp only [CollatzResearch.WordTrace]
  refine ⟨44482922294054074443206201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118621126117477531848549869 44482922294054074443206201)
  ·
    refine ⟨33362191720540555832404651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44482922294054074443206201 33362191720540555832404651)
    ·
      refine ⟨50043287580810833748606977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33362191720540555832404651 50043287580810833748606977)
      ·
        refine ⟨37532465685608125311455233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50043287580810833748606977 37532465685608125311455233)
        ·
          refine ⟨28149349264206093983591425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37532465685608125311455233 28149349264206093983591425)
          ·
            refine ⟨21112011948154570487693569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28149349264206093983591425 21112011948154570487693569)
            ·
              refine ⟨15834008961115927865770177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21112011948154570487693569 15834008961115927865770177)
              ·
                refine ⟨11875506720836945899327633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15834008961115927865770177 11875506720836945899327633)
                ·
                  refine ⟨8906630040627709424495725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11875506720836945899327633 8906630040627709424495725)
                  ·
                    refine ⟨3339986265235391034185897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8906630040627709424495725 3339986265235391034185897)
                    ·
                      refine ⟨2504989698926543275639423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3339986265235391034185897 2504989698926543275639423)
                      ·
                        rfl

theorem cell23_4878450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_4878450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878450 prefixEnd_4878450 := by exact prefixLift 4878450
  have htrace : WordTrace (prefixWord ++ tailWord_4878450) baseStart_4878450 baseEnd_4878450 := by
    simpa [prefixWord, tailWord_4878450, baseEnd_4878450] using wordTrace_append hprefix tailTrace_4878450
  have hstable : (prefixWord ++ tailWord_4878450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878450).length < 2 ^ (prefixWord ++ tailWord_4878450).sum := by decide
  have hdescent : baseEnd_4878450 < baseStart_4878450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878457 : List Nat := [1, 2, 1, 3, 4, 2, 1, 4, 1, 1, 3]
def baseStart_4878457 : Nat := 118140960795 + 4878457 * 2 ^ 59
def prefixEnd_4878457 : Nat := 4983230072969 + 3 ^ 40 * 4878457 * 2
def baseEnd_4878457 : Nat := 2504993293291124748251891

theorem tailTrace_4878457 : CollatzResearch.WordTrace tailWord_4878457 prefixEnd_4878457 2504993293291124748251891 := by
  unfold tailWord_4878457
  simp only [CollatzResearch.WordTrace]
  refine ⟨177931944487190937968329625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118621296324793958645553083 177931944487190937968329625)
  ·
    refine ⟨133448958365393203476247219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177931944487190937968329625 133448958365393203476247219)
    ·
      refine ⟨200173437548089805214370829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133448958365393203476247219 200173437548089805214370829)
      ·
        refine ⟨75065039080533676955389061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200173437548089805214370829 75065039080533676955389061)
        ·
          refine ⟨14074694827600064429135449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75065039080533676955389061 14074694827600064429135449)
          ·
            refine ⟨10556021120700048321851587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14074694827600064429135449 10556021120700048321851587)
            ·
              refine ⟨15834031681050072482777381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10556021120700048321851587 15834031681050072482777381)
              ·
                refine ⟨2968880940196888590520759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15834031681050072482777381 2968880940196888590520759)
                ·
                  refine ⟨4453321410295332885781139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2968880940196888590520759 4453321410295332885781139)
                  ·
                    refine ⟨6679982115442999328671709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4453321410295332885781139 6679982115442999328671709)
                    ·
                      refine ⟨2504993293291124748251891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6679982115442999328671709 2504993293291124748251891)
                      ·
                        rfl

theorem cell23_4878457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 4, 1, 1, 3].length) (baseStart_4878457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878457 prefixEnd_4878457 := by exact prefixLift 4878457
  have htrace : WordTrace (prefixWord ++ tailWord_4878457) baseStart_4878457 baseEnd_4878457 := by
    simpa [prefixWord, tailWord_4878457, baseEnd_4878457] using wordTrace_append hprefix tailTrace_4878457
  have hstable : (prefixWord ++ tailWord_4878457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878457).length < 2 ^ (prefixWord ++ tailWord_4878457).sum := by decide
  have hdescent : baseEnd_4878457 < baseStart_4878457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878473 : List Nat := [1, 2, 1, 1, 4, 2, 1, 5, 2, 4]
def baseStart_4878473 : Nat := 118140960795 + 4878473 * 2 ^ 59
def prefixEnd_4878473 : Nat := 4983230072969 + 3 ^ 40 * 4878473 * 2
def baseEnd_4878473 : Nat := 835000502993865561883939

theorem tailTrace_4878473 : CollatzResearch.WordTrace tailWord_4878473 prefixEnd_4878473 835000502993865561883939 := by
  unfold tailWord_4878473
  simp only [CollatzResearch.WordTrace]
  refine ⟨177932528055132972700912073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118621685370088648467274715 177932528055132972700912073)
  ·
    refine ⟨133449396041349729525684055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177932528055132972700912073 133449396041349729525684055)
    ·
      refine ⟨200174094062024594288526083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133449396041349729525684055 200174094062024594288526083)
      ·
        refine ⟨300261141093036891432789125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200174094062024594288526083 300261141093036891432789125)
        ·
          refine ⟨56298963954944417143647961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 300261141093036891432789125 56298963954944417143647961)
          ·
            refine ⟨42224222966208312857735971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56298963954944417143647961 42224222966208312857735971)
            ·
              refine ⟨63336334449312469286603957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42224222966208312857735971 63336334449312469286603957)
              ·
                refine ⟨5937781354623043995619121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63336334449312469286603957 5937781354623043995619121)
                ·
                  refine ⟨4453336015967282996714341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5937781354623043995619121 4453336015967282996714341)
                  ·
                    refine ⟨835000502993865561883939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4453336015967282996714341 835000502993865561883939)
                    ·
                      rfl

theorem cell23_4878473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 5, 2, 4].length) (baseStart_4878473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878473 prefixEnd_4878473 := by exact prefixLift 4878473
  have htrace : WordTrace (prefixWord ++ tailWord_4878473) baseStart_4878473 baseEnd_4878473 := by
    simpa [prefixWord, tailWord_4878473, baseEnd_4878473] using wordTrace_append hprefix tailTrace_4878473
  have hstable : (prefixWord ++ tailWord_4878473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878473).length < 2 ^ (prefixWord ++ tailWord_4878473).sum := by decide
  have hdescent : baseEnd_4878473 < baseStart_4878473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878480 : List Nat := [2, 1, 1, 1, 1, 1, 7, 2, 3, 2, 2]
def baseStart_4878480 : Nat := 118140960795 + 4878480 * 2 ^ 59
def prefixEnd_4878480 : Nat := 4983230072969 + 3 ^ 40 * 4878480 * 2
def baseEnd_4878480 : Nat := 2505005103346178158264285

theorem tailTrace_4878480 : CollatzResearch.WordTrace tailWord_4878480 prefixEnd_4878480 2505005103346178158264285 := by
  unfold tailWord_4878480
  simp only [CollatzResearch.WordTrace]
  refine ⟨88966391683053806448208447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118621855577405075264277929 88966391683053806448208447)
  ·
    refine ⟨133449587524580709672312671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88966391683053806448208447 133449587524580709672312671)
    ·
      refine ⟨200174381286871064508469007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133449587524580709672312671 200174381286871064508469007)
      ·
        refine ⟨300261571930306596762703511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200174381286871064508469007 300261571930306596762703511)
        ·
          refine ⟨450392357895459895144055267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300261571930306596762703511 450392357895459895144055267)
          ·
            refine ⟨675588536843189842716082901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450392357895459895144055267 675588536843189842716082901)
            ·
              refine ⟨15834106332262261938658193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 675588536843189842716082901 15834106332262261938658193)
              ·
                refine ⟨11875579749196696453993645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15834106332262261938658193 11875579749196696453993645)
                ·
                  refine ⟨4453342405948761170247617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11875579749196696453993645 4453342405948761170247617)
                  ·
                    refine ⟨3340006804461570877685713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4453342405948761170247617 3340006804461570877685713)
                    ·
                      refine ⟨2505005103346178158264285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340006804461570877685713 2505005103346178158264285)
                      ·
                        rfl

theorem cell23_4878480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 7, 2, 3, 2, 2].length) (baseStart_4878480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878480 prefixEnd_4878480 := by exact prefixLift 4878480
  have htrace : WordTrace (prefixWord ++ tailWord_4878480) baseStart_4878480 baseEnd_4878480 := by
    simpa [prefixWord, tailWord_4878480, baseEnd_4878480] using wordTrace_append hprefix tailTrace_4878480
  have hstable : (prefixWord ++ tailWord_4878480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878480).length < 2 ^ (prefixWord ++ tailWord_4878480).sum := by decide
  have hdescent : baseEnd_4878480 < baseStart_4878480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878483 : List Nat := [1, 1, 1, 2, 1, 2, 3, 6, 1, 2, 3]
def baseStart_4878483 : Nat := 118140960795 + 4878483 * 2 ^ 59
def prefixEnd_4878483 : Nat := 4983230072969 + 3 ^ 40 * 4878483 * 2
def baseEnd_4878483 : Nat := 2505006643788141646526771

theorem tailTrace_4878483 : CollatzResearch.WordTrace tailWord_4878483 prefixEnd_4878483 2505006643788141646526771 := by
  unfold tailWord_4878483
  simp only [CollatzResearch.WordTrace]
  refine ⟨177932892785096744408776103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118621928523397829605850735 177932892785096744408776103)
  ·
    refine ⟨266899339177645116613164155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177932892785096744408776103 266899339177645116613164155)
    ·
      refine ⟨400349008766467674919746233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266899339177645116613164155 400349008766467674919746233)
      ·
        refine ⟨300261756574850756189809675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400349008766467674919746233 300261756574850756189809675)
        ·
          refine ⟨450392634862276134284714513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300261756574850756189809675 450392634862276134284714513)
          ·
            refine ⟨337794476146707100713535885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450392634862276134284714513 337794476146707100713535885)
            ·
              refine ⟨126672928555015162767575957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337794476146707100713535885 126672928555015162767575957)
              ·
                refine ⟨5937793526016335754730123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 126672928555015162767575957 5937793526016335754730123)
                ·
                  refine ⟨8906690289024503632095185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5937793526016335754730123 8906690289024503632095185)
                  ·
                    refine ⟨6680017716768377724071389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8906690289024503632095185 6680017716768377724071389)
                    ·
                      refine ⟨2505006643788141646526771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6680017716768377724071389 2505006643788141646526771)
                      ·
                        rfl

theorem cell23_4878483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 6, 1, 2, 3].length) (baseStart_4878483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878483 prefixEnd_4878483 := by exact prefixLift 4878483
  have htrace : WordTrace (prefixWord ++ tailWord_4878483) baseStart_4878483 baseEnd_4878483 := by
    simpa [prefixWord, tailWord_4878483, baseEnd_4878483] using wordTrace_append hprefix tailTrace_4878483
  have hstable : (prefixWord ++ tailWord_4878483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878483).length < 2 ^ (prefixWord ++ tailWord_4878483).sum := by decide
  have hdescent : baseEnd_4878483 < baseStart_4878483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878493 : List Nat := [1, 4, 2, 1, 1, 3, 2, 2, 1, 2, 4]
def baseStart_4878493 : Nat := 118140960795 + 4878493 * 2 ^ 59
def prefixEnd_4878493 : Nat := 4983230072969 + 3 ^ 40 * 4878493 * 2
def baseEnd_4878493 : Nat := 2505011778594686607401725

theorem tailTrace_4878493 : CollatzResearch.WordTrace tailWord_4878493 prefixEnd_4878493 2505011778594686607401725 := by
  unfold tailWord_4878493
  simp only [CollatzResearch.WordTrace]
  refine ⟨177933257515060516116640133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118622171676707010744426755 177933257515060516116640133)
  ·
    refine ⟨33362485784073846771870025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177933257515060516116640133 33362485784073846771870025)
    ·
      refine ⟨25021864338055385078902519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33362485784073846771870025 25021864338055385078902519)
      ·
        refine ⟨37532796507083077618353779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25021864338055385078902519 37532796507083077618353779)
        ·
          refine ⟨56299194760624616427530669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37532796507083077618353779 56299194760624616427530669)
          ·
            refine ⟨21112198035234231160324001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56299194760624616427530669 21112198035234231160324001)
            ·
              refine ⟨15834148526425673370243001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21112198035234231160324001 15834148526425673370243001)
              ·
                refine ⟨11875611394819255027682251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15834148526425673370243001 11875611394819255027682251)
                ·
                  refine ⟨17813417092228882541523377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11875611394819255027682251 17813417092228882541523377)
                  ·
                    refine ⟨13360062819171661906142533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17813417092228882541523377 13360062819171661906142533)
                    ·
                      refine ⟨2505011778594686607401725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13360062819171661906142533 2505011778594686607401725)
                      ·
                        rfl

theorem cell23_4878493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 2, 1, 2, 4].length) (baseStart_4878493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878493 prefixEnd_4878493 := by exact prefixLift 4878493
  have htrace : WordTrace (prefixWord ++ tailWord_4878493) baseStart_4878493 baseEnd_4878493 := by
    simpa [prefixWord, tailWord_4878493, baseEnd_4878493] using wordTrace_append hprefix tailTrace_4878493
  have hstable : (prefixWord ++ tailWord_4878493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878493).length < 2 ^ (prefixWord ++ tailWord_4878493).sum := by decide
  have hdescent : baseEnd_4878493 < baseStart_4878493 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878494 : List Nat := [4, 3, 1, 1, 3, 2, 2, 1, 1, 5]
def baseStart_4878494 : Nat := 118140960795 + 4878494 * 2 ^ 59
def prefixEnd_4878494 : Nat := 4983230072969 + 3 ^ 40 * 4878494 * 2
def baseEnd_4878494 : Nat := 835004097358447034496407

theorem tailTrace_4878494 : CollatzResearch.WordTrace tailWord_4878494 prefixEnd_4878494 835004097358447034496407 := by
  unfold tailWord_4878494
  simp only [CollatzResearch.WordTrace]
  refine ⟨22241661748507111660928317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118622195992037928858284357 22241661748507111660928317)
  ·
    refine ⟨8340623155690166872848119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22241661748507111660928317 8340623155690166872848119)
    ·
      refine ⟨12510934733535250309272179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8340623155690166872848119 12510934733535250309272179)
      ·
        refine ⟨18766402100302875463908269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12510934733535250309272179 18766402100302875463908269)
        ·
          refine ⟨7037400787613578298965601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18766402100302875463908269 7037400787613578298965601)
          ·
            refine ⟨5278050590710183724224201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7037400787613578298965601 5278050590710183724224201)
            ·
              refine ⟨3958537943032637793168151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5278050590710183724224201 3958537943032637793168151)
              ·
                refine ⟨5937806914548956689752227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3958537943032637793168151 5937806914548956689752227)
                ·
                  refine ⟨8906710371823435034628341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5937806914548956689752227 8906710371823435034628341)
                  ·
                    refine ⟨835004097358447034496407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8906710371823435034628341 835004097358447034496407)
                    ·
                      rfl

theorem cell23_4878494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_4878494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878494 prefixEnd_4878494 := by exact prefixLift 4878494
  have htrace : WordTrace (prefixWord ++ tailWord_4878494) baseStart_4878494 baseEnd_4878494 := by
    simpa [prefixWord, tailWord_4878494, baseEnd_4878494] using wordTrace_append hprefix tailTrace_4878494
  have hstable : (prefixWord ++ tailWord_4878494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878494).length < 2 ^ (prefixWord ++ tailWord_4878494).sum := by decide
  have hdescent : baseEnd_4878494 < baseStart_4878494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878497 : List Nat := [1, 2, 3, 3, 1, 4, 2, 1, 1, 1, 4]
def baseStart_4878497 : Nat := 118140960795 + 4878497 * 2 ^ 59
def prefixEnd_4878497 : Nat := 4983230072969 + 3 ^ 40 * 4878497 * 2
def baseEnd_4878497 : Nat := 2505013832517304591751707

theorem tailTrace_4878497 : CollatzResearch.WordTrace tailWord_4878497 prefixEnd_4878497 2505013832517304591751707 := by
  unfold tailWord_4878497
  simp only [CollatzResearch.WordTrace]
  refine ⟨177933403407046024799785745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118622268938030683199857163 177933403407046024799785745)
  ·
    refine ⟨133450052555284518599839309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177933403407046024799785745 133450052555284518599839309)
    ·
      refine ⟨50043769708231694474939741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133450052555284518599839309 50043769708231694474939741)
      ·
        refine ⟨18766413640586885428102403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50043769708231694474939741 18766413640586885428102403)
        ·
          refine ⟨28149620460880328142153605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18766413640586885428102403 28149620460880328142153605)
          ·
            refine ⟨5278053836415061526653801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28149620460880328142153605 5278053836415061526653801)
            ·
              refine ⟨3958540377311296144990351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5278053836415061526653801 3958540377311296144990351)
              ·
                refine ⟨5937810565966944217485527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3958540377311296144990351 5937810565966944217485527)
                ·
                  refine ⟨8906715848950416326228291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5937810565966944217485527 8906715848950416326228291)
                  ·
                    refine ⟨13360073773425624489342437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8906715848950416326228291 13360073773425624489342437)
                    ·
                      refine ⟨2505013832517304591751707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13360073773425624489342437 2505013832517304591751707)
                      ·
                        rfl

theorem cell23_4878497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_4878497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878497 prefixEnd_4878497 := by exact prefixLift 4878497
  have htrace : WordTrace (prefixWord ++ tailWord_4878497) baseStart_4878497 baseEnd_4878497 := by
    simpa [prefixWord, tailWord_4878497, baseEnd_4878497] using wordTrace_append hprefix tailTrace_4878497
  have hstable : (prefixWord ++ tailWord_4878497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878497).length < 2 ^ (prefixWord ++ tailWord_4878497).sum := by decide
  have hdescent : baseEnd_4878497 < baseStart_4878497 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878503 : List Nat := [1, 1, 6, 2, 2, 1, 10]
def baseStart_4878503 : Nat := 118140960795 + 4878503 * 2 ^ 59
def prefixEnd_4878503 : Nat := 4983230072969 + 3 ^ 40 * 4878503 * 2
def baseEnd_4878503 : Nat := 30926134733348537879959

theorem tailTrace_4878503 : CollatzResearch.WordTrace tailWord_4878503 prefixEnd_4878503 30926134733348537879959 := by
  unfold tailWord_4878503
  simp only [CollatzResearch.WordTrace]
  refine ⟨177933622245024287824504163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118622414830016191883002775 177933622245024287824504163)
  ·
    refine ⟨266900433367536431736756245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177933622245024287824504163 266900433367536431736756245)
    ·
      refine ⟨12510957814103270237660449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 266900433367536431736756245 12510957814103270237660449)
      ·
        refine ⟨9383218360577452678245337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12510957814103270237660449 9383218360577452678245337)
        ·
          refine ⟨7037413770433089508684003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9383218360577452678245337 7037413770433089508684003)
          ·
            refine ⟨10556120655649634263026005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7037413770433089508684003 10556120655649634263026005)
            ·
              refine ⟨30926134733348537879959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 10556120655649634263026005 30926134733348537879959)
              ·
                rfl

theorem cell23_4878503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 10].length) (baseStart_4878503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878503 prefixEnd_4878503 := by exact prefixLift 4878503
  have htrace : WordTrace (prefixWord ++ tailWord_4878503) baseStart_4878503 baseEnd_4878503 := by
    simpa [prefixWord, tailWord_4878503, baseEnd_4878503] using wordTrace_append hprefix tailTrace_4878503
  have hstable : (prefixWord ++ tailWord_4878503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878503).length < 2 ^ (prefixWord ++ tailWord_4878503).sum := by decide
  have hdescent : baseEnd_4878503 < baseStart_4878503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878621 : List Nat := [1, 4, 2, 3, 2, 1, 2, 2, 2, 2, 2]
def baseStart_4878621 : Nat := 118140960795 + 4878621 * 2 ^ 59
def prefixEnd_4878621 : Nat := 4983230072969 + 3 ^ 40 * 4878621 * 2
def baseEnd_4878621 : Nat := 2505077504118462106601137

theorem tailTrace_4878621 : CollatzResearch.WordTrace tailWord_4878621 prefixEnd_4878621 2505077504118462106601137 := by
  unfold tailWord_4878621
  simp only [CollatzResearch.WordTrace]
  refine ⟨177937926058596793977299717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118625284039064529318199811 177937926058596793977299717)
  ·
    refine ⟨33363361135986898870743697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177937926058596793977299717 33363361135986898870743697)
    ·
      refine ⟨25022520851990174153057773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33363361135986898870743697 25022520851990174153057773)
      ·
        refine ⟨9383445319496315307396665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25022520851990174153057773 9383445319496315307396665)
        ·
          refine ⟨7037583989622236480547499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9383445319496315307396665 7037583989622236480547499)
          ·
            refine ⟨10556375984433354720821249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7037583989622236480547499 10556375984433354720821249)
            ·
              refine ⟨7917281988325016040615937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10556375984433354720821249 7917281988325016040615937)
              ·
                refine ⟨5937961491243762030461953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7917281988325016040615937 5937961491243762030461953)
                ·
                  refine ⟨4453471118432821522846465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5937961491243762030461953 4453471118432821522846465)
                  ·
                    refine ⟨3340103338824616142134849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4453471118432821522846465 3340103338824616142134849)
                    ·
                      refine ⟨2505077504118462106601137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340103338824616142134849 2505077504118462106601137)
                      ·
                        rfl

theorem cell23_4878621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_4878621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878621 prefixEnd_4878621 := by exact prefixLift 4878621
  have htrace : WordTrace (prefixWord ++ tailWord_4878621) baseStart_4878621 baseEnd_4878621 := by
    simpa [prefixWord, tailWord_4878621, baseEnd_4878621] using wordTrace_append hprefix tailTrace_4878621
  have hstable : (prefixWord ++ tailWord_4878621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878621).length < 2 ^ (prefixWord ++ tailWord_4878621).sum := by decide
  have hdescent : baseEnd_4878621 < baseStart_4878621 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878643 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 4]
def baseStart_4878643 : Nat := 118140960795 + 4878643 * 2 ^ 59
def prefixEnd_4878643 : Nat := 4983230072969 + 3 ^ 40 * 4878643 * 2
def baseEnd_4878643 : Nat := 2505088800692861020526035

theorem tailTrace_4878643 : CollatzResearch.WordTrace tailWord_4878643 prefixEnd_4878643 2505088800692861020526035 := by
  unfold tailWord_4878643
  simp only [CollatzResearch.WordTrace]
  refine ⟨177938728464517091734600583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118625818976344727823067055 177938728464517091734600583)
  ·
    refine ⟨266908092696775637601900875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177938728464517091734600583 266908092696775637601900875)
    ·
      refine ⟨400362139045163456402851313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266908092696775637601900875 400362139045163456402851313)
      ·
        refine ⟨300271604283872592302138485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400362139045163456402851313 300271604283872592302138485)
        ·
          refine ⟨28150462901613055528325483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 300271604283872592302138485 28150462901613055528325483)
          ·
            refine ⟨42225694352419583292488225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28150462901613055528325483 42225694352419583292488225)
            ·
              refine ⟨31669270764314687469366169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42225694352419583292488225 31669270764314687469366169)
              ·
                refine ⟨23751953073236015602024627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31669270764314687469366169 23751953073236015602024627)
                ·
                  refine ⟨35627929609854023403036941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23751953073236015602024627 35627929609854023403036941)
                  ·
                    refine ⟨13360473603695258776138853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35627929609854023403036941 13360473603695258776138853)
                    ·
                      refine ⟨2505088800692861020526035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13360473603695258776138853 2505088800692861020526035)
                      ·
                        rfl

theorem cell23_4878643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 3, 4].length) (baseStart_4878643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878643 prefixEnd_4878643 := by exact prefixLift 4878643
  have htrace : WordTrace (prefixWord ++ tailWord_4878643) baseStart_4878643 baseEnd_4878643 := by
    simpa [prefixWord, tailWord_4878643, baseEnd_4878643] using wordTrace_append hprefix tailTrace_4878643
  have hstable : (prefixWord ++ tailWord_4878643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878643).length < 2 ^ (prefixWord ++ tailWord_4878643).sum := by decide
  have hdescent : baseEnd_4878643 < baseStart_4878643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878673 : List Nat := [1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 6]
def baseStart_4878673 : Nat := 118140960795 + 4878673 * 2 ^ 59
def prefixEnd_4878673 : Nat := 4983230072969 + 3 ^ 40 * 4878673 * 2
def baseEnd_4878673 : Nat := 2505104205112495903150897

theorem tailTrace_4878673 : CollatzResearch.WordTrace tailWord_4878673 prefixEnd_4878673 2505104205112495903150897 := by
  unfold tailWord_4878673
  simp only [CollatzResearch.WordTrace]
  refine ⟨177939822654408406858192673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118626548436272271238795115 177939822654408406858192673)
  ·
    refine ⟨133454866990806305143644505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177939822654408406858192673 133454866990806305143644505)
    ·
      refine ⟨100091150243104728857733379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133454866990806305143644505 100091150243104728857733379)
      ·
        refine ⟨150136725364657093286600069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100091150243104728857733379 150136725364657093286600069)
        ·
          refine ⟨28150636005873204991237513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150136725364657093286600069 28150636005873204991237513)
          ·
            refine ⟨21112977004404903743428135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28150636005873204991237513 21112977004404903743428135)
            ·
              refine ⟨31669465506607355615142203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21112977004404903743428135 31669465506607355615142203)
              ·
                refine ⟨47504198259911033422713305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31669465506607355615142203 47504198259911033422713305)
                ·
                  refine ⟨35628148694933275067034979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47504198259911033422713305 35628148694933275067034979)
                  ·
                    refine ⟨53442223042399912600552469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35628148694933275067034979 53442223042399912600552469)
                    ·
                      refine ⟨2505104205112495903150897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53442223042399912600552469 2505104205112495903150897)
                      ·
                        rfl

theorem cell23_4878673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_4878673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878673 prefixEnd_4878673 := by exact prefixLift 4878673
  have htrace : WordTrace (prefixWord ++ tailWord_4878673) baseStart_4878673 baseEnd_4878673 := by
    simpa [prefixWord, tailWord_4878673, baseEnd_4878673] using wordTrace_append hprefix tailTrace_4878673
  have hstable : (prefixWord ++ tailWord_4878673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878673).length < 2 ^ (prefixWord ++ tailWord_4878673).sum := by decide
  have hdescent : baseEnd_4878673 < baseStart_4878673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878687 : List Nat := [1, 1, 2, 3, 1, 2, 4, 4, 1, 4]
def baseStart_4878687 : Nat := 118140960795 + 4878687 * 2 ^ 59
def prefixEnd_4878687 : Nat := 4983230072969 + 3 ^ 40 * 4878687 * 2
def baseEnd_4878687 : Nat := 835037131280552949458611

theorem tailTrace_4878687 : CollatzResearch.WordTrace tailWord_4878687 prefixEnd_4878687 835037131280552949458611 := by
  unfold tailWord_4878687
  simp only [CollatzResearch.WordTrace]
  refine ⟨177940333276357687249202315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118626888850905124832801543 177940333276357687249202315)
  ·
    refine ⟨266910499914536530873803473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177940333276357687249202315 266910499914536530873803473)
    ·
      refine ⟨200182874935902398155352605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266910499914536530873803473 200182874935902398155352605)
      ·
        refine ⟨75068578100963399308257227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200182874935902398155352605 75068578100963399308257227)
        ·
          refine ⟨112602867151445098962385841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75068578100963399308257227 112602867151445098962385841)
          ·
            refine ⟨84452150363583824221789381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112602867151445098962385841 84452150363583824221789381)
            ·
              refine ⟨15834778193171967041585509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84452150363583824221789381 15834778193171967041585509)
              ·
                refine ⟨2969020911219743820297283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15834778193171967041585509 2969020911219743820297283)
                ·
                  refine ⟨4453531366829615730445925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969020911219743820297283 4453531366829615730445925)
                  ·
                    refine ⟨835037131280552949458611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4453531366829615730445925 835037131280552949458611)
                    ·
                      rfl

theorem cell23_4878687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 4, 1, 4].length) (baseStart_4878687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878687 prefixEnd_4878687 := by exact prefixLift 4878687
  have htrace : WordTrace (prefixWord ++ tailWord_4878687) baseStart_4878687 baseEnd_4878687 := by
    simpa [prefixWord, tailWord_4878687, baseEnd_4878687] using wordTrace_append hprefix tailTrace_4878687
  have hstable : (prefixWord ++ tailWord_4878687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878687).length < 2 ^ (prefixWord ++ tailWord_4878687).sum := by decide
  have hdescent : baseEnd_4878687 < baseStart_4878687 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878721 : List Nat := [1, 2, 4, 3, 1, 3, 1, 3, 1, 4]
def baseStart_4878721 : Nat := 118140960795 + 4878721 * 2 ^ 59
def prefixEnd_4878721 : Nat := 4983230072969 + 3 ^ 40 * 4878721 * 2
def baseEnd_4878721 : Nat := 835042950727970571783559

theorem tailTrace_4878721 : CollatzResearch.WordTrace tailWord_4878721 prefixEnd_4878721 835042950727970571783559 := by
  unfold tailWord_4878721
  simp only [CollatzResearch.WordTrace]
  refine ⟨177941573358234511055940017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118627715572156340703960011 177941573358234511055940017)
  ·
    refine ⟨133456180018675883291955013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177941573358234511055940017 133456180018675883291955013)
    ·
      refine ⟨25023033753501728117241565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133456180018675883291955013 25023033753501728117241565)
      ·
        refine ⟨9383637657563148043965587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25023033753501728117241565 9383637657563148043965587)
        ·
          refine ⟨14075456486344722065948381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9383637657563148043965587 14075456486344722065948381)
          ·
            refine ⟨5278296182379270774730643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14075456486344722065948381 5278296182379270774730643)
            ·
              refine ⟨7917444273568906162095965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5278296182379270774730643 7917444273568906162095965)
              ·
                refine ⟨2969041602588339810785987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7917444273568906162095965 2969041602588339810785987)
                ·
                  refine ⟨4453562403882509716178981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969041602588339810785987 4453562403882509716178981)
                  ·
                    refine ⟨835042950727970571783559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4453562403882509716178981 835042950727970571783559)
                    ·
                      rfl

theorem cell23_4878721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_4878721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878721 prefixEnd_4878721 := by exact prefixLift 4878721
  have htrace : WordTrace (prefixWord ++ tailWord_4878721) baseStart_4878721 baseEnd_4878721 := by
    simpa [prefixWord, tailWord_4878721, baseEnd_4878721] using wordTrace_append hprefix tailTrace_4878721
  have hstable : (prefixWord ++ tailWord_4878721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878721).length < 2 ^ (prefixWord ++ tailWord_4878721).sum := by decide
  have hdescent : baseEnd_4878721 < baseStart_4878721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878744 : List Nat := [2, 1, 2, 5, 1, 1, 3, 1, 3, 1, 3]
def baseStart_4878744 : Nat := 118140960795 + 4878744 * 2 ^ 59
def prefixEnd_4878744 : Nat := 4983230072969 + 3 ^ 40 * 4878744 * 2
def baseEnd_4878744 : Nat := 2505140662238965125363071

theorem tailTrace_4878744 : CollatzResearch.WordTrace tailWord_4878744 prefixEnd_4878744 2505140662238965125363071 := by
  unfold tailWord_4878744
  simp only [CollatzResearch.WordTrace]
  refine ⟨88971206118575592992013643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118628274824767457322684857 88971206118575592992013643)
  ·
    refine ⟨133456809177863389488020465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88971206118575592992013643 133456809177863389488020465)
    ·
      refine ⟨100092606883397542116015349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133456809177863389488020465 100092606883397542116015349)
      ·
        refine ⟨9383681895318519573376439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 100092606883397542116015349 9383681895318519573376439)
        ·
          refine ⟨14075522842977779360064659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9383681895318519573376439 14075522842977779360064659)
          ·
            refine ⟨21113284264466669040096989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14075522842977779360064659 21113284264466669040096989)
            ·
              refine ⟨7917481599175000890036371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21113284264466669040096989 7917481599175000890036371)
              ·
                refine ⟨11876222398762501335054557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7917481599175000890036371 11876222398762501335054557)
                ·
                  refine ⟨4453583399535938000645459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11876222398762501335054557 4453583399535938000645459)
                  ·
                    refine ⟨6680375099303907000968189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4453583399535938000645459 6680375099303907000968189)
                    ·
                      refine ⟨2505140662238965125363071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6680375099303907000968189 2505140662238965125363071)
                      ·
                        rfl

theorem cell23_4878744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_4878744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878744 prefixEnd_4878744 := by exact prefixLift 4878744
  have htrace : WordTrace (prefixWord ++ tailWord_4878744) baseStart_4878744 baseEnd_4878744 := by
    simpa [prefixWord, tailWord_4878744, baseEnd_4878744] using wordTrace_append hprefix tailTrace_4878744
  have hstable : (prefixWord ++ tailWord_4878744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878744).length < 2 ^ (prefixWord ++ tailWord_4878744).sum := by decide
  have hdescent : baseEnd_4878744 < baseStart_4878744 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878763 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 4]
def baseStart_4878763 : Nat := 118140960795 + 4878763 * 2 ^ 59
def prefixEnd_4878763 : Nat := 4983230072969 + 3 ^ 40 * 4878763 * 2
def baseEnd_4878763 : Nat := 2505150418371400551025483

theorem tailTrace_4878763 : CollatzResearch.WordTrace tailWord_4878763 prefixEnd_4878763 2505150418371400551025483 := by
  unfold tailWord_4878763
  simp only [CollatzResearch.WordTrace]
  refine ⟨177943105224082352228968943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118628736816054901485979295 177943105224082352228968943)
  ·
    refine ⟨266914657836123528343453415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177943105224082352228968943 266914657836123528343453415)
    ·
      refine ⟨400371986754185292515180123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266914657836123528343453415 400371986754185292515180123)
      ·
        refine ⟨600557980131277938772770185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400371986754185292515180123 600557980131277938772770185)
        ·
          refine ⟨450418485098458454079577639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600557980131277938772770185 450418485098458454079577639)
          ·
            refine ⟨675627727647687681119366459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450418485098458454079577639 675627727647687681119366459)
            ·
              refine ⟨1013441591471531521679049689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 675627727647687681119366459 1013441591471531521679049689)
              ·
                refine ⟨760081193603648641259287267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013441591471531521679049689 760081193603648641259287267)
                ·
                  refine ⟨1140121790405472961888930901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760081193603648641259287267 1140121790405472961888930901)
                  ·
                    refine ⟨13360802231314136272135909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 1140121790405472961888930901 13360802231314136272135909)
                    ·
                      refine ⟨2505150418371400551025483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13360802231314136272135909 2505150418371400551025483)
                      ·
                        rfl

theorem cell23_4878763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 8, 4].length) (baseStart_4878763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878763 prefixEnd_4878763 := by exact prefixLift 4878763
  have htrace : WordTrace (prefixWord ++ tailWord_4878763) baseStart_4878763 baseEnd_4878763 := by
    simpa [prefixWord, tailWord_4878763, baseEnd_4878763] using wordTrace_append hprefix tailTrace_4878763
  have hstable : (prefixWord ++ tailWord_4878763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878763).length < 2 ^ (prefixWord ++ tailWord_4878763).sum := by decide
  have hdescent : baseEnd_4878763 < baseStart_4878763 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878790 : List Nat := [6, 1, 16]
def baseStart_4878790 : Nat := 118140960795 + 4878790 * 2 ^ 59
def prefixEnd_4878790 : Nat := 4983230072969 + 3 ^ 40 * 4878790 * 2
def baseEnd_4878790 : Nat := 381826593865122991219

theorem tailTrace_4878790 : CollatzResearch.WordTrace tailWord_4878790 prefixEnd_4878790 381826593865122991219 := by
  unfold tailWord_4878790
  simp only [CollatzResearch.WordTrace]
  refine ⟨5560752812343266745006307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 118629393329989690560134549 5560752812343266745006307)
  ·
    refine ⟨8341129218514900117509461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5560752812343266745006307 8341129218514900117509461)
    ·
      refine ⟨381826593865122991219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 8341129218514900117509461 381826593865122991219)
      ·
        rfl

theorem cell23_4878790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 16].length) (baseStart_4878790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878790 prefixEnd_4878790 := by exact prefixLift 4878790
  have htrace : WordTrace (prefixWord ++ tailWord_4878790) baseStart_4878790 baseEnd_4878790 := by
    simpa [prefixWord, tailWord_4878790, baseEnd_4878790] using wordTrace_append hprefix tailTrace_4878790
  have hstable : (prefixWord ++ tailWord_4878790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878790).length < 2 ^ (prefixWord ++ tailWord_4878790).sum := by decide
  have hdescent : baseEnd_4878790 < baseStart_4878790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878817 : List Nat := [1, 2, 3, 1, 2, 2, 4, 1, 1, 3, 3]
def baseStart_4878817 : Nat := 118140960795 + 4878817 * 2 ^ 59
def prefixEnd_4878817 : Nat := 4983230072969 + 3 ^ 40 * 4878817 * 2
def baseEnd_4878817 : Nat := 2505178146326743339750235

theorem tailTrace_4878817 : CollatzResearch.WordTrace tailWord_4878817 prefixEnd_4878817 2505178146326743339750235 := by
  unfold tailWord_4878817
  simp only [CollatzResearch.WordTrace]
  refine ⟨177945074765886719451434705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118630049843924479634289803 177945074765886719451434705)
  ·
    refine ⟨133458806074415039588576029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177945074765886719451434705 133458806074415039588576029)
    ·
      refine ⟨50047052277905639845716011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133458806074415039588576029 50047052277905639845716011)
      ·
        refine ⟨75070578416858459768574017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50047052277905639845716011 75070578416858459768574017)
        ·
          refine ⟨56302933812643844826430513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75070578416858459768574017 56302933812643844826430513)
          ·
            refine ⟨42227200359482883619822885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56302933812643844826430513 42227200359482883619822885)
            ·
              refine ⟨7917600067403040678716791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42227200359482883619822885 7917600067403040678716791)
              ·
                refine ⟨11876400101104561018075187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7917600067403040678716791 11876400101104561018075187)
                ·
                  refine ⟨17814600151656841527112781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11876400101104561018075187 17814600151656841527112781)
                  ·
                    refine ⟨6680475056871315572667293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17814600151656841527112781 6680475056871315572667293)
                    ·
                      refine ⟨2505178146326743339750235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6680475056871315572667293 2505178146326743339750235)
                      ·
                        rfl

theorem cell23_4878817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_4878817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878817 prefixEnd_4878817 := by exact prefixLift 4878817
  have htrace : WordTrace (prefixWord ++ tailWord_4878817) baseStart_4878817 baseEnd_4878817 := by
    simpa [prefixWord, tailWord_4878817, baseEnd_4878817] using wordTrace_append hprefix tailTrace_4878817
  have hstable : (prefixWord ++ tailWord_4878817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878817).length < 2 ^ (prefixWord ++ tailWord_4878817).sum := by decide
  have hdescent : baseEnd_4878817 < baseStart_4878817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878827 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 3, 3, 2]
def baseStart_4878827 : Nat := 118140960795 + 4878827 * 2 ^ 59
def prefixEnd_4878827 : Nat := 4983230072969 + 3 ^ 40 * 4878827 * 2
def baseEnd_4878827 : Nat := 2505183281133288300625189

theorem tailTrace_4878827 : CollatzResearch.WordTrace tailWord_4878827 prefixEnd_4878827 2505183281133288300625189 := by
  unfold tailWord_4878827
  simp only [CollatzResearch.WordTrace]
  refine ⟨177945439495850491159298735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118630292997233660772865823 177945439495850491159298735)
  ·
    refine ⟨266918159243775736738948103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177945439495850491159298735 266918159243775736738948103)
    ·
      refine ⟨400377238865663605108422155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266918159243775736738948103 400377238865663605108422155)
      ·
        refine ⟨600565858298495407662633233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400377238865663605108422155 600565858298495407662633233)
        ·
          refine ⟨450424393723871555746974925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600565858298495407662633233 450424393723871555746974925)
          ·
            refine ⟨168909147646451833405115597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 450424393723871555746974925 168909147646451833405115597)
            ·
              refine ⟨63340930367419437526918349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168909147646451833405115597 63340930367419437526918349)
              ·
                refine ⟨23752848887782289072594381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63340930367419437526918349 23752848887782289072594381)
                ·
                  refine ⟨8907318332918358402222893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23752848887782289072594381 8907318332918358402222893)
                  ·
                    refine ⟨3340244374844384400833585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8907318332918358402222893 3340244374844384400833585)
                    ·
                      refine ⟨2505183281133288300625189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340244374844384400833585 2505183281133288300625189)
                      ·
                        rfl

theorem cell23_4878827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 3, 3, 2].length) (baseStart_4878827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878827 prefixEnd_4878827 := by exact prefixLift 4878827
  have htrace : WordTrace (prefixWord ++ tailWord_4878827) baseStart_4878827 baseEnd_4878827 := by
    simpa [prefixWord, tailWord_4878827, baseEnd_4878827] using wordTrace_append hprefix tailTrace_4878827
  have hstable : (prefixWord ++ tailWord_4878827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878827).length < 2 ^ (prefixWord ++ tailWord_4878827).sum := by decide
  have hdescent : baseEnd_4878827 < baseStart_4878827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878874 : List Nat := [3, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2]
def baseStart_4878874 : Nat := 118140960795 + 4878874 * 2 ^ 59
def prefixEnd_4878874 : Nat := 4983230072969 + 3 ^ 40 * 4878874 * 2
def baseEnd_4878874 : Nat := 2505207414724049616737473

theorem tailTrace_4878874 : CollatzResearch.WordTrace tailWord_4878874 prefixEnd_4878874 2505207414724049616737473 := by
  unfold tailWord_4878874
  simp only [CollatzResearch.WordTrace]
  refine ⟨44486788431670054546564919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118631435817786812124173117 44486788431670054546564919)
  ·
    refine ⟨66730182647505081819847379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44486788431670054546564919 66730182647505081819847379)
    ·
      refine ⟨100095273971257622729771069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66730182647505081819847379 100095273971257622729771069)
      ·
        refine ⟨37535727739221608523664151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100095273971257622729771069 37535727739221608523664151)
        ·
          refine ⟨56303591608832412785496227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37535727739221608523664151 56303591608832412785496227)
          ·
            refine ⟨84455387413248619178244341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56303591608832412785496227 84455387413248619178244341)
            ·
              refine ⟨7917692569992058047960407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84455387413248619178244341 7917692569992058047960407)
              ·
                refine ⟨11876538854988087071940611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7917692569992058047960407 11876538854988087071940611)
                ·
                  refine ⟨17814808282482130607910917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11876538854988087071940611 17814808282482130607910917)
                  ·
                    refine ⟨3340276552965399488983297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17814808282482130607910917 3340276552965399488983297)
                    ·
                      refine ⟨2505207414724049616737473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340276552965399488983297 2505207414724049616737473)
                      ·
                        rfl

theorem cell23_4878874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_4878874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878874 prefixEnd_4878874 := by exact prefixLift 4878874
  have htrace : WordTrace (prefixWord ++ tailWord_4878874) baseStart_4878874 baseEnd_4878874 := by
    simpa [prefixWord, tailWord_4878874, baseEnd_4878874] using wordTrace_append hprefix tailTrace_4878874
  have hstable : (prefixWord ++ tailWord_4878874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878874).length < 2 ^ (prefixWord ++ tailWord_4878874).sum := by decide
  have hdescent : baseEnd_4878874 < baseStart_4878874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878894 : List Nat := [4, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_4878894 : Nat := 118140960795 + 4878894 * 2 ^ 59
def prefixEnd_4878894 : Nat := 4983230072969 + 3 ^ 40 * 4878894 * 2
def baseEnd_4878894 : Nat := 2505217684337139538487381

theorem tailTrace_4878894 : CollatzResearch.WordTrace tailWord_4878894 prefixEnd_4878894 2505217684337139538487381 := by
  unfold tailWord_4878894
  simp only [CollatzResearch.WordTrace]
  refine ⟨22243485398325970200248467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118631922124405174401325157 22243485398325970200248467)
  ·
    refine ⟨33365228097488955300372701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22243485398325970200248467 33365228097488955300372701)
    ·
      refine ⟨12511960536558358237639763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33365228097488955300372701 12511960536558358237639763)
      ·
        refine ⟨18767940804837537356459645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12511960536558358237639763 18767940804837537356459645)
        ·
          refine ⟨7037977801814076508672367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18767940804837537356459645 7037977801814076508672367)
          ·
            refine ⟨10556966702721114763008551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7037977801814076508672367 10556966702721114763008551)
            ·
              refine ⟨15835450054081672144512827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10556966702721114763008551 15835450054081672144512827)
              ·
                refine ⟨23753175081122508216769241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15835450054081672144512827 23753175081122508216769241)
                ·
                  refine ⟨17814881310841881162576931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23753175081122508216769241 17814881310841881162576931)
                  ·
                    refine ⟨26722321966262821743865397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17814881310841881162576931 26722321966262821743865397)
                    ·
                      refine ⟨2505217684337139538487381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26722321966262821743865397 2505217684337139538487381)
                      ·
                        rfl

theorem cell23_4878894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_4878894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878894 prefixEnd_4878894 := by exact prefixLift 4878894
  have htrace : WordTrace (prefixWord ++ tailWord_4878894) baseStart_4878894 baseEnd_4878894 := by
    simpa [prefixWord, tailWord_4878894, baseEnd_4878894] using wordTrace_append hprefix tailTrace_4878894
  have hstable : (prefixWord ++ tailWord_4878894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878894).length < 2 ^ (prefixWord ++ tailWord_4878894).sum := by decide
  have hdescent : baseEnd_4878894 < baseStart_4878894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878925 : List Nat := [1, 6, 1, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_4878925 : Nat := 118140960795 + 4878925 * 2 ^ 59
def prefixEnd_4878925 : Nat := 4983230072969 + 3 ^ 40 * 4878925 * 2
def baseEnd_4878925 : Nat := 2505233602237428917199739

theorem tailTrace_4878925 : CollatzResearch.WordTrace tailWord_4878925 prefixEnd_4878925 2505233602237428917199739 := by
  unfold tailWord_4878925
  simp only [CollatzResearch.WordTrace]
  refine ⟨177949013849495453896366229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118632675899663635930910819 177949013849495453896366229)
  ·
    refine ⟨8341360024195099401392167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 177949013849495453896366229 8341360024195099401392167)
    ·
      refine ⟨12512040036292649102088251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8341360024195099401392167 12512040036292649102088251)
      ·
        refine ⟨18768060054438973653132377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12512040036292649102088251 18768060054438973653132377)
        ·
          refine ⟨14076045040829230239849283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18768060054438973653132377 14076045040829230239849283)
          ·
            refine ⟨21114067561243845359773925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14076045040829230239849283 21114067561243845359773925)
            ·
              refine ⟨3958887667733221004957611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21114067561243845359773925 3958887667733221004957611)
              ·
                refine ⟨5938331501599831507436417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3958887667733221004957611 5938331501599831507436417)
                ·
                  refine ⟨4453748626199873630577313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5938331501599831507436417 4453748626199873630577313)
                  ·
                    refine ⟨3340311469649905222932985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4453748626199873630577313 3340311469649905222932985)
                    ·
                      refine ⟨2505233602237428917199739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340311469649905222932985 2505233602237428917199739)
                      ·
                        rfl

theorem cell23_4878925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_4878925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878925 prefixEnd_4878925 := by exact prefixLift 4878925
  have htrace : WordTrace (prefixWord ++ tailWord_4878925) baseStart_4878925 baseEnd_4878925 := by
    simpa [prefixWord, tailWord_4878925, baseEnd_4878925] using wordTrace_append hprefix tailTrace_4878925
  have hstable : (prefixWord ++ tailWord_4878925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878925).length < 2 ^ (prefixWord ++ tailWord_4878925).sum := by decide
  have hdescent : baseEnd_4878925 < baseStart_4878925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878965 : List Nat := [1, 3, 4, 2, 3, 1, 2, 2, 5]
def baseStart_4878965 : Nat := 118140960795 + 4878965 * 2 ^ 59
def prefixEnd_4878965 : Nat := 4983230072969 + 3 ^ 40 * 4878965 * 2
def baseEnd_4878965 : Nat := 278361571273734306744395

theorem tailTrace_4878965 : CollatzResearch.WordTrace tailWord_4878965 prefixEnd_4878965 278361571273734306744395 := by
  unfold tailWord_4878965
  simp only [CollatzResearch.WordTrace]
  refine ⟨177950472769350540727822349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118633648512900360485214899 177950472769350540727822349)
  ·
    refine ⟨66731427288506452772933381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177950472769350540727822349 66731427288506452772933381)
    ·
      refine ⟨12512142616594959894925009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66731427288506452772933381 12512142616594959894925009)
      ·
        refine ⟨9384106962446219921193757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12512142616594959894925009 9384106962446219921193757)
        ·
          refine ⟨3519040110917332470447659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9384106962446219921193757 3519040110917332470447659)
          ·
            refine ⟨5278560166375998705671489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3519040110917332470447659 5278560166375998705671489)
            ·
              refine ⟨3958920124781999029253617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5278560166375998705671489 3958920124781999029253617)
              ·
                refine ⟨2969190093586499271940213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3958920124781999029253617 2969190093586499271940213)
                ·
                  refine ⟨278361571273734306744395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2969190093586499271940213 278361571273734306744395)
                  ·
                    rfl

theorem cell23_4878965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 3, 1, 2, 2, 5].length) (baseStart_4878965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878965 prefixEnd_4878965 := by exact prefixLift 4878965
  have htrace : WordTrace (prefixWord ++ tailWord_4878965) baseStart_4878965 baseEnd_4878965 := by
    simpa [prefixWord, tailWord_4878965, baseEnd_4878965] using wordTrace_append hprefix tailTrace_4878965
  have hstable : (prefixWord ++ tailWord_4878965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878965).length < 2 ^ (prefixWord ++ tailWord_4878965).sum := by decide
  have hdescent : baseEnd_4878965 < baseStart_4878965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4878970 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 12]
def baseStart_4878970 : Nat := 118140960795 + 4878970 * 2 ^ 59
def prefixEnd_4878970 : Nat := 4983230072969 + 3 ^ 40 * 4878970 * 2
def baseEnd_4878970 : Nat := 278361856540764582348559

theorem tailTrace_4878970 : CollatzResearch.WordTrace tailWord_4878970 prefixEnd_4878970 278361856540764582348559 := by
  unfold tailWord_4878970
  simp only [CollatzResearch.WordTrace]
  refine ⟨44487663783583106645438591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118633770089554951054502909 44487663783583106645438591)
  ·
    refine ⟨66731495675374659968157887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44487663783583106645438591 66731495675374659968157887)
    ·
      refine ⟨100097243513061989952236831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66731495675374659968157887 100097243513061989952236831)
      ·
        refine ⟨150145865269592984928355247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100097243513061989952236831 150145865269592984928355247)
        ·
          refine ⟨225218797904389477392532871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150145865269592984928355247 225218797904389477392532871)
          ·
            refine ⟨337828196856584216088799307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225218797904389477392532871 337828196856584216088799307)
            ·
              refine ⟨506742295284876324133198961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337828196856584216088799307 506742295284876324133198961)
              ·
                refine ⟨380056721463657243099899221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506742295284876324133198961 380056721463657243099899221)
                ·
                  refine ⟨278361856540764582348559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 380056721463657243099899221 278361856540764582348559)
                  ·
                    rfl

theorem cell23_4878970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 12].length) (baseStart_4878970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4878970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4878970 prefixEnd_4878970 := by exact prefixLift 4878970
  have htrace : WordTrace (prefixWord ++ tailWord_4878970) baseStart_4878970 baseEnd_4878970 := by
    simpa [prefixWord, tailWord_4878970, baseEnd_4878970] using wordTrace_append hprefix tailTrace_4878970
  have hstable : (prefixWord ++ tailWord_4878970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4878970).length < 2 ^ (prefixWord ++ tailWord_4878970).sum := by decide
  have hdescent : baseEnd_4878970 < baseStart_4878970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4878970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879008 : List Nat := [2, 1, 1, 4, 4, 1, 2, 3, 1, 4]
def baseStart_4879008 : Nat := 118140960795 + 4879008 * 2 ^ 59
def prefixEnd_4879008 : Nat := 4983230072969 + 3 ^ 40 * 4879008 * 2
def baseEnd_4879008 : Nat := 835092073710584030820619

theorem tailTrace_4879008 : CollatzResearch.WordTrace tailWord_4879008 prefixEnd_4879008 835092073710584030820619 := by
  unfold tailWord_4879008
  simp only [CollatzResearch.WordTrace]
  refine ⟨88976020554097379535818839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118634694072129839381091785 88976020554097379535818839)
  ·
    refine ⟨133464030831146069303728259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88976020554097379535818839 133464030831146069303728259)
    ·
      refine ⟨200196046246719103955592389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133464030831146069303728259 200196046246719103955592389)
      ·
        refine ⟨37536758671259831991673573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200196046246719103955592389 37536758671259831991673573)
        ·
          refine ⟨7038142250861218498438795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37536758671259831991673573 7038142250861218498438795)
          ·
            refine ⟨10557213376291827747658193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7038142250861218498438795 10557213376291827747658193)
            ·
              refine ⟨7917910032218870810743645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10557213376291827747658193 7917910032218870810743645)
              ·
                refine ⟨2969216262082076554028867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7917910032218870810743645 2969216262082076554028867)
                ·
                  refine ⟨4453824393123114831043301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969216262082076554028867 4453824393123114831043301)
                  ·
                    refine ⟨835092073710584030820619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4453824393123114831043301 835092073710584030820619)
                    ·
                      rfl

theorem cell23_4879008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3, 1, 4].length) (baseStart_4879008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879008 prefixEnd_4879008 := by exact prefixLift 4879008
  have htrace : WordTrace (prefixWord ++ tailWord_4879008) baseStart_4879008 baseEnd_4879008 := by
    simpa [prefixWord, tailWord_4879008, baseEnd_4879008] using wordTrace_append hprefix tailTrace_4879008
  have hstable : (prefixWord ++ tailWord_4879008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879008).length < 2 ^ (prefixWord ++ tailWord_4879008).sum := by decide
  have hdescent : baseEnd_4879008 < baseStart_4879008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879021 : List Nat := [1, 5, 2, 1, 1, 4, 1, 2, 6]
def baseStart_4879021 : Nat := 118140960795 + 4879021 * 2 ^ 59
def prefixEnd_4879021 : Nat := 4983230072969 + 3 ^ 40 * 4879021 * 2
def baseEnd_4879021 : Nat := 278364766264473393511033

theorem tailTrace_4879021 : CollatzResearch.WordTrace tailWord_4879021 prefixEnd_4879021 278364766264473393511033 := by
  unfold tailWord_4879021
  simp only [CollatzResearch.WordTrace]
  refine ⟨177952515257147662291860917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118635010171431774861240611 177952515257147662291860917)
  ·
    refine ⟨16683048305357593339861961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177952515257147662291860917 16683048305357593339861961)
    ·
      refine ⟨12512286229018195004896471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16683048305357593339861961 12512286229018195004896471)
      ·
        refine ⟨18768429343527292507344707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12512286229018195004896471 18768429343527292507344707)
        ·
          refine ⟨28152644015290938761017061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18768429343527292507344707 28152644015290938761017061)
          ·
            refine ⟨5278620752867051017690699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28152644015290938761017061 5278620752867051017690699)
            ·
              refine ⟨7917931129300576526536049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5278620752867051017690699 7917931129300576526536049)
              ·
                refine ⟨5938448346975432394902037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7917931129300576526536049 5938448346975432394902037)
                ·
                  refine ⟨278364766264473393511033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5938448346975432394902037 278364766264473393511033)
                  ·
                    rfl

theorem cell23_4879021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 1, 2, 6].length) (baseStart_4879021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879021 prefixEnd_4879021 := by exact prefixLift 4879021
  have htrace : WordTrace (prefixWord ++ tailWord_4879021) baseStart_4879021 baseEnd_4879021 := by
    simpa [prefixWord, tailWord_4879021, baseEnd_4879021] using wordTrace_append hprefix tailTrace_4879021
  have hstable : (prefixWord ++ tailWord_4879021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879021).length < 2 ^ (prefixWord ++ tailWord_4879021).sum := by decide
  have hdescent : baseEnd_4879021 < baseStart_4879021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879024 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 4, 3, 2]
def baseStart_4879024 : Nat := 118140960795 + 4879024 * 2 ^ 59
def prefixEnd_4879024 : Nat := 4983230072969 + 3 ^ 40 * 4879024 * 2
def baseEnd_4879024 : Nat := 2505284436822224029861783

theorem tailTrace_4879024 : CollatzResearch.WordTrace tailWord_4879024 prefixEnd_4879024 2505284436822224029861783 := by
  unfold tailWord_4879024
  simp only [CollatzResearch.WordTrace]
  refine ⟨88976312338068396902110063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118635083117424529202813417 88976312338068396902110063)
  ·
    refine ⟨133464468507102595353165095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88976312338068396902110063 133464468507102595353165095)
    ·
      refine ⟨200196702760653893029747643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133464468507102595353165095 200196702760653893029747643)
      ·
        refine ⟨300295054140980839544621465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200196702760653893029747643 300295054140980839544621465)
        ·
          refine ⟨225221290605735629658466099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300295054140980839544621465 225221290605735629658466099)
          ·
            refine ⟨337831935908603444487699149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225221290605735629658466099 337831935908603444487699149)
            ·
              refine ⟨126686975965726291682887181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 337831935908603444487699149 126686975965726291682887181)
              ·
                refine ⟨47507615987147359381082693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 126686975965726291682887181 47507615987147359381082693)
                ·
                  refine ⟨8907677997590129883953005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47507615987147359381082693 8907677997590129883953005)
                  ·
                    refine ⟨3340379249096298706482377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8907677997590129883953005 3340379249096298706482377)
                    ·
                      refine ⟨2505284436822224029861783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340379249096298706482377 2505284436822224029861783)
                      ·
                        rfl

theorem cell23_4879024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 4, 3, 2].length) (baseStart_4879024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879024 prefixEnd_4879024 := by exact prefixLift 4879024
  have htrace : WordTrace (prefixWord ++ tailWord_4879024) baseStart_4879024 baseEnd_4879024 := by
    simpa [prefixWord, tailWord_4879024, baseEnd_4879024] using wordTrace_append hprefix tailTrace_4879024
  have hstable : (prefixWord ++ tailWord_4879024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879024).length < 2 ^ (prefixWord ++ tailWord_4879024).sum := by decide
  have hdescent : baseEnd_4879024 < baseStart_4879024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879047 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 1, 6]
def baseStart_4879047 : Nat := 118140960795 + 4879047 * 2 ^ 59
def prefixEnd_4879047 : Nat := 4983230072969 + 3 ^ 40 * 4879047 * 2
def baseEnd_4879047 : Nat := 835098748959092479958059

theorem tailTrace_4879047 : CollatzResearch.WordTrace tailWord_4879047 prefixEnd_4879047 835098748959092479958059 := by
  unfold tailWord_4879047
  simp only [CollatzResearch.WordTrace]
  refine ⟨177953463555053468732307395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118635642370035645821538263 177953463555053468732307395)
  ·
    refine ⟨266930195332580203098461093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177953463555053468732307395 266930195332580203098461093)
    ·
      refine ⟨50049411624858788080961455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266930195332580203098461093 50049411624858788080961455)
      ·
        refine ⟨75074117437288182121442183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50049411624858788080961455 75074117437288182121442183)
        ·
          refine ⟨112611176155932273182163275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75074117437288182121442183 112611176155932273182163275)
          ·
            refine ⟨168916764233898409773244913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112611176155932273182163275 168916764233898409773244913)
            ·
              refine ⟨126687573175423807329933685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 168916764233898409773244913 126687573175423807329933685)
              ·
                refine ⟨11876959985195981937181283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 126687573175423807329933685 11876959985195981937181283)
                ·
                  refine ⟨17815439977793972905771925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11876959985195981937181283 17815439977793972905771925)
                  ·
                    refine ⟨835098748959092479958059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17815439977793972905771925 835098748959092479958059)
                    ·
                      rfl

theorem cell23_4879047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_4879047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879047 prefixEnd_4879047 := by exact prefixLift 4879047
  have htrace : WordTrace (prefixWord ++ tailWord_4879047) baseStart_4879047 baseEnd_4879047 := by
    simpa [prefixWord, tailWord_4879047, baseEnd_4879047] using wordTrace_append hprefix tailTrace_4879047
  have hstable : (prefixWord ++ tailWord_4879047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879047).length < 2 ^ (prefixWord ++ tailWord_4879047).sum := by decide
  have hdescent : baseEnd_4879047 < baseStart_4879047 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879057 : List Nat := [1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 5]
def baseStart_4879057 : Nat := 118140960795 + 4879057 * 2 ^ 59
def prefixEnd_4879057 : Nat := 4983230072969 + 3 ^ 40 * 4879057 * 2
def baseEnd_4879057 : Nat := 2505301381683822400749131

theorem tailTrace_4879057 : CollatzResearch.WordTrace tailWord_4879057 prefixEnd_4879057 2505301381683822400749131 := by
  unfold tailWord_4879057
  simp only [CollatzResearch.WordTrace]
  refine ⟨177953828285017240440171425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118635885523344826960114283 177953828285017240440171425)
  ·
    refine ⟨133465371213762930330128569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177953828285017240440171425 133465371213762930330128569)
    ·
      refine ⟨100099028410322197747596427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133465371213762930330128569 100099028410322197747596427)
      ·
        refine ⟨150148542615483296621394641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100099028410322197747596427 150148542615483296621394641)
        ·
          refine ⟨112611406961612472466045981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150148542615483296621394641 112611406961612472466045981)
          ·
            refine ⟨42229277610604677174767243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112611406961612472466045981 42229277610604677174767243)
            ·
              refine ⟨63343916415907015762150865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42229277610604677174767243 63343916415907015762150865)
              ·
                refine ⟨47507937311930261821613149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63343916415907015762150865 47507937311930261821613149)
                ·
                  refine ⟨17815476491973848183104931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47507937311930261821613149 17815476491973848183104931)
                  ·
                    refine ⟨26723214737960772274657397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17815476491973848183104931 26723214737960772274657397)
                    ·
                      refine ⟨2505301381683822400749131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26723214737960772274657397 2505301381683822400749131)
                      ·
                        rfl

theorem cell23_4879057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_4879057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879057 prefixEnd_4879057 := by exact prefixLift 4879057
  have htrace : WordTrace (prefixWord ++ tailWord_4879057) baseStart_4879057 baseEnd_4879057 := by
    simpa [prefixWord, tailWord_4879057, baseEnd_4879057] using wordTrace_append hprefix tailTrace_4879057
  have hstable : (prefixWord ++ tailWord_4879057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879057).length < 2 ^ (prefixWord ++ tailWord_4879057).sum := by decide
  have hdescent : baseEnd_4879057 < baseStart_4879057 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879064 : List Nat := [2, 1, 2, 2, 3, 2, 1, 2, 4, 4]
def baseStart_4879064 : Nat := 118140960795 + 4879064 * 2 ^ 59
def prefixEnd_4879064 : Nat := 4983230072969 + 3 ^ 40 * 4879064 * 2
def baseEnd_4879064 : Nat := 835101658682801291120533

theorem tailTrace_4879064 : CollatzResearch.WordTrace tailWord_4879064 prefixEnd_4879064 835101658682801291120533 := by
  unfold tailWord_4879064
  simp only [CollatzResearch.WordTrace]
  refine ⟨88977041797995940317838123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118636055730661253757117497 88977041797995940317838123)
  ·
    refine ⟨133465562696993910476757185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88977041797995940317838123 133465562696993910476757185)
    ·
      refine ⟨100099172022745432857567889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133465562696993910476757185 100099172022745432857567889)
      ·
        refine ⟨75074379017059074643175917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100099172022745432857567889 75074379017059074643175917)
        ·
          refine ⟨28152892131397152991190969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75074379017059074643175917 28152892131397152991190969)
          ·
            refine ⟨21114669098547864743393227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28152892131397152991190969 21114669098547864743393227)
            ·
              refine ⟨31672003647821797115089841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21114669098547864743393227 31672003647821797115089841)
              ·
                refine ⟨23754002735866347836317381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31672003647821797115089841 23754002735866347836317381)
                ·
                  refine ⟨4453875512974940219309509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23754002735866347836317381 4453875512974940219309509)
                  ·
                    refine ⟨835101658682801291120533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4453875512974940219309509 835101658682801291120533)
                    ·
                      rfl

theorem cell23_4879064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_4879064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879064 prefixEnd_4879064 := by exact prefixLift 4879064
  have htrace : WordTrace (prefixWord ++ tailWord_4879064) baseStart_4879064 baseEnd_4879064 := by
    simpa [prefixWord, tailWord_4879064, baseEnd_4879064] using wordTrace_append hprefix tailTrace_4879064
  have hstable : (prefixWord ++ tailWord_4879064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879064).length < 2 ^ (prefixWord ++ tailWord_4879064).sum := by decide
  have hdescent : baseEnd_4879064 < baseStart_4879064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879077 : List Nat := [1, 3, 1, 4, 1, 2, 11]
def baseStart_4879077 : Nat := 118140960795 + 4879077 * 2 ^ 59
def prefixEnd_4879077 : Nat := 4983230072969 + 3 ^ 40 * 4879077 * 2
def baseEnd_4879077 : Nat := 30929773472801386697519

theorem tailTrace_4879077 : CollatzResearch.WordTrace tailWord_4879077 prefixEnd_4879077 30929773472801386697519 := by
  unfold tailWord_4879077
  simp only [CollatzResearch.WordTrace]
  refine ⟨177954557744944783855899485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118636371829963189237266323 177954557744944783855899485)
  ·
    refine ⟨66732959154354293945962307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177954557744944783855899485 66732959154354293945962307)
    ·
      refine ⟨100099438731531440918943461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66732959154354293945962307 100099438731531440918943461)
      ·
        refine ⟨18768644762162145172301899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100099438731531440918943461 18768644762162145172301899)
        ·
          refine ⟨28152967143243217758452849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18768644762162145172301899 28152967143243217758452849)
          ·
            refine ⟨21114725357432413318839637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28152967143243217758452849 21114725357432413318839637)
            ·
              refine ⟨30929773472801386697519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21114725357432413318839637 30929773472801386697519)
              ·
                rfl

theorem cell23_4879077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 11].length) (baseStart_4879077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879077 prefixEnd_4879077 := by exact prefixLift 4879077
  have htrace : WordTrace (prefixWord ++ tailWord_4879077) baseStart_4879077 baseEnd_4879077 := by
    simpa [prefixWord, tailWord_4879077, baseEnd_4879077] using wordTrace_append hprefix tailTrace_4879077
  have hstable : (prefixWord ++ tailWord_4879077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879077).length < 2 ^ (prefixWord ++ tailWord_4879077).sum := by decide
  have hdescent : baseEnd_4879077 < baseStart_4879077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879094 : List Nat := [5, 1, 1, 1, 1, 2, 4, 8]
def baseStart_4879094 : Nat := 118140960795 + 4879094 * 2 ^ 59
def prefixEnd_4879094 : Nat := 4983230072969 + 3 ^ 40 * 4879094 * 2
def baseEnd_4879094 : Nat := 92789643721038472443943

theorem tailTrace_4879094 : CollatzResearch.WordTrace tailWord_4879094 prefixEnd_4879094 92789643721038472443943 := by
  unfold tailWord_4879094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11122198611617699734954271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118636785190588797172845557 11122198611617699734954271)
  ·
    refine ⟨16683297917426549602431407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11122198611617699734954271 16683297917426549602431407)
    ·
      refine ⟨25024946876139824403647111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16683297917426549602431407 25024946876139824403647111)
      ·
        refine ⟨37537420314209736605470667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25024946876139824403647111 37537420314209736605470667)
        ·
          refine ⟨56306130471314604908206001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37537420314209736605470667 56306130471314604908206001)
          ·
            refine ⟨42229597853485953681154501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56306130471314604908206001 42229597853485953681154501)
            ·
              refine ⟨7918049597528616315216469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42229597853485953681154501 7918049597528616315216469)
              ·
                refine ⟨92789643721038472443943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7918049597528616315216469 92789643721038472443943)
                ·
                  rfl

theorem cell23_4879094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 4, 8].length) (baseStart_4879094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879094 prefixEnd_4879094 := by exact prefixLift 4879094
  have htrace : WordTrace (prefixWord ++ tailWord_4879094) baseStart_4879094 baseEnd_4879094 := by
    simpa [prefixWord, tailWord_4879094, baseEnd_4879094] using wordTrace_append hprefix tailTrace_4879094
  have hstable : (prefixWord ++ tailWord_4879094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879094).length < 2 ^ (prefixWord ++ tailWord_4879094).sum := by decide
  have hdescent : baseEnd_4879094 < baseStart_4879094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879138 : List Nat := [3, 3, 1, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_4879138 : Nat := 118140960795 + 4879138 * 2 ^ 59
def prefixEnd_4879138 : Nat := 4983230072969 + 3 ^ 40 * 4879138 * 2
def baseEnd_4879138 : Nat := 2505342973616836583836259

theorem tailTrace_4879138 : CollatzResearch.WordTrace tailWord_4879138 prefixEnd_4879138 2505342973616836583836259 := by
  unfold tailWord_4879138
  simp only [CollatzResearch.WordTrace]
  refine ⟨44489195649430947818467517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118637855065149194182580045 44489195649430947818467517)
  ·
    refine ⟨16683448368536605431925319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44489195649430947818467517 16683448368536605431925319)
    ·
      refine ⟨25025172552804908147887979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16683448368536605431925319 25025172552804908147887979)
      ·
        refine ⟨37537758829207362221831969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25025172552804908147887979 37537758829207362221831969)
        ·
          refine ⟨28153319121905521666373977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37537758829207362221831969 28153319121905521666373977)
          ·
            refine ⟨21114989341429141249780483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28153319121905521666373977 21114989341429141249780483)
            ·
              refine ⟨31672484012143711874670725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21114989341429141249780483 31672484012143711874670725)
              ·
                refine ⟨5938590752276945976500761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31672484012143711874670725 5938590752276945976500761)
                ·
                  refine ⟨4453943064207709482375571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5938590752276945976500761 4453943064207709482375571)
                  ·
                    refine ⟨6680914596311564223563357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4453943064207709482375571 6680914596311564223563357)
                    ·
                      refine ⟨2505342973616836583836259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6680914596311564223563357 2505342973616836583836259)
                      ·
                        rfl

theorem cell23_4879138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_4879138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879138 prefixEnd_4879138 := by exact prefixLift 4879138
  have htrace : WordTrace (prefixWord ++ tailWord_4879138) baseStart_4879138 baseEnd_4879138 := by
    simpa [prefixWord, tailWord_4879138, baseEnd_4879138] using wordTrace_append hprefix tailTrace_4879138
  have hstable : (prefixWord ++ tailWord_4879138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879138).length < 2 ^ (prefixWord ++ tailWord_4879138).sum := by decide
  have hdescent : baseEnd_4879138 < baseStart_4879138 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879144 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_4879144 : Nat := 118140960795 + 4879144 * 2 ^ 59
def prefixEnd_4879144 : Nat := 4983230072969 + 3 ^ 40 * 4879144 * 2
def baseEnd_4879144 : Nat := 2505346054500763560361231

theorem tailTrace_4879144 : CollatzResearch.WordTrace tailWord_4879144 prefixEnd_4879144 2505346054500763560361231 := by
  unfold tailWord_4879144
  simp only [CollatzResearch.WordTrace]
  refine ⟨88978500717851027149294243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118638000957134702865725657 88978500717851027149294243)
  ·
    refine ⟨133467751076776540723941365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88978500717851027149294243 133467751076776540723941365)
    ·
      refine ⟨12512601663447800692869503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133467751076776540723941365 12512601663447800692869503)
      ·
        refine ⟨18768902495171701039304255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12512601663447800692869503 18768902495171701039304255)
        ·
          refine ⟨28153353742757551558956383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18768902495171701039304255 28153353742757551558956383)
          ·
            refine ⟨42230030614136327338434575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28153353742757551558956383 42230030614136327338434575)
            ·
              refine ⟨63345045921204491007651863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42230030614136327338434575 63345045921204491007651863)
              ·
                refine ⟨95017568881806736511477795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63345045921204491007651863 95017568881806736511477795)
                ·
                  refine ⟨142526353322710104767216693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95017568881806736511477795 142526353322710104767216693)
                  ·
                    refine ⟨13361845624004072321926565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 142526353322710104767216693 13361845624004072321926565)
                    ·
                      refine ⟨2505346054500763560361231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13361845624004072321926565 2505346054500763560361231)
                      ·
                        rfl

theorem cell23_4879144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_4879144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879144 prefixEnd_4879144 := by exact prefixLift 4879144
  have htrace : WordTrace (prefixWord ++ tailWord_4879144) baseStart_4879144 baseEnd_4879144 := by
    simpa [prefixWord, tailWord_4879144, baseEnd_4879144] using wordTrace_append hprefix tailTrace_4879144
  have hstable : (prefixWord ++ tailWord_4879144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879144).length < 2 ^ (prefixWord ++ tailWord_4879144).sum := by decide
  have hdescent : baseEnd_4879144 < baseStart_4879144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879147 : List Nat := [1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 5]
def baseStart_4879147 : Nat := 118140960795 + 4879147 * 2 ^ 59
def prefixEnd_4879147 : Nat := 4983230072969 + 3 ^ 40 * 4879147 * 2
def baseEnd_4879147 : Nat := 2505347594942727048623717

theorem tailTrace_4879147 : CollatzResearch.WordTrace tailWord_4879147 prefixEnd_4879147 2505347594942727048623717 := by
  unfold tailWord_4879147
  simp only [CollatzResearch.WordTrace]
  refine ⟨177957110854691185810947695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118638073903127457207298463 177957110854691185810947695)
  ·
    refine ⟨266935666282036778716421543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177957110854691185810947695 266935666282036778716421543)
    ·
      refine ⟨400403499423055168074632315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266935666282036778716421543 400403499423055168074632315)
      ·
        refine ⟨600605249134582752111948473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400403499423055168074632315 600605249134582752111948473)
        ·
          refine ⟨450453936850937064083961355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 600605249134582752111948473 450453936850937064083961355)
          ·
            refine ⟨675680905276405596125942033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 450453936850937064083961355 675680905276405596125942033)
            ·
              refine ⟨506760678957304197094456525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 675680905276405596125942033 506760678957304197094456525)
              ·
                refine ⟨190035254608989073910421197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 506760678957304197094456525 190035254608989073910421197)
                ·
                  refine ⟨71263220478370902716407949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 190035254608989073910421197 71263220478370902716407949)
                  ·
                    refine ⟨26723707679389088518652981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71263220478370902716407949 26723707679389088518652981)
                    ·
                      refine ⟨2505347594942727048623717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26723707679389088518652981 2505347594942727048623717)
                      ·
                        rfl

theorem cell23_4879147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 5].length) (baseStart_4879147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879147 prefixEnd_4879147 := by exact prefixLift 4879147
  have htrace : WordTrace (prefixWord ++ tailWord_4879147) baseStart_4879147 baseEnd_4879147 := by
    simpa [prefixWord, tailWord_4879147, baseEnd_4879147] using wordTrace_append hprefix tailTrace_4879147
  have hstable : (prefixWord ++ tailWord_4879147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879147).length < 2 ^ (prefixWord ++ tailWord_4879147).sum := by decide
  have hdescent : baseEnd_4879147 < baseStart_4879147 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879154 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 2, 6]
def baseStart_4879154 : Nat := 118140960795 + 4879154 * 2 ^ 59
def prefixEnd_4879154 : Nat := 4983230072969 + 3 ^ 40 * 4879154 * 2
def baseEnd_4879154 : Nat := 835117063102436173745395

theorem tailTrace_4879154 : CollatzResearch.WordTrace tailWord_4879154 prefixEnd_4879154 835117063102436173745395 := by
  unfold tailWord_4879154
  simp only [CollatzResearch.WordTrace]
  refine ⟨44489341541416456501613129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118638244110443884004301677 44489341541416456501613129)
  ·
    refine ⟨33367006156062342376209847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44489341541416456501613129 33367006156062342376209847)
    ·
      refine ⟨50050509234093513564314771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33367006156062342376209847 50050509234093513564314771)
      ·
        refine ⟨75075763851140270346472157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50050509234093513564314771 75075763851140270346472157)
        ·
          refine ⟨28153411444177601379927059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75075763851140270346472157 28153411444177601379927059)
          ·
            refine ⟨42230117166266402069890589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28153411444177601379927059 42230117166266402069890589)
            ·
              refine ⟨15836293937349900776208971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42230117166266402069890589 15836293937349900776208971)
              ·
                refine ⟨23754440906024851164313457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15836293937349900776208971 23754440906024851164313457)
                ·
                  refine ⟨17815830679518638373235093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23754440906024851164313457 17815830679518638373235093)
                  ·
                    refine ⟨835117063102436173745395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17815830679518638373235093 835117063102436173745395)
                    ·
                      rfl

theorem cell23_4879154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 6].length) (baseStart_4879154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879154 prefixEnd_4879154 := by exact prefixLift 4879154
  have htrace : WordTrace (prefixWord ++ tailWord_4879154) baseStart_4879154 baseEnd_4879154 := by
    simpa [prefixWord, tailWord_4879154, baseEnd_4879154] using wordTrace_append hprefix tailTrace_4879154
  have hstable : (prefixWord ++ tailWord_4879154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879154).length < 2 ^ (prefixWord ++ tailWord_4879154).sum := by decide
  have hdescent : baseEnd_4879154 < baseStart_4879154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879164 : List Nat := [2, 2, 2, 2, 1, 1, 1, 1, 4, 4, 3]
def baseStart_4879164 : Nat := 118140960795 + 4879164 * 2 ^ 59
def prefixEnd_4879164 : Nat := 4983230072969 + 3 ^ 40 * 4879164 * 2
def baseEnd_4879164 : Nat := 2505356324113853482111139

theorem tailTrace_4879164 : CollatzResearch.WordTrace tailWord_4879164 prefixEnd_4879164 2505356324113853482111139 := by
  unfold tailWord_4879164
  simp only [CollatzResearch.WordTrace]
  refine ⟨88978865447814798857158273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118638487263753065142877697 88978865447814798857158273)
  ·
    refine ⟨66734149085861099142868705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88978865447814798857158273 66734149085861099142868705)
    ·
      refine ⟨50050611814395824357151529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66734149085861099142868705 50050611814395824357151529)
      ·
        refine ⟨37537958860796868267863647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50050611814395824357151529 37537958860796868267863647)
        ·
          refine ⟨56306938291195302401795471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37537958860796868267863647 56306938291195302401795471)
          ·
            refine ⟨84460407436792953602693207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56306938291195302401795471 84460407436792953602693207)
            ·
              refine ⟨126690611155189430404039811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84460407436792953602693207 126690611155189430404039811)
              ·
                refine ⟨190035916732784145606059717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 126690611155189430404039811 190035916732784145606059717)
                ·
                  refine ⟨35631734387397027301136197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 190035916732784145606059717 35631734387397027301136197)
                  ·
                    refine ⟨6680950197636942618963037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35631734387397027301136197 6680950197636942618963037)
                    ·
                      refine ⟨2505356324113853482111139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6680950197636942618963037 2505356324113853482111139)
                      ·
                        rfl

theorem cell23_4879164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_4879164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879164 prefixEnd_4879164 := by exact prefixLift 4879164
  have htrace : WordTrace (prefixWord ++ tailWord_4879164) baseStart_4879164 baseEnd_4879164 := by
    simpa [prefixWord, tailWord_4879164, baseEnd_4879164] using wordTrace_append hprefix tailTrace_4879164
  have hstable : (prefixWord ++ tailWord_4879164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879164).length < 2 ^ (prefixWord ++ tailWord_4879164).sum := by decide
  have hdescent : baseEnd_4879164 < baseStart_4879164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879251 : List Nat := [1, 1, 1, 2, 1, 2, 1, 6, 2, 4, 2]
def baseStart_4879251 : Nat := 118140960795 + 4879251 * 2 ^ 59
def prefixEnd_4879251 : Nat := 4983230072969 + 3 ^ 40 * 4879251 * 2
def baseEnd_4879251 : Nat := 2505400996930794641723239

theorem tailTrace_4879251 : CollatzResearch.WordTrace tailWord_4879251 prefixEnd_4879251 2505400996930794641723239 := by
  unfold tailWord_4879251
  simp only [CollatzResearch.WordTrace]
  refine ⟨177960904046314411572733607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118640602697542941048489071 177960904046314411572733607)
  ·
    refine ⟨266941356069471617359100411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177960904046314411572733607 266941356069471617359100411)
    ·
      refine ⟨400412034104207426038650617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266941356069471617359100411 400412034104207426038650617)
      ·
        refine ⟨300309025578155569528987963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 400412034104207426038650617 300309025578155569528987963)
        ·
          refine ⟨450463538367233354293481945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300309025578155569528987963 450463538367233354293481945)
          ·
            refine ⟨337847653775425015720111459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 450463538367233354293481945 337847653775425015720111459)
            ·
              refine ⟨506771480663137523580167189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337847653775425015720111459 506771480663137523580167189)
              ·
                refine ⟨23754913156084571417820337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 506771480663137523580167189 23754913156084571417820337)
                ·
                  refine ⟨17816184867063428563365253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23754913156084571417820337 17816184867063428563365253)
                  ·
                    refine ⟨3340534662574392855630985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17816184867063428563365253 3340534662574392855630985)
                    ·
                      refine ⟨2505400996930794641723239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340534662574392855630985 2505400996930794641723239)
                      ·
                        rfl

theorem cell23_4879251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 6, 2, 4, 2].length) (baseStart_4879251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879251 prefixEnd_4879251 := by exact prefixLift 4879251
  have htrace : WordTrace (prefixWord ++ tailWord_4879251) baseStart_4879251 baseEnd_4879251 := by
    simpa [prefixWord, tailWord_4879251, baseEnd_4879251] using wordTrace_append hprefix tailTrace_4879251
  have hstable : (prefixWord ++ tailWord_4879251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879251).length < 2 ^ (prefixWord ++ tailWord_4879251).sum := by decide
  have hdescent : baseEnd_4879251 < baseStart_4879251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879264 : List Nat := [2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 6]
def baseStart_4879264 : Nat := 118140960795 + 4879264 * 2 ^ 59
def prefixEnd_4879264 : Nat := 4983230072969 + 3 ^ 40 * 4879264 * 2
def baseEnd_4879264 : Nat := 2505407672179303090860679

theorem tailTrace_4879264 : CollatzResearch.WordTrace tailWord_4879264 prefixEnd_4879264 2505407672179303090860679 := by
  unfold tailWord_4879264
  simp only [CollatzResearch.WordTrace]
  refine ⟨88980689097633657396478423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118640918796844876528637897 88980689097633657396478423)
  ·
    refine ⟨133471033646450486094717635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88980689097633657396478423 133471033646450486094717635)
    ·
      refine ⟨200206550469675729142076453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133471033646450486094717635 200206550469675729142076453)
      ·
        refine ⟨37538728213064199214139335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200206550469675729142076453 37538728213064199214139335)
        ·
          refine ⟨56308092319596298821209003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37538728213064199214139335 56308092319596298821209003)
          ·
            refine ⟨84462138479394448231813505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56308092319596298821209003 84462138479394448231813505)
            ·
              refine ⟨63346603859545836173860129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84462138479394448231813505 63346603859545836173860129)
              ·
                refine ⟨47509952894659377130395097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63346603859545836173860129 47509952894659377130395097)
                ·
                  refine ⟨35632464670994532847796323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47509952894659377130395097 35632464670994532847796323)
                  ·
                    refine ⟨53448697006491799271694485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35632464670994532847796323 53448697006491799271694485)
                    ·
                      refine ⟨2505407672179303090860679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53448697006491799271694485 2505407672179303090860679)
                      ·
                        rfl

theorem cell23_4879264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_4879264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879264 prefixEnd_4879264 := by exact prefixLift 4879264
  have htrace : WordTrace (prefixWord ++ tailWord_4879264) baseStart_4879264 baseEnd_4879264 := by
    simpa [prefixWord, tailWord_4879264, baseEnd_4879264] using wordTrace_append hprefix tailTrace_4879264
  have hstable : (prefixWord ++ tailWord_4879264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879264).length < 2 ^ (prefixWord ++ tailWord_4879264).sum := by decide
  have hdescent : baseEnd_4879264 < baseStart_4879264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879288 : List Nat := [2, 1, 2, 1, 2, 5, 2, 1, 2, 2, 3]
def baseStart_4879288 : Nat := 118140960795 + 4879288 * 2 ^ 59
def prefixEnd_4879288 : Nat := 4983230072969 + 3 ^ 40 * 4879288 * 2
def baseEnd_4879288 : Nat := 2505419995715010996960569

theorem tailTrace_4879288 : CollatzResearch.WordTrace tailWord_4879288 prefixEnd_4879288 2505419995715010996960569 := by
  unfold tailWord_4879288
  simp only [CollatzResearch.WordTrace]
  refine ⟨88981126773590183445915259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118641502364786911261220345 88981126773590183445915259)
  ·
    refine ⟨133471690160385275168872889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88981126773590183445915259 133471690160385275168872889)
    ·
      refine ⟨100103767620288956376654667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133471690160385275168872889 100103767620288956376654667)
      ·
        refine ⟨150155651430433434564982001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100103767620288956376654667 150155651430433434564982001)
        ·
          refine ⟨112616738572825075923736501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150155651430433434564982001 112616738572825075923736501)
          ·
            refine ⟨10557819241202350867850297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 112616738572825075923736501 10557819241202350867850297)
            ·
              refine ⟨7918364430901763150887723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10557819241202350867850297 7918364430901763150887723)
              ·
                refine ⟨11877546646352644726331585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7918364430901763150887723 11877546646352644726331585)
                ·
                  refine ⟨8908159984764483544748689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11877546646352644726331585 8908159984764483544748689)
                  ·
                    refine ⟨6681119988573362658561517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8908159984764483544748689 6681119988573362658561517)
                    ·
                      refine ⟨2505419995715010996960569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6681119988573362658561517 2505419995715010996960569)
                      ·
                        rfl

theorem cell23_4879288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_4879288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879288 prefixEnd_4879288 := by exact prefixLift 4879288
  have htrace : WordTrace (prefixWord ++ tailWord_4879288) baseStart_4879288 baseEnd_4879288 := by
    simpa [prefixWord, tailWord_4879288, baseEnd_4879288] using wordTrace_append hprefix tailTrace_4879288
  have hstable : (prefixWord ++ tailWord_4879288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879288).length < 2 ^ (prefixWord ++ tailWord_4879288).sum := by decide
  have hdescent : baseEnd_4879288 < baseStart_4879288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879321 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 3, 5]
def baseStart_4879321 : Nat := 118140960795 + 4879321 * 2 ^ 59
def prefixEnd_4879321 : Nat := 4983230072969 + 3 ^ 40 * 4879321 * 2
def baseEnd_4879321 : Nat := 835145646858869789282639

theorem tailTrace_4879321 : CollatzResearch.WordTrace tailWord_4879321 prefixEnd_4879321 835145646858869789282639 := by
  unfold tailWord_4879321
  simp only [CollatzResearch.WordTrace]
  refine ⟨177963457156060813527781817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118642304770707209018521211 177963457156060813527781817)
  ·
    refine ⟨133472592867045610145836363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177963457156060813527781817 133472592867045610145836363)
    ·
      refine ⟨200208889300568415218754545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133472592867045610145836363 200208889300568415218754545)
      ·
        refine ⟨150156666975426311414065909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200208889300568415218754545 150156666975426311414065909)
        ·
          refine ⟨14077187528946216695068679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150156666975426311414065909 14077187528946216695068679)
          ·
            refine ⟨21115781293419325042603019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14077187528946216695068679 21115781293419325042603019)
            ·
              refine ⟨31673671940128987563904529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21115781293419325042603019 31673671940128987563904529)
              ·
                refine ⟨23755253955096740672928397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31673671940128987563904529 23755253955096740672928397)
                ·
                  refine ⟨8908220233161277752348149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23755253955096740672928397 8908220233161277752348149)
                  ·
                    refine ⟨835145646858869789282639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8908220233161277752348149 835145646858869789282639)
                    ·
                      rfl

theorem cell23_4879321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 5].length) (baseStart_4879321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879321 prefixEnd_4879321 := by exact prefixLift 4879321
  have htrace : WordTrace (prefixWord ++ tailWord_4879321) baseStart_4879321 baseEnd_4879321 := by
    simpa [prefixWord, tailWord_4879321, baseEnd_4879321] using wordTrace_append hprefix tailTrace_4879321
  have hstable : (prefixWord ++ tailWord_4879321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879321).length < 2 ^ (prefixWord ++ tailWord_4879321).sum := by decide
  have hdescent : baseEnd_4879321 < baseStart_4879321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879335 : List Nat := [1, 1, 5, 2, 2, 2, 1, 2, 3, 1, 3]
def baseStart_4879335 : Nat := 118140960795 + 4879335 * 2 ^ 59
def prefixEnd_4879335 : Nat := 4983230072969 + 3 ^ 40 * 4879335 * 2
def baseEnd_4879335 : Nat := 2505444129305772313072853

theorem tailTrace_4879335 : CollatzResearch.WordTrace tailWord_4879335 prefixEnd_4879335 2505444129305772313072853 := by
  unfold tailWord_4879335
  simp only [CollatzResearch.WordTrace]
  refine ⟨177963967778010093918791459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118642645185340062612527639 177963967778010093918791459)
  ·
    refine ⟨266945951667015140878187189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177963967778010093918791459 266945951667015140878187189)
    ·
      refine ⟨25026182968782669457330049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 266945951667015140878187189 25026182968782669457330049)
      ·
        refine ⟨18769637226587002092997537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25026182968782669457330049 18769637226587002092997537)
        ·
          refine ⟨14077227919940251569748153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18769637226587002092997537 14077227919940251569748153)
          ·
            refine ⟨10557920939955188677311115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14077227919940251569748153 10557920939955188677311115)
            ·
              refine ⟨15836881409932783015966673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10557920939955188677311115 15836881409932783015966673)
              ·
                refine ⟨11877661057449587261975005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15836881409932783015966673 11877661057449587261975005)
                ·
                  refine ⟨4454122896543595223240627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11877661057449587261975005 4454122896543595223240627)
                  ·
                    refine ⟨6681184344815392834860941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4454122896543595223240627 6681184344815392834860941)
                    ·
                      refine ⟨2505444129305772313072853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6681184344815392834860941 2505444129305772313072853)
                      ·
                        rfl

theorem cell23_4879335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_4879335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879335 prefixEnd_4879335 := by exact prefixLift 4879335
  have htrace : WordTrace (prefixWord ++ tailWord_4879335) baseStart_4879335 baseEnd_4879335 := by
    simpa [prefixWord, tailWord_4879335, baseEnd_4879335] using wordTrace_append hprefix tailTrace_4879335
  have hstable : (prefixWord ++ tailWord_4879335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879335).length < 2 ^ (prefixWord ++ tailWord_4879335).sum := by decide
  have hdescent : baseEnd_4879335 < baseStart_4879335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879345 : List Nat := [1, 2, 2, 2, 4, 1, 3, 1, 2, 3, 2]
def baseStart_4879345 : Nat := 118140960795 + 4879345 * 2 ^ 59
def prefixEnd_4879345 : Nat := 4983230072969 + 3 ^ 40 * 4879345 * 2
def baseEnd_4879345 : Nat := 2505449264112317273947807

theorem tailTrace_4879345 : CollatzResearch.WordTrace tailWord_4879345 prefixEnd_4879345 2505449264112317273947807 := by
  unfold tailWord_4879345
  simp only [CollatzResearch.WordTrace]
  refine ⟨177964332507973865626655489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118642888338649243751103659 177964332507973865626655489)
  ·
    refine ⟨133473249380980399219991617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177964332507973865626655489 133473249380980399219991617)
    ·
      refine ⟨100104937035735299414993713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133473249380980399219991617 100104937035735299414993713)
      ·
        refine ⟨75078702776801474561245285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100104937035735299414993713 75078702776801474561245285)
        ·
          refine ⟨14077256770650276480233491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75078702776801474561245285 14077256770650276480233491)
          ·
            refine ⟨21115885155975414720350237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14077256770650276480233491 21115885155975414720350237)
            ·
              refine ⟨7918456933490780520131339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21115885155975414720350237 7918456933490780520131339)
              ·
                refine ⟨11877685400236170780197009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7918456933490780520131339 11877685400236170780197009)
                ·
                  refine ⟨8908264050177128085147757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11877685400236170780197009 8908264050177128085147757)
                  ·
                    refine ⟨3340599018816423031930409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8908264050177128085147757 3340599018816423031930409)
                    ·
                      refine ⟨2505449264112317273947807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340599018816423031930409 2505449264112317273947807)
                      ·
                        rfl

theorem cell23_4879345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_4879345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879345 prefixEnd_4879345 := by exact prefixLift 4879345
  have htrace : WordTrace (prefixWord ++ tailWord_4879345) baseStart_4879345 baseEnd_4879345 := by
    simpa [prefixWord, tailWord_4879345, baseEnd_4879345] using wordTrace_append hprefix tailTrace_4879345
  have hstable : (prefixWord ++ tailWord_4879345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879345).length < 2 ^ (prefixWord ++ tailWord_4879345).sum := by decide
  have hdescent : baseEnd_4879345 < baseStart_4879345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879368 : List Nat := [2, 1, 3, 2, 1, 4, 1, 1, 4, 4]
def baseStart_4879368 : Nat := 118140960795 + 4879368 * 2 ^ 59
def prefixEnd_4879368 : Nat := 4983230072969 + 3 ^ 40 * 4879368 * 2
def baseEnd_4879368 : Nat := 835153691389123561320067

theorem tailTrace_4879368 : CollatzResearch.WordTrace tailWord_4879368 prefixEnd_4879368 835153691389123561320067 := by
  unfold tailWord_4879368
  simp only [CollatzResearch.WordTrace]
  refine ⟨88982585693445270277371379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118643447591260360369828505 88982585693445270277371379)
  ·
    refine ⟨133473878540167905416057069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88982585693445270277371379 133473878540167905416057069)
    ·
      refine ⟨50052704452562964531021401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133473878540167905416057069 50052704452562964531021401)
      ·
        refine ⟨37539528339422223398266051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50052704452562964531021401 37539528339422223398266051)
        ·
          refine ⟨56309292509133335097399077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37539528339422223398266051 56309292509133335097399077)
          ·
            refine ⟨10557992345462500330762327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56309292509133335097399077 10557992345462500330762327)
            ·
              refine ⟨15836988518193750496143491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10557992345462500330762327 15836988518193750496143491)
              ·
                refine ⟨23755482777290625744215237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15836988518193750496143491 23755482777290625744215237)
                ·
                  refine ⟨4454153020741992327040357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23755482777290625744215237 4454153020741992327040357)
                  ·
                    refine ⟨835153691389123561320067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4454153020741992327040357 835153691389123561320067)
                    ·
                      rfl

theorem cell23_4879368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_4879368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879368 prefixEnd_4879368 := by exact prefixLift 4879368
  have htrace : WordTrace (prefixWord ++ tailWord_4879368) baseStart_4879368 baseEnd_4879368 := by
    simpa [prefixWord, tailWord_4879368, baseEnd_4879368] using wordTrace_append hprefix tailTrace_4879368
  have hstable : (prefixWord ++ tailWord_4879368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879368).length < 2 ^ (prefixWord ++ tailWord_4879368).sum := by decide
  have hdescent : baseEnd_4879368 < baseStart_4879368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879388 : List Nat := [2, 2, 3, 1, 4, 1, 1, 1, 1, 1, 6]
def baseStart_4879388 : Nat := 118140960795 + 4879388 * 2 ^ 59
def prefixEnd_4879388 : Nat := 4983230072969 + 3 ^ 40 * 4879388 * 2
def baseEnd_4879388 : Nat := 2505471343780460605710109

theorem tailTrace_4879388 : CollatzResearch.WordTrace tailWord_4879388 prefixEnd_4879388 2505471343780460605710109 := by
  unfold tailWord_4879388
  simp only [CollatzResearch.WordTrace]
  refine ⟨88982950423409041985235409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118643933897878722646980545 88982950423409041985235409)
  ·
    refine ⟨66737212817556781488926557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88982950423409041985235409 66737212817556781488926557)
    ·
      refine ⟨25026454806583793058347459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 66737212817556781488926557 25026454806583793058347459)
      ·
        refine ⟨37539682209875689587521189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25026454806583793058347459 37539682209875689587521189)
        ·
          refine ⟨7038690414351691797660223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37539682209875689587521189 7038690414351691797660223)
          ·
            refine ⟨10558035621527537696490335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7038690414351691797660223 10558035621527537696490335)
            ·
              refine ⟨15837053432291306544735503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10558035621527537696490335 15837053432291306544735503)
              ·
                refine ⟨23755580148436959817103255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15837053432291306544735503 23755580148436959817103255)
                ·
                  refine ⟨35633370222655439725654883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23755580148436959817103255 35633370222655439725654883)
                  ·
                    refine ⟨53450055333983159588482325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35633370222655439725654883 53450055333983159588482325)
                    ·
                      refine ⟨2505471343780460605710109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53450055333983159588482325 2505471343780460605710109)
                      ·
                        rfl

theorem cell23_4879388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_4879388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879388 prefixEnd_4879388 := by exact prefixLift 4879388
  have htrace : WordTrace (prefixWord ++ tailWord_4879388) baseStart_4879388 baseEnd_4879388 := by
    simpa [prefixWord, tailWord_4879388, baseEnd_4879388] using wordTrace_append hprefix tailTrace_4879388
  have hstable : (prefixWord ++ tailWord_4879388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879388).length < 2 ^ (prefixWord ++ tailWord_4879388).sum := by decide
  have hdescent : baseEnd_4879388 < baseStart_4879388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879392 : List Nat := [2, 1, 1, 7, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4879392 : Nat := 118140960795 + 4879392 * 2 ^ 59
def prefixEnd_4879392 : Nat := 4983230072969 + 3 ^ 40 * 4879392 * 2
def baseEnd_4879392 : Nat := 2505473397703078590060091

theorem tailTrace_4879392 : CollatzResearch.WordTrace tailWord_4879392 prefixEnd_4879392 2505473397703078590060091 := by
  unfold tailWord_4879392
  simp only [CollatzResearch.WordTrace]
  refine ⟨88983023369401796326808215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118644031159202395102410953 88983023369401796326808215)
  ·
    refine ⟨133474535054102694490212323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88983023369401796326808215 133474535054102694490212323)
    ·
      refine ⟨200211802581154041735318485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133474535054102694490212323 200211802581154041735318485)
      ·
        refine ⟨4692464122995797853171527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 200211802581154041735318485 4692464122995797853171527)
        ·
          refine ⟨7038696184493696779757291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4692464122995797853171527 7038696184493696779757291)
          ·
            refine ⟨10558044276740545169635937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7038696184493696779757291 10558044276740545169635937)
            ·
              refine ⟨7918533207555408877226953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10558044276740545169635937 7918533207555408877226953)
              ·
                refine ⟨5938899905666556657920215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7918533207555408877226953 5938899905666556657920215)
                ·
                  refine ⟨8908349858499834986880323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5938899905666556657920215 8908349858499834986880323)
                  ·
                    refine ⟨13362524787749752480320485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8908349858499834986880323 13362524787749752480320485)
                    ·
                      refine ⟨2505473397703078590060091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13362524787749752480320485 2505473397703078590060091)
                      ·
                        rfl

theorem cell23_4879392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4879392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879392 prefixEnd_4879392 := by exact prefixLift 4879392
  have htrace : WordTrace (prefixWord ++ tailWord_4879392) baseStart_4879392 baseEnd_4879392 := by
    simpa [prefixWord, tailWord_4879392, baseEnd_4879392] using wordTrace_append hprefix tailTrace_4879392
  have hstable : (prefixWord ++ tailWord_4879392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879392).length < 2 ^ (prefixWord ++ tailWord_4879392).sum := by decide
  have hdescent : baseEnd_4879392 < baseStart_4879392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879395 : List Nat := [1, 1, 1, 4, 3, 3, 2, 2, 1, 2, 3]
def baseStart_4879395 : Nat := 118140960795 + 4879395 * 2 ^ 59
def prefixEnd_4879395 : Nat := 4983230072969 + 3 ^ 40 * 4879395 * 2
def baseEnd_4879395 : Nat := 2505474938145042078322577

theorem tailTrace_4879395 : CollatzResearch.WordTrace tailWord_4879395 prefixEnd_4879395 2505474938145042078322577 := by
  unfold tailWord_4879395
  simp only [CollatzResearch.WordTrace]
  refine ⟨177966156157792724165975639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118644104105195149443983759 177966156157792724165975639)
  ·
    refine ⟨266949234236689086248963459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177966156157792724165975639 266949234236689086248963459)
    ·
      refine ⟨400423851355033629373445189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266949234236689086248963459 400423851355033629373445189)
      ·
        refine ⟨75079472129068805507520973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 400423851355033629373445189 75079472129068805507520973)
        ·
          refine ⟨28154802048400802065320365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75079472129068805507520973 28154802048400802065320365)
          ·
            refine ⟨10558050768150300774495137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28154802048400802065320365 10558050768150300774495137)
            ·
              refine ⟨7918538076112725580871353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10558050768150300774495137 7918538076112725580871353)
              ·
                refine ⟨5938903557084544185653515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7918538076112725580871353 5938903557084544185653515)
                ·
                  refine ⟨8908355335626816278480273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5938903557084544185653515 8908355335626816278480273)
                  ·
                    refine ⟨6681266501720112208860205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8908355335626816278480273 6681266501720112208860205)
                    ·
                      refine ⟨2505474938145042078322577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6681266501720112208860205 2505474938145042078322577)
                      ·
                        rfl

theorem cell23_4879395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 2, 3].length) (baseStart_4879395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879395 prefixEnd_4879395 := by exact prefixLift 4879395
  have htrace : WordTrace (prefixWord ++ tailWord_4879395) baseStart_4879395 baseEnd_4879395 := by
    simpa [prefixWord, tailWord_4879395, baseEnd_4879395] using wordTrace_append hprefix tailTrace_4879395
  have hstable : (prefixWord ++ tailWord_4879395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879395).length < 2 ^ (prefixWord ++ tailWord_4879395).sum := by decide
  have hdescent : baseEnd_4879395 < baseStart_4879395 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879408 : List Nat := [2, 1, 1, 1, 2, 4, 1, 1, 6, 1, 3]
def baseStart_4879408 : Nat := 118140960795 + 4879408 * 2 ^ 59
def prefixEnd_4879408 : Nat := 4983230072969 + 3 ^ 40 * 4879408 * 2
def baseEnd_4879408 : Nat := 2505481613393550527460017

theorem tailTrace_4879408 : CollatzResearch.WordTrace tailWord_4879408 prefixEnd_4879408 2505481613393550527460017 := by
  unfold tailWord_4879408
  simp only [CollatzResearch.WordTrace]
  refine ⟨88983315153372813693099439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118644420204497084924132585 88983315153372813693099439)
  ·
    refine ⟨133474972730059220539649159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88983315153372813693099439 133474972730059220539649159)
    ·
      refine ⟨200212459095088830809473739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133474972730059220539649159 200212459095088830809473739)
      ·
        refine ⟨300318688642633246214210609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200212459095088830809473739 300318688642633246214210609)
        ·
          refine ⟨225239016481974934660657957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 300318688642633246214210609 225239016481974934660657957)
          ·
            refine ⟨42232315590370300248873367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 225239016481974934660657957 42232315590370300248873367)
            ·
              refine ⟨63348473385555450373310051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42232315590370300248873367 63348473385555450373310051)
              ·
                refine ⟨95022710078333175559965077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63348473385555450373310051 95022710078333175559965077)
                ·
                  refine ⟨4454189534921867604373363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95022710078333175559965077 4454189534921867604373363)
                  ·
                    refine ⟨6681284302382801406560045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4454189534921867604373363 6681284302382801406560045)
                    ·
                      refine ⟨2505481613393550527460017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6681284302382801406560045 2505481613393550527460017)
                      ·
                        rfl

theorem cell23_4879408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 1, 6, 1, 3].length) (baseStart_4879408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879408 prefixEnd_4879408 := by exact prefixLift 4879408
  have htrace : WordTrace (prefixWord ++ tailWord_4879408) baseStart_4879408 baseEnd_4879408 := by
    simpa [prefixWord, tailWord_4879408, baseEnd_4879408] using wordTrace_append hprefix tailTrace_4879408
  have hstable : (prefixWord ++ tailWord_4879408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879408).length < 2 ^ (prefixWord ++ tailWord_4879408).sum := by decide
  have hdescent : baseEnd_4879408 < baseStart_4879408 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879412 : List Nat := [2, 5, 1, 2, 1, 1, 2, 3, 1, 2, 3]
def baseStart_4879412 : Nat := 118140960795 + 4879412 * 2 ^ 59
def prefixEnd_4879412 : Nat := 4983230072969 + 3 ^ 40 * 4879412 * 2
def baseEnd_4879412 : Nat := 2505483667316168511809999

theorem tailTrace_4879412 : CollatzResearch.WordTrace tailWord_4879412 prefixEnd_4879412 2505483667316168511809999 := by
  unfold tailWord_4879412
  simp only [CollatzResearch.WordTrace]
  refine ⟨88983388099365568034672245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118644517465820757379562993 88983388099365568034672245)
  ·
    refine ⟨8342192634315522003250523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88983388099365568034672245 8342192634315522003250523)
    ·
      refine ⟨12513288951473283004875785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8342192634315522003250523 12513288951473283004875785)
      ·
        refine ⟨9384966713604962253656839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12513288951473283004875785 9384966713604962253656839)
        ·
          refine ⟨14077450070407443380485259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9384966713604962253656839 14077450070407443380485259)
          ·
            refine ⟨21116175105611165070727889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14077450070407443380485259 21116175105611165070727889)
            ·
              refine ⟨15837131329208373803045917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21116175105611165070727889 15837131329208373803045917)
              ·
                refine ⟨5938924248453140176142219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15837131329208373803045917 5938924248453140176142219)
                ·
                  refine ⟨8908386372679710264213329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5938924248453140176142219 8908386372679710264213329)
                  ·
                    refine ⟨6681289779509782698159997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8908386372679710264213329 6681289779509782698159997)
                    ·
                      refine ⟨2505483667316168511809999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6681289779509782698159997 2505483667316168511809999)
                      ·
                        rfl

theorem cell23_4879412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_4879412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879412 prefixEnd_4879412 := by exact prefixLift 4879412
  have htrace : WordTrace (prefixWord ++ tailWord_4879412) baseStart_4879412 baseEnd_4879412 := by
    simpa [prefixWord, tailWord_4879412, baseEnd_4879412] using wordTrace_append hprefix tailTrace_4879412
  have hstable : (prefixWord ++ tailWord_4879412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879412).length < 2 ^ (prefixWord ++ tailWord_4879412).sum := by decide
  have hdescent : baseEnd_4879412 < baseStart_4879412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879441 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 2, 6]
def baseStart_4879441 : Nat := 118140960795 + 4879441 * 2 ^ 59
def prefixEnd_4879441 : Nat := 4983230072969 + 3 ^ 40 * 4879441 * 2
def baseEnd_4879441 : Nat := 835166186085049632782455

theorem tailTrace_4879441 : CollatzResearch.WordTrace tailWord_4879441 prefixEnd_4879441 835166186085049632782455 := by
  unfold tailWord_4879441
  simp only [CollatzResearch.WordTrace]
  refine ⟨177967833915626074022150177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118645222610417382681433451 177967833915626074022150177)
  ·
    refine ⟨133475875436719555516612633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177967833915626074022150177 133475875436719555516612633)
    ·
      refine ⟨100106906577539666637459475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133475875436719555516612633 100106906577539666637459475)
      ·
        refine ⟨150160359866309499956189213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100106906577539666637459475 150160359866309499956189213)
        ·
          refine ⟨56310134949866062483570955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150160359866309499956189213 56310134949866062483570955)
          ·
            refine ⟨84465202424799093725356433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56310134949866062483570955 84465202424799093725356433)
            ·
              refine ⟨63348901818599320294017325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84465202424799093725356433 63348901818599320294017325)
              ·
                refine ⟨23755838181974745110256497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63348901818599320294017325 23755838181974745110256497)
                ·
                  refine ⟨17816878636481058832692373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23755838181974745110256497 17816878636481058832692373)
                  ·
                    refine ⟨835166186085049632782455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17816878636481058832692373 835166186085049632782455)
                    ·
                      rfl

theorem cell23_4879441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 6].length) (baseStart_4879441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879441 prefixEnd_4879441 := by exact prefixLift 4879441
  have htrace : WordTrace (prefixWord ++ tailWord_4879441) baseStart_4879441 baseEnd_4879441 := by
    simpa [prefixWord, tailWord_4879441, baseEnd_4879441] using wordTrace_append hprefix tailTrace_4879441
  have hstable : (prefixWord ++ tailWord_4879441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879441).length < 2 ^ (prefixWord ++ tailWord_4879441).sum := by decide
  have hdescent : baseEnd_4879441 < baseStart_4879441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879442 : List Nat := [3, 2, 2, 1, 3, 2, 1, 3, 2, 1, 3]
def baseStart_4879442 : Nat := 118140960795 + 4879442 * 2 ^ 59
def prefixEnd_4879442 : Nat := 4983230072969 + 3 ^ 40 * 4879442 * 2
def baseEnd_4879442 : Nat := 2505499071735803394434861

theorem tailTrace_4879442 : CollatzResearch.WordTrace tailWord_4879442 prefixEnd_4879442 2505499071735803394434861 := by
  unfold tailWord_4879442
  simp only [CollatzResearch.WordTrace]
  refine ⟨44491967597155612798234145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118645246925748300795291053 44491967597155612798234145)
  ·
    refine ⟨33368975697866709598675609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44491967597155612798234145 33368975697866709598675609)
    ·
      refine ⟨25026731773400032199006707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33368975697866709598675609 25026731773400032199006707)
      ·
        refine ⟨37540097660100048298510061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25026731773400032199006707 37540097660100048298510061)
        ·
          refine ⟨14077536622537518111941273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37540097660100048298510061 14077536622537518111941273)
          ·
            refine ⟨10558152466903138583955955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14077536622537518111941273 10558152466903138583955955)
            ·
              refine ⟨15837228700354707875933933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10558152466903138583955955 15837228700354707875933933)
              ·
                refine ⟨5938960762633015453475225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15837228700354707875933933 5938960762633015453475225)
                ·
                  refine ⟨4454220571974761590106419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5938960762633015453475225 4454220571974761590106419)
                  ·
                    refine ⟨6681330857962142385159629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4454220571974761590106419 6681330857962142385159629)
                    ·
                      refine ⟨2505499071735803394434861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6681330857962142385159629 2505499071735803394434861)
                      ·
                        rfl

theorem cell23_4879442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_4879442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879442 prefixEnd_4879442 := by exact prefixLift 4879442
  have htrace : WordTrace (prefixWord ++ tailWord_4879442) baseStart_4879442 baseEnd_4879442 := by
    simpa [prefixWord, tailWord_4879442, baseEnd_4879442] using wordTrace_append hprefix tailTrace_4879442
  have hstable : (prefixWord ++ tailWord_4879442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879442).length < 2 ^ (prefixWord ++ tailWord_4879442).sum := by decide
  have hdescent : baseEnd_4879442 < baseStart_4879442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879446 : List Nat := [5, 2, 2, 1, 2, 2, 1, 2, 1, 2, 3]
def baseStart_4879446 : Nat := 118140960795 + 4879446 * 2 ^ 59
def prefixEnd_4879446 : Nat := 4983230072969 + 3 ^ 40 * 4879446 * 2
def baseEnd_4879446 : Nat := 2505501125658421378784843

theorem tailTrace_4879446 : CollatzResearch.WordTrace tailWord_4879446 prefixEnd_4879446 2505501125658421378784843 := by
  unfold tailWord_4879446
  simp only [CollatzResearch.WordTrace]
  refine ⟨11123001017537997492255137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 118645344187071973250721461 11123001017537997492255137)
  ·
    refine ⟨8342250763153498119191353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11123001017537997492255137 8342250763153498119191353)
    ·
      refine ⟨6256688072365123589393515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8342250763153498119191353 6256688072365123589393515)
      ·
        refine ⟨9385032108547685384090273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6256688072365123589393515 9385032108547685384090273)
        ·
          refine ⟨7038774081410764038067705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9385032108547685384090273 7038774081410764038067705)
          ·
            refine ⟨5279080561058073028550779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7038774081410764038067705 5279080561058073028550779)
            ·
              refine ⟨7918620841587109542826169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5279080561058073028550779 7918620841587109542826169)
              ·
                refine ⟨5938965631190332157119627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7918620841587109542826169 5938965631190332157119627)
                ·
                  refine ⟨8908448446785498235679441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5938965631190332157119627 8908448446785498235679441)
                  ·
                    refine ⟨6681336335089123676759581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8908448446785498235679441 6681336335089123676759581)
                    ·
                      refine ⟨2505501125658421378784843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6681336335089123676759581 2505501125658421378784843)
                      ·
                        rfl

theorem cell23_4879446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_4879446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879446 prefixEnd_4879446 := by exact prefixLift 4879446
  have htrace : WordTrace (prefixWord ++ tailWord_4879446) baseStart_4879446 baseEnd_4879446 := by
    simpa [prefixWord, tailWord_4879446, baseEnd_4879446] using wordTrace_append hprefix tailTrace_4879446
  have hstable : (prefixWord ++ tailWord_4879446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879446).length < 2 ^ (prefixWord ++ tailWord_4879446).sum := by decide
  have hdescent : baseEnd_4879446 < baseStart_4879446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879465 : List Nat := [1, 2, 1, 1, 1, 7, 1, 2, 1, 4, 2]
def baseStart_4879465 : Nat := 118140960795 + 4879465 * 2 ^ 59
def prefixEnd_4879465 : Nat := 4983230072969 + 3 ^ 40 * 4879465 * 2
def baseEnd_4879465 : Nat := 2505510881790856804447255

theorem tailTrace_4879465 : CollatzResearch.WordTrace tailWord_4879465 prefixEnd_4879465 2505510881790856804447255 := by
  unfold tailWord_4879465
  simp only [CollatzResearch.WordTrace]
  refine ⟨177968709267539126121023849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118645806178359417414015899 177968709267539126121023849)
  ·
    refine ⟨133476531950654344590767887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177968709267539126121023849 133476531950654344590767887)
    ·
      refine ⟨200214797925981516886151831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133476531950654344590767887 200214797925981516886151831)
      ·
        refine ⟨300322196888972275329227747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200214797925981516886151831 300322196888972275329227747)
        ·
          refine ⟨450483295333458412993841621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300322196888972275329227747 450483295333458412993841621)
          ·
            refine ⟨10558202234377931554543163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 450483295333458412993841621 10558202234377931554543163)
            ·
              refine ⟨15837303351566897331814745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10558202234377931554543163 15837303351566897331814745)
              ·
                refine ⟨11877977513675172998861059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15837303351566897331814745 11877977513675172998861059)
                ·
                  refine ⟨17816966270512759498291589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11877977513675172998861059 17816966270512759498291589)
                  ·
                    refine ⟨3340681175721142405929673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17816966270512759498291589 3340681175721142405929673)
                    ·
                      refine ⟨2505510881790856804447255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340681175721142405929673 2505510881790856804447255)
                      ·
                        rfl

theorem cell23_4879465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 1, 2, 1, 4, 2].length) (baseStart_4879465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879465 prefixEnd_4879465 := by exact prefixLift 4879465
  have htrace : WordTrace (prefixWord ++ tailWord_4879465) baseStart_4879465 baseEnd_4879465 := by
    simpa [prefixWord, tailWord_4879465, baseEnd_4879465] using wordTrace_append hprefix tailTrace_4879465
  have hstable : (prefixWord ++ tailWord_4879465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879465).length < 2 ^ (prefixWord ++ tailWord_4879465).sum := by decide
  have hdescent : baseEnd_4879465 < baseStart_4879465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879469 : List Nat := [1, 5, 1, 1, 2, 3, 3, 1, 1, 3, 2]
def baseStart_4879469 : Nat := 118140960795 + 4879469 * 2 ^ 59
def prefixEnd_4879469 : Nat := 4983230072969 + 3 ^ 40 * 4879469 * 2
def baseEnd_4879469 : Nat := 2505512935713474788797237

theorem tailTrace_4879469 : CollatzResearch.WordTrace tailWord_4879469 prefixEnd_4879469 2505512935713474788797237 := by
  unfold tailWord_4879469
  simp only [CollatzResearch.WordTrace]
  refine ⟨177968855159524634804169461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118645903439683089869446307 177968855159524634804169461)
  ·
    refine ⟨16684580171205434512890887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177968855159524634804169461 16684580171205434512890887)
    ·
      refine ⟨25026870256808151769336331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16684580171205434512890887 25026870256808151769336331)
      ·
        refine ⟨37540305385212227654004497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25026870256808151769336331 37540305385212227654004497)
        ·
          refine ⟨28155229038909170740503373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37540305385212227654004497 28155229038909170740503373)
          ·
            refine ⟨10558210889590939027688765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28155229038909170740503373 10558210889590939027688765)
            ·
              refine ⟨3959329083596602135383287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10558210889590939027688765 3959329083596602135383287)
              ·
                refine ⟨5938993625394903203074931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3959329083596602135383287 5938993625394903203074931)
                ·
                  refine ⟨8908490438092354804612397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5938993625394903203074931 8908490438092354804612397)
                  ·
                    refine ⟨3340683914284633051729649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8908490438092354804612397 3340683914284633051729649)
                    ·
                      refine ⟨2505512935713474788797237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340683914284633051729649 2505512935713474788797237)
                      ·
                        rfl

theorem cell23_4879469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_4879469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879469 prefixEnd_4879469 := by exact prefixLift 4879469
  have htrace : WordTrace (prefixWord ++ tailWord_4879469) baseStart_4879469 baseEnd_4879469 := by
    simpa [prefixWord, tailWord_4879469, baseEnd_4879469] using wordTrace_append hprefix tailTrace_4879469
  have hstable : (prefixWord ++ tailWord_4879469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879469).length < 2 ^ (prefixWord ++ tailWord_4879469).sum := by decide
  have hdescent : baseEnd_4879469 < baseStart_4879469 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879533 : List Nat := [1, 5, 2, 1, 4, 1, 1, 2, 2, 2, 2]
def baseStart_4879533 : Nat := 118140960795 + 4879533 * 2 ^ 59
def prefixEnd_4879533 : Nat := 4983230072969 + 3 ^ 40 * 4879533 * 2
def baseEnd_4879533 : Nat := 2505545798475362538396943

theorem tailTrace_4879533 : CollatzResearch.WordTrace tailWord_4879533 prefixEnd_4879533 2505545798475362538396943 := by
  unfold tailWord_4879533
  simp only [CollatzResearch.WordTrace]
  refine ⟨177971189431292773734499253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118647459620861849156332835 177971189431292773734499253)
  ·
    refine ⟨16684799009183697537609305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 177971189431292773734499253 16684799009183697537609305)
    ·
      refine ⟨12513599256887773153206979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16684799009183697537609305 12513599256887773153206979)
      ·
        refine ⟨18770398885331659729810469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12513599256887773153206979 18770398885331659729810469)
        ·
          refine ⟨3519449790999686199339463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18770398885331659729810469 3519449790999686199339463)
          ·
            refine ⟨5279174686499529299009195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3519449790999686199339463 5279174686499529299009195)
            ·
              refine ⟨7918762029749293948513793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5279174686499529299009195 7918762029749293948513793)
              ·
                refine ⟨5939071522311970461385345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7918762029749293948513793 5939071522311970461385345)
                ·
                  refine ⟨4454303641733977846039009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5939071522311970461385345 4454303641733977846039009)
                  ·
                    refine ⟨3340727731300483384529257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4454303641733977846039009 3340727731300483384529257)
                    ·
                      refine ⟨2505545798475362538396943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340727731300483384529257 2505545798475362538396943)
                      ·
                        rfl

theorem cell23_4879533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_4879533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879533 prefixEnd_4879533 := by exact prefixLift 4879533
  have htrace : WordTrace (prefixWord ++ tailWord_4879533) baseStart_4879533 baseEnd_4879533 := by
    simpa [prefixWord, tailWord_4879533, baseEnd_4879533] using wordTrace_append hprefix tailTrace_4879533
  have hstable : (prefixWord ++ tailWord_4879533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879533).length < 2 ^ (prefixWord ++ tailWord_4879533).sum := by decide
  have hdescent : baseEnd_4879533 < baseStart_4879533 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879598 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_4879598 : Nat := 118140960795 + 4879598 * 2 ^ 59
def prefixEnd_4879598 : Nat := 4983230072969 + 3 ^ 40 * 4879598 * 2
def baseEnd_4879598 : Nat := 2505579174717904784084143

theorem tailTrace_4879598 : CollatzResearch.WordTrace tailWord_4879598 prefixEnd_4879598 2505579174717904784084143 := by
  unfold tailWord_4879598
  simp only [CollatzResearch.WordTrace]
  refine ⟨22246695022007161229451931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118649040117371526557076965 22246695022007161229451931)
  ·
    refine ⟨33370042533010741844177897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22246695022007161229451931 33370042533010741844177897)
    ·
      refine ⟨25027531899758056383133423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33370042533010741844177897 25027531899758056383133423)
      ·
        refine ⟨37541297849637084574700135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25027531899758056383133423 37541297849637084574700135)
        ·
          refine ⟨56311946774455626862050203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37541297849637084574700135 56311946774455626862050203)
          ·
            refine ⟨84467920161683440293075305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56311946774455626862050203 84467920161683440293075305)
            ·
              refine ⟨63350940121262580219806479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84467920161683440293075305 63350940121262580219806479)
              ·
                refine ⟨95026410181893870329709719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63350940121262580219806479 95026410181893870329709719)
                ·
                  refine ⟨142539615272840805494564579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95026410181893870329709719 142539615272840805494564579)
                  ·
                    refine ⟨213809422909261208241846869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 142539615272840805494564579 213809422909261208241846869)
                    ·
                      refine ⟨2505579174717904784084143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 213809422909261208241846869 2505579174717904784084143)
                      ·
                        rfl

theorem cell23_4879598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_4879598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879598 prefixEnd_4879598 := by exact prefixLift 4879598
  have htrace : WordTrace (prefixWord ++ tailWord_4879598) baseStart_4879598 baseEnd_4879598 := by
    simpa [prefixWord, tailWord_4879598, baseEnd_4879598] using wordTrace_append hprefix tailTrace_4879598
  have hstable : (prefixWord ++ tailWord_4879598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879598).length < 2 ^ (prefixWord ++ tailWord_4879598).sum := by decide
  have hdescent : baseEnd_4879598 < baseStart_4879598 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879599 : List Nat := [1, 1, 2, 1, 8, 1, 1, 1, 3, 4]
def baseStart_4879599 : Nat := 118140960795 + 4879599 * 2 ^ 59
def prefixEnd_4879599 : Nat := 4983230072969 + 3 ^ 40 * 4879599 * 2
def baseEnd_4879599 : Nat := 835193229399519760057213

theorem tailTrace_4879599 : CollatzResearch.WordTrace tailWord_4879599 prefixEnd_4879599 835193229399519760057213 := by
  unfold tailWord_4879599
  simp only [CollatzResearch.WordTrace]
  refine ⟨177973596649053667006401851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118649064432702444670934567 177973596649053667006401851)
  ·
    refine ⟨266960394973580500509602777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177973596649053667006401851 266960394973580500509602777)
    ·
      refine ⟨200220296230185375382202083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266960394973580500509602777 200220296230185375382202083)
      ·
        refine ⟨300330444345278063073303125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200220296230185375382202083 300330444345278063073303125)
        ·
          refine ⟨3519497394671227301640271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 300330444345278063073303125 3519497394671227301640271)
          ·
            refine ⟨5279246092006840952460407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3519497394671227301640271 5279246092006840952460407)
            ·
              refine ⟨7918869138010261428690611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5279246092006840952460407 7918869138010261428690611)
              ·
                refine ⟨11878303707015392143035917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7918869138010261428690611 11878303707015392143035917)
                ·
                  refine ⟨4454363890130772053638469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11878303707015392143035917 4454363890130772053638469)
                  ·
                    refine ⟨835193229399519760057213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4454363890130772053638469 835193229399519760057213)
                    ·
                      rfl

theorem cell23_4879599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 1, 3, 4].length) (baseStart_4879599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879599 prefixEnd_4879599 := by exact prefixLift 4879599
  have htrace : WordTrace (prefixWord ++ tailWord_4879599) baseStart_4879599 baseEnd_4879599 := by
    simpa [prefixWord, tailWord_4879599, baseEnd_4879599] using wordTrace_append hprefix tailTrace_4879599
  have hstable : (prefixWord ++ tailWord_4879599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879599).length < 2 ^ (prefixWord ++ tailWord_4879599).sum := by decide
  have hdescent : baseEnd_4879599 < baseStart_4879599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879639 : List Nat := [1, 1, 3, 4, 1, 1, 2, 5, 1, 1, 3]
def baseStart_4879639 : Nat := 118140960795 + 4879639 * 2 ^ 59
def prefixEnd_4879639 : Nat := 4983230072969 + 3 ^ 40 * 4879639 * 2
def baseEnd_4879639 : Nat := 2505600227424739123671455

theorem tailTrace_4879639 : CollatzResearch.WordTrace tailWord_4879639 prefixEnd_4879639 2505600227424739123671455 := by
  unfold tailWord_4879639
  simp only [CollatzResearch.WordTrace]
  refine ⟨177975055568908753837857971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118650037045939169225238647 177975055568908753837857971)
  ·
    refine ⟨266962583353363130756786957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177975055568908753837857971 266962583353363130756786957)
    ·
      refine ⟨100110968757511174033795109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 266962583353363130756786957 100110968757511174033795109)
      ·
        refine ⟨18770806642033345131336583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100110968757511174033795109 18770806642033345131336583)
        ·
          refine ⟨28156209963050017697004875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18770806642033345131336583 28156209963050017697004875)
          ·
            refine ⟨42234314944575026545507313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28156209963050017697004875 42234314944575026545507313)
            ·
              refine ⟨31675736208431269909130485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42234314944575026545507313 31675736208431269909130485)
              ·
                refine ⟨2969600269540431553980983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31675736208431269909130485 2969600269540431553980983)
                ·
                  refine ⟨4454400404310647330971475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969600269540431553980983 4454400404310647330971475)
                  ·
                    refine ⟨6681600606465970996457213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4454400404310647330971475 6681600606465970996457213)
                    ·
                      refine ⟨2505600227424739123671455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6681600606465970996457213 2505600227424739123671455)
                      ·
                        rfl

theorem cell23_4879639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_4879639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879639 prefixEnd_4879639 := by exact prefixLift 4879639
  have htrace : WordTrace (prefixWord ++ tailWord_4879639) baseStart_4879639 baseEnd_4879639 := by
    simpa [prefixWord, tailWord_4879639, baseEnd_4879639] using wordTrace_append hprefix tailTrace_4879639
  have hstable : (prefixWord ++ tailWord_4879639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879639).length < 2 ^ (prefixWord ++ tailWord_4879639).sum := by decide
  have hdescent : baseEnd_4879639 < baseStart_4879639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879656 : List Nat := [2, 1, 5, 1, 2, 2, 1, 4, 1, 1, 3]
def baseStart_4879656 : Nat := 118140960795 + 4879656 * 2 ^ 59
def prefixEnd_4879656 : Nat := 4983230072969 + 3 ^ 40 * 4879656 * 2
def baseEnd_4879656 : Nat := 2505608956595865557158877

theorem tailTrace_4879656 : CollatzResearch.WordTrace tailWord_4879656 prefixEnd_4879656 2505608956595865557158877 := by
  unfold tailWord_4879656
  simp only [CollatzResearch.WordTrace]
  refine ⟨88987837804923582870613411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118650450406564777160817881 88987837804923582870613411)
  ·
    refine ⟨133481756707385374305920117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88987837804923582870613411 133481756707385374305920117)
    ·
      refine ⟨12513914691317378841180011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 133481756707385374305920117 12513914691317378841180011)
      ·
        refine ⟨18770872036976068261770017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12513914691317378841180011 18770872036976068261770017)
        ·
          refine ⟨14078154027732051196327513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18770872036976068261770017 14078154027732051196327513)
          ·
            refine ⟨10558615520799038397245635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14078154027732051196327513 10558615520799038397245635)
            ·
              refine ⟨15837923281198557595868453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10558615520799038397245635 15837923281198557595868453)
              ·
                refine ⟨2969610615224729549225335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15837923281198557595868453 2969610615224729549225335)
                ·
                  refine ⟨4454415922837094323838003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969610615224729549225335 4454415922837094323838003)
                  ·
                    refine ⟨6681623884255641485757005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4454415922837094323838003 6681623884255641485757005)
                    ·
                      refine ⟨2505608956595865557158877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6681623884255641485757005 2505608956595865557158877)
                      ·
                        rfl

theorem cell23_4879656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_4879656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879656 prefixEnd_4879656 := by exact prefixLift 4879656
  have htrace : WordTrace (prefixWord ++ tailWord_4879656) baseStart_4879656 baseEnd_4879656 := by
    simpa [prefixWord, tailWord_4879656, baseEnd_4879656] using wordTrace_append hprefix tailTrace_4879656
  have hstable : (prefixWord ++ tailWord_4879656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879656).length < 2 ^ (prefixWord ++ tailWord_4879656).sum := by decide
  have hdescent : baseEnd_4879656 < baseStart_4879656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879679 : List Nat := [1, 1, 2, 2, 4, 3, 1, 2, 3, 2, 2]
def baseStart_4879679 : Nat := 118140960795 + 4879679 * 2 ^ 59
def prefixEnd_4879679 : Nat := 4983230072969 + 3 ^ 40 * 4879679 * 2
def baseEnd_4879679 : Nat := 2505620766650918967171271

theorem tailTrace_4879679 : CollatzResearch.WordTrace tailWord_4879679 prefixEnd_4879679 2505620766650918967171271 := by
  unfold tailWord_4879679
  simp only [CollatzResearch.WordTrace]
  refine ⟨177976514488763840669314091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118651009659175893779542727 177976514488763840669314091)
  ·
    refine ⟨266964771733145761003971137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177976514488763840669314091 266964771733145761003971137)
    ·
      refine ⟨200223578799859320752978353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266964771733145761003971137 200223578799859320752978353)
      ·
        refine ⟨150167684099894490564733765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200223578799859320752978353 150167684099894490564733765)
        ·
          refine ⟨28156440768730216980887581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150167684099894490564733765 28156440768730216980887581)
          ·
            refine ⟨10558665288273831367832843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28156440768730216980887581 10558665288273831367832843)
            ·
              refine ⟨15837997932410747051749265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10558665288273831367832843 15837997932410747051749265)
              ·
                refine ⟨11878498449308060288811949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15837997932410747051749265 11878498449308060288811949)
                ·
                  refine ⟨4454436918490522608304481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11878498449308060288811949 4454436918490522608304481)
                  ·
                    refine ⟨3340827688867891956228361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4454436918490522608304481 3340827688867891956228361)
                    ·
                      refine ⟨2505620766650918967171271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340827688867891956228361 2505620766650918967171271)
                      ·
                        rfl

theorem cell23_4879679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 2, 3, 2, 2].length) (baseStart_4879679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879679 prefixEnd_4879679 := by exact prefixLift 4879679
  have htrace : WordTrace (prefixWord ++ tailWord_4879679) baseStart_4879679 baseEnd_4879679 := by
    simpa [prefixWord, tailWord_4879679, baseEnd_4879679] using wordTrace_append hprefix tailTrace_4879679
  have hstable : (prefixWord ++ tailWord_4879679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879679).length < 2 ^ (prefixWord ++ tailWord_4879679).sum := by decide
  have hdescent : baseEnd_4879679 < baseStart_4879679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879693 : List Nat := [1, 6, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_4879693 : Nat := 118140960795 + 4879693 * 2 ^ 59
def prefixEnd_4879693 : Nat := 4983230072969 + 3 ^ 40 * 4879693 * 2
def baseEnd_4879693 : Nat := 835209318460027304132069

theorem tailTrace_4879693 : CollatzResearch.WordTrace tailWord_4879693 prefixEnd_4879693 835209318460027304132069 := by
  unfold tailWord_4879693
  simp only [CollatzResearch.WordTrace]
  refine ⟨177977025110713121060323733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118651350073808747373549155 177977025110713121060323733)
  ·
    refine ⟨8342673052064677549702675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 177977025110713121060323733 8342673052064677549702675)
    ·
      refine ⟨12514009578097016324554013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8342673052064677549702675 12514009578097016324554013)
      ·
        refine ⟨4692753591786381121707755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12514009578097016324554013 4692753591786381121707755)
        ·
          refine ⟨7039130387679571682561633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4692753591786381121707755 7039130387679571682561633)
          ·
            refine ⟨5279347790759678761921225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7039130387679571682561633 5279347790759678761921225)
            ·
              refine ⟨3959510843069759071440919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5279347790759678761921225 3959510843069759071440919)
              ·
                refine ⟨5939266264604638607161379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3959510843069759071440919 5939266264604638607161379)
                ·
                  refine ⟨8908899396906957910742069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5939266264604638607161379 8908899396906957910742069)
                  ·
                    refine ⟨835209318460027304132069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8908899396906957910742069 835209318460027304132069)
                    ·
                      rfl

theorem cell23_4879693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_4879693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879693 prefixEnd_4879693 := by exact prefixLift 4879693
  have htrace : WordTrace (prefixWord ++ tailWord_4879693) baseStart_4879693 baseEnd_4879693 := by
    simpa [prefixWord, tailWord_4879693, baseEnd_4879693] using wordTrace_append hprefix tailTrace_4879693
  have hstable : (prefixWord ++ tailWord_4879693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879693).length < 2 ^ (prefixWord ++ tailWord_4879693).sum := by decide
  have hdescent : baseEnd_4879693 < baseStart_4879693 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879696 : List Nat := [2, 1, 1, 1, 1, 5, 4, 3, 1, 2, 2]
def baseStart_4879696 : Nat := 118140960795 + 4879696 * 2 ^ 59
def prefixEnd_4879696 : Nat := 4983230072969 + 3 ^ 40 * 4879696 * 2
def baseEnd_4879696 : Nat := 2505629495822045400658693

theorem tailTrace_4879696 : CollatzResearch.WordTrace tailWord_4879696 prefixEnd_4879696 2505629495822045400658693 := by
  unfold tailWord_4879696
  simp only [CollatzResearch.WordTrace]
  refine ⟨88988567264851126286341471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118651423019801501715121961 88988567264851126286341471)
  ·
    refine ⟨133482850897276689429512207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88988567264851126286341471 133482850897276689429512207)
    ·
      refine ⟨200224276345915034144268311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133482850897276689429512207 200224276345915034144268311)
      ·
        refine ⟨300336414518872551216402467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200224276345915034144268311 300336414518872551216402467)
        ·
          refine ⟨450504621778308826824603701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300336414518872551216402467 450504621778308826824603701)
          ·
            refine ⟨42234808291716452514806597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 450504621778308826824603701 42234808291716452514806597)
            ·
              refine ⟨7919026554696834846526237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42234808291716452514806597 7919026554696834846526237)
              ·
                refine ⟨2969634958011313067447339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7919026554696834846526237 2969634958011313067447339)
                ·
                  refine ⟨4454452437016969601171009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969634958011313067447339 4454452437016969601171009)
                  ·
                    refine ⟨3340839327762727200878257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4454452437016969601171009 3340839327762727200878257)
                    ·
                      refine ⟨2505629495822045400658693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340839327762727200878257 2505629495822045400658693)
                      ·
                        rfl

theorem cell23_4879696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 4, 3, 1, 2, 2].length) (baseStart_4879696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879696 prefixEnd_4879696 := by exact prefixLift 4879696
  have htrace : WordTrace (prefixWord ++ tailWord_4879696) baseStart_4879696 baseEnd_4879696 := by
    simpa [prefixWord, tailWord_4879696, baseEnd_4879696] using wordTrace_append hprefix tailTrace_4879696
  have hstable : (prefixWord ++ tailWord_4879696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879696).length < 2 ^ (prefixWord ++ tailWord_4879696).sum := by decide
  have hdescent : baseEnd_4879696 < baseStart_4879696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879726 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_4879726 : Nat := 118140960795 + 4879726 * 2 ^ 59
def prefixEnd_4879726 : Nat := 4983230072969 + 3 ^ 40 * 4879726 * 2
def baseEnd_4879726 : Nat := 2505644900241680283283555

theorem tailTrace_4879726 : CollatzResearch.WordTrace tailWord_4879726 prefixEnd_4879726 2505644900241680283283555 := by
  unfold tailWord_4879726
  simp only [CollatzResearch.WordTrace]
  refine ⟨22247278589949195962034379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118652152479729045130850021 22247278589949195962034379)
  ·
    refine ⟨33370917884923793943051569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22247278589949195962034379 33370917884923793943051569)
    ·
      refine ⟨25028188413692845457288677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33370917884923793943051569 25028188413692845457288677)
      ·
        refine ⟨4692785327567408523241627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25028188413692845457288677 4692785327567408523241627)
        ·
          refine ⟨7039177991351112784862441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4692785327567408523241627 7039177991351112784862441)
          ·
            refine ⟨5279383493513334588646831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7039177991351112784862441 5279383493513334588646831)
            ·
              refine ⟨7919075240270001882970247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5279383493513334588646831 7919075240270001882970247)
              ·
                refine ⟨11878612860405002824455371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7919075240270001882970247 11878612860405002824455371)
                ·
                  refine ⟨17817919290607504236683057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11878612860405002824455371 17817919290607504236683057)
                  ·
                    refine ⟨13363439467955628177512293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17817919290607504236683057 13363439467955628177512293)
                    ·
                      refine ⟨2505644900241680283283555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13363439467955628177512293 2505644900241680283283555)
                      ·
                        rfl

theorem cell23_4879726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_4879726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879726 prefixEnd_4879726 := by exact prefixLift 4879726
  have htrace : WordTrace (prefixWord ++ tailWord_4879726) baseStart_4879726 baseEnd_4879726 := by
    simpa [prefixWord, tailWord_4879726, baseEnd_4879726] using wordTrace_append hprefix tailTrace_4879726
  have hstable : (prefixWord ++ tailWord_4879726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879726).length < 2 ^ (prefixWord ++ tailWord_4879726).sum := by decide
  have hdescent : baseEnd_4879726 < baseStart_4879726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879739 : List Nat := [1, 1, 1, 1, 1, 6, 4, 2, 1, 3, 2]
def baseStart_4879739 : Nat := 118140960795 + 4879739 * 2 ^ 59
def prefixEnd_4879739 : Nat := 4983230072969 + 3 ^ 40 * 4879739 * 2
def baseEnd_4879739 : Nat := 2505651575490188732420995

theorem tailTrace_4879739 : CollatzResearch.WordTrace tailWord_4879739 prefixEnd_4879739 2505651575490188732420995 := by
  unfold tailWord_4879739
  simp only [CollatzResearch.WordTrace]
  refine ⟨177978702868546470916498271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118652468579030980610998847 177978702868546470916498271)
  ·
    refine ⟨266968054302819706374747407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177978702868546470916498271 266968054302819706374747407)
    ·
      refine ⟨400452081454229559562121111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266968054302819706374747407 400452081454229559562121111)
      ·
        refine ⟨600678122181344339343181667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400452081454229559562121111 600678122181344339343181667)
        ·
          refine ⟨901017183272016509014772501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 600678122181344339343181667 901017183272016509014772501)
          ·
            refine ⟨42235180465875773860067461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 901017183272016509014772501 42235180465875773860067461)
            ·
              refine ⟨7919096337351707598762649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42235180465875773860067461 7919096337351707598762649)
              ·
                refine ⟨5939322253013780699071987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7919096337351707598762649 5939322253013780699071987)
                ·
                  refine ⟨8908983379520671048607981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5939322253013780699071987 8908983379520671048607981)
                  ·
                    refine ⟨3340868767320251643227993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8908983379520671048607981 3340868767320251643227993)
                    ·
                      refine ⟨2505651575490188732420995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340868767320251643227993 2505651575490188732420995)
                      ·
                        rfl

theorem cell23_4879739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 2, 1, 3, 2].length) (baseStart_4879739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879739 prefixEnd_4879739 := by exact prefixLift 4879739
  have htrace : WordTrace (prefixWord ++ tailWord_4879739) baseStart_4879739 baseEnd_4879739 := by
    simpa [prefixWord, tailWord_4879739, baseEnd_4879739] using wordTrace_append hprefix tailTrace_4879739
  have hstable : (prefixWord ++ tailWord_4879739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879739).length < 2 ^ (prefixWord ++ tailWord_4879739).sum := by decide
  have hdescent : baseEnd_4879739 < baseStart_4879739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879746 : List Nat := [3, 4, 2, 1, 1, 1, 1, 2, 4, 1, 3]
def baseStart_4879746 : Nat := 118140960795 + 4879746 * 2 ^ 59
def prefixEnd_4879746 : Nat := 4983230072969 + 3 ^ 40 * 4879746 * 2
def baseEnd_4879746 : Nat := 2505655169854770205033463

theorem tailTrace_4879746 : CollatzResearch.WordTrace tailWord_4879746 prefixEnd_4879746 2505655169854770205033463 := by
  unfold tailWord_4879746
  simp only [CollatzResearch.WordTrace]
  refine ⟨44494739544880277778000773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118652638786347407408002061 44494739544880277778000773)
  ·
    refine ⟨8342763664665052083375145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44494739544880277778000773 8342763664665052083375145)
    ·
      refine ⟨6257072748498789062531359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8342763664665052083375145 6257072748498789062531359)
      ·
        refine ⟨9385609122748183593797039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6257072748498789062531359 9385609122748183593797039)
        ·
          refine ⟨14078413684122275390695559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9385609122748183593797039 14078413684122275390695559)
          ·
            refine ⟨21117620526183413086043339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14078413684122275390695559 21117620526183413086043339)
            ·
              refine ⟨31676430789275119629065009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21117620526183413086043339 31676430789275119629065009)
              ·
                refine ⟨23757323091956339721798757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31676430789275119629065009 23757323091956339721798757)
                ·
                  refine ⟨4454498079741813697837267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23757323091956339721798757 4454498079741813697837267)
                  ·
                    refine ⟨6681747119612720546755901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4454498079741813697837267 6681747119612720546755901)
                    ·
                      refine ⟨2505655169854770205033463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6681747119612720546755901 2505655169854770205033463)
                      ·
                        rfl

theorem cell23_4879746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_4879746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879746 prefixEnd_4879746 := by exact prefixLift 4879746
  have htrace : WordTrace (prefixWord ++ tailWord_4879746) baseStart_4879746 baseEnd_4879746 := by
    simpa [prefixWord, tailWord_4879746, baseEnd_4879746] using wordTrace_append hprefix tailTrace_4879746
  have hstable : (prefixWord ++ tailWord_4879746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879746).length < 2 ^ (prefixWord ++ tailWord_4879746).sum := by decide
  have hdescent : baseEnd_4879746 < baseStart_4879746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879755 : List Nat := [1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 5]
def baseStart_4879755 : Nat := 118140960795 + 4879755 * 2 ^ 59
def prefixEnd_4879755 : Nat := 4983230072969 + 3 ^ 40 * 4879755 * 2
def baseEnd_4879755 : Nat := 2505659791180660669820921

theorem tailTrace_4879755 : CollatzResearch.WordTrace tailWord_4879755 prefixEnd_4879755 2505659791180660669820921 := by
  unfold tailWord_4879755
  simp only [CollatzResearch.WordTrace]
  refine ⟨177979286436488505649080719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118652857624325670432720479 177979286436488505649080719)
  ·
    refine ⟨266968929654732758473621079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177979286436488505649080719 266968929654732758473621079)
    ·
      refine ⟨400453394482099137710431619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 266968929654732758473621079 400453394482099137710431619)
      ·
        refine ⟨600680091723148706565647429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 400453394482099137710431619 600680091723148706565647429)
        ·
          refine ⟨112627517198090382481058893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 600680091723148706565647429 112627517198090382481058893)
          ·
            refine ⟨42235318949283893430397085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112627517198090382481058893 42235318949283893430397085)
            ·
              refine ⟨15838244605981460036398907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42235318949283893430397085 15838244605981460036398907)
              ·
                refine ⟨23757366908972190054598361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15838244605981460036398907 23757366908972190054598361)
                ·
                  refine ⟨17818025181729142540948771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23757366908972190054598361 17818025181729142540948771)
                  ·
                    refine ⟨26727037772593713811423157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17818025181729142540948771 26727037772593713811423157)
                    ·
                      refine ⟨2505659791180660669820921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26727037772593713811423157 2505659791180660669820921)
                      ·
                        rfl

theorem cell23_4879755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 5].length) (baseStart_4879755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879755 prefixEnd_4879755 := by exact prefixLift 4879755
  have htrace : WordTrace (prefixWord ++ tailWord_4879755) baseStart_4879755 baseEnd_4879755 := by
    simpa [prefixWord, tailWord_4879755, baseEnd_4879755] using wordTrace_append hprefix tailTrace_4879755
  have hstable : (prefixWord ++ tailWord_4879755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879755).length < 2 ^ (prefixWord ++ tailWord_4879755).sum := by decide
  have hdescent : baseEnd_4879755 < baseStart_4879755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879765 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 4, 2, 4]
def baseStart_4879765 : Nat := 118140960795 + 4879765 * 2 ^ 59
def prefixEnd_4879765 : Nat := 4983230072969 + 3 ^ 40 * 4879765 * 2
def baseEnd_4879765 : Nat := 2505664925987205630695875

theorem tailTrace_4879765 : CollatzResearch.WordTrace tailWord_4879765 prefixEnd_4879765 2505664925987205630695875 := by
  unfold tailWord_4879765
  simp only [CollatzResearch.WordTrace]
  refine ⟨177979651166452277356944749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118653100777634851571296499 177979651166452277356944749)
  ·
    refine ⟨66742369187419604008854281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 177979651166452277356944749 66742369187419604008854281)
    ·
      refine ⟨50056776890564703006640711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66742369187419604008854281 50056776890564703006640711)
      ·
        refine ⟨75085165335847054509961067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50056776890564703006640711 75085165335847054509961067)
        ·
          refine ⟨112627748003770581764941601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75085165335847054509961067 112627748003770581764941601)
          ·
            refine ⟨84470811002827936323706201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112627748003770581764941601 84470811002827936323706201)
            ·
              refine ⟨63353108252120952242779651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84470811002827936323706201 63353108252120952242779651)
              ·
                refine ⟨95029662378181428364169477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63353108252120952242779651 95029662378181428364169477)
                ·
                  refine ⟨17818061695909017818281777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95029662378181428364169477 17818061695909017818281777)
                  ·
                    refine ⟨13363546271931763363711333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17818061695909017818281777 13363546271931763363711333)
                    ·
                      refine ⟨2505664925987205630695875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13363546271931763363711333 2505664925987205630695875)
                      ·
                        rfl

theorem cell23_4879765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 2, 4].length) (baseStart_4879765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879765 prefixEnd_4879765 := by exact prefixLift 4879765
  have htrace : WordTrace (prefixWord ++ tailWord_4879765) baseStart_4879765 baseEnd_4879765 := by
    simpa [prefixWord, tailWord_4879765, baseEnd_4879765] using wordTrace_append hprefix tailTrace_4879765
  have hstable : (prefixWord ++ tailWord_4879765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879765).length < 2 ^ (prefixWord ++ tailWord_4879765).sum := by decide
  have hdescent : baseEnd_4879765 < baseStart_4879765 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879769 : List Nat := [1, 2, 1, 2, 1, 5, 2, 1, 4, 2, 2]
def baseStart_4879769 : Nat := 118140960795 + 4879769 * 2 ^ 59
def prefixEnd_4879769 : Nat := 4983230072969 + 3 ^ 40 * 4879769 * 2
def baseEnd_4879769 : Nat := 2505666979909823615045857

theorem tailTrace_4879769 : CollatzResearch.WordTrace tailWord_4879769 prefixEnd_4879769 2505666979909823615045857 := by
  unfold tailWord_4879769
  simp only [CollatzResearch.WordTrace]
  refine ⟨177979797058437786040090361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118653198038958524026726907 177979797058437786040090361)
  ·
    refine ⟨133484847793828339530067771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177979797058437786040090361 133484847793828339530067771)
    ·
      refine ⟨200227271690742509295101657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133484847793828339530067771 200227271690742509295101657)
      ·
        refine ⟨150170453768056881971326243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200227271690742509295101657 150170453768056881971326243)
        ·
          refine ⟨225255680652085322956989365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150170453768056881971326243 225255680652085322956989365)
          ·
            refine ⟨21117720061132999027217753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 225255680652085322956989365 21117720061132999027217753)
            ·
              refine ⟨15838290045849749270413315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21117720061132999027217753 15838290045849749270413315)
              ·
                refine ⟨23757435068774623905619973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15838290045849749270413315 23757435068774623905619973)
                ·
                  refine ⟨4454519075395241982303745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23757435068774623905619973 4454519075395241982303745)
                  ·
                    refine ⟨3340889306546431486727809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4454519075395241982303745 3340889306546431486727809)
                    ·
                      refine ⟨2505666979909823615045857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3340889306546431486727809 2505666979909823615045857)
                      ·
                        rfl

theorem cell23_4879769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 1, 4, 2, 2].length) (baseStart_4879769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879769 prefixEnd_4879769 := by exact prefixLift 4879769
  have htrace : WordTrace (prefixWord ++ tailWord_4879769) baseStart_4879769 baseEnd_4879769 := by
    simpa [prefixWord, tailWord_4879769, baseEnd_4879769] using wordTrace_append hprefix tailTrace_4879769
  have hstable : (prefixWord ++ tailWord_4879769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879769).length < 2 ^ (prefixWord ++ tailWord_4879769).sum := by decide
  have hdescent : baseEnd_4879769 < baseStart_4879769 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879815 : List Nat := [1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 5]
def baseStart_4879815 : Nat := 118140960795 + 4879815 * 2 ^ 59
def prefixEnd_4879815 : Nat := 4983230072969 + 3 ^ 40 * 4879815 * 2
def baseEnd_4879815 : Nat := 2505690600019930435070645

theorem tailTrace_4879815 : CollatzResearch.WordTrace tailWord_4879815 prefixEnd_4879815 2505690600019930435070645 := by
  unfold tailWord_4879815
  simp only [CollatzResearch.WordTrace]
  refine ⟨177981474816271135896264899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118654316544180757264176599 177981474816271135896264899)
  ·
    refine ⟨266972212224406703844397349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177981474816271135896264899 266972212224406703844397349)
    ·
      refine ⟨50057289792076256970824503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266972212224406703844397349 50057289792076256970824503)
      ·
        refine ⟨75085934688114385456236755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50057289792076256970824503 75085934688114385456236755)
        ·
          refine ⟨112628902032171578184355133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75085934688114385456236755 112628902032171578184355133)
          ·
            refine ⟨42235838262064341819133175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112628902032171578184355133 42235838262064341819133175)
            ·
              refine ⟨63353757393096512728699763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42235838262064341819133175 63353757393096512728699763)
              ·
                refine ⟨95030636089644769093049645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63353757393096512728699763 95030636089644769093049645)
                ·
                  refine ⟨35636488533616788409893617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95030636089644769093049645 35636488533616788409893617)
                  ·
                    refine ⟨26727366400212591307420213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35636488533616788409893617 26727366400212591307420213)
                    ·
                      refine ⟨2505690600019930435070645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26727366400212591307420213 2505690600019930435070645)
                      ·
                        rfl

theorem cell23_4879815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_4879815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879815 prefixEnd_4879815 := by exact prefixLift 4879815
  have htrace : WordTrace (prefixWord ++ tailWord_4879815) baseStart_4879815 baseEnd_4879815 := by
    simpa [prefixWord, tailWord_4879815, baseEnd_4879815] using wordTrace_append hprefix tailTrace_4879815
  have hstable : (prefixWord ++ tailWord_4879815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879815).length < 2 ^ (prefixWord ++ tailWord_4879815).sum := by decide
  have hdescent : baseEnd_4879815 < baseStart_4879815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879822 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 2, 5]
def baseStart_4879822 : Nat := 118140960795 + 4879822 * 2 ^ 59
def prefixEnd_4879822 : Nat := 4983230072969 + 3 ^ 40 * 4879822 * 2
def baseEnd_4879822 : Nat := 835231398128170635894371

theorem tailTrace_4879822 : CollatzResearch.WordTrace tailWord_4879822 prefixEnd_4879822 835231398128170635894371 := by
  unfold tailWord_4879822
  simp only [CollatzResearch.WordTrace]
  refine ⟨22247716265905722011471215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118654486751497184061179813 22247716265905722011471215)
  ·
    refine ⟨33371574398858583017206823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22247716265905722011471215 33371574398858583017206823)
    ·
      refine ⟨50057361598287874525810235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33371574398858583017206823 50057361598287874525810235)
      ·
        refine ⟨75086042397431811788715353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50057361598287874525810235 75086042397431811788715353)
        ·
          refine ⟨56314531798073858841536515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75086042397431811788715353 56314531798073858841536515)
          ·
            refine ⟨84471797697110788262304773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56314531798073858841536515 84471797697110788262304773)
            ·
              refine ⟨15838462068208272799182145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84471797697110788262304773 15838462068208272799182145)
              ·
                refine ⟨11878846551156204599386609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15838462068208272799182145 11878846551156204599386609)
                ·
                  refine ⟨8909134913367153449539957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11878846551156204599386609 8909134913367153449539957)
                  ·
                    refine ⟨835231398128170635894371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8909134913367153449539957 835231398128170635894371)
                    ·
                      rfl

theorem cell23_4879822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_4879822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879822 prefixEnd_4879822 := by exact prefixLift 4879822
  have htrace : WordTrace (prefixWord ++ tailWord_4879822) baseStart_4879822 baseEnd_4879822 := by
    simpa [prefixWord, tailWord_4879822, baseEnd_4879822] using wordTrace_append hprefix tailTrace_4879822
  have hstable : (prefixWord ++ tailWord_4879822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879822).length < 2 ^ (prefixWord ++ tailWord_4879822).sum := by decide
  have hdescent : baseEnd_4879822 < baseStart_4879822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879825 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 5, 3, 4]
def baseStart_4879825 : Nat := 118140960795 + 4879825 * 2 ^ 59
def prefixEnd_4879825 : Nat := 4983230072969 + 3 ^ 40 * 4879825 * 2
def baseEnd_4879825 : Nat := 2505695734826475395945599

theorem tailTrace_4879825 : CollatzResearch.WordTrace tailWord_4879825 prefixEnd_4879825 2505695734826475395945599 := by
  unfold tailWord_4879825
  simp only [CollatzResearch.WordTrace]
  refine ⟨177981839546234907604128929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118654559697489938402752619 177981839546234907604128929)
  ·
    refine ⟨133486379659676180703096697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177981839546234907604128929 133486379659676180703096697)
    ·
      refine ⟨100114784744757135527322523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133486379659676180703096697 100114784744757135527322523)
      ·
        refine ⟨150172177117135703290983785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100114784744757135527322523 150172177117135703290983785)
        ·
          refine ⟨112629132837851777468237839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150172177117135703290983785 112629132837851777468237839)
          ·
            refine ⟨168943699256777666202356759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112629132837851777468237839 168943699256777666202356759)
            ·
              refine ⟨253415548885166499303535139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168943699256777666202356759 253415548885166499303535139)
              ·
                refine ⟨380123323327749748955302709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 253415548885166499303535139 380123323327749748955302709)
                ·
                  refine ⟨35636561561976538964559629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 380123323327749748955302709 35636561561976538964559629)
                  ·
                    refine ⟨13363710585741202111709861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35636561561976538964559629 13363710585741202111709861)
                    ·
                      refine ⟨2505695734826475395945599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13363710585741202111709861 2505695734826475395945599)
                      ·
                        rfl

theorem cell23_4879825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_4879825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879825 prefixEnd_4879825 := by exact prefixLift 4879825
  have htrace : WordTrace (prefixWord ++ tailWord_4879825) baseStart_4879825 baseEnd_4879825 := by
    simpa [prefixWord, tailWord_4879825, baseEnd_4879825] using wordTrace_append hprefix tailTrace_4879825
  have hstable : (prefixWord ++ tailWord_4879825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879825).length < 2 ^ (prefixWord ++ tailWord_4879825).sum := by decide
  have hdescent : baseEnd_4879825 < baseStart_4879825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879865 : List Nat := [1, 2, 1, 3, 1, 2, 1, 4, 8]
def baseStart_4879865 : Nat := 118140960795 + 4879865 * 2 ^ 59
def prefixEnd_4879865 : Nat := 4983230072969 + 3 ^ 40 * 4879865 * 2
def baseEnd_4879865 : Nat := 278412919339183915493935

theorem tailTrace_4879865 : CollatzResearch.WordTrace tailWord_4879865 prefixEnd_4879865 278412919339183915493935 := by
  unfold tailWord_4879865
  simp only [CollatzResearch.WordTrace]
  refine ⟨177983298466089994435585049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118655532310726662957056699 177983298466089994435585049)
  ·
    refine ⟨133487473849567495826688787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177983298466089994435585049 133487473849567495826688787)
    ·
      refine ⟨200231210774351243740033181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133487473849567495826688787 200231210774351243740033181)
      ·
        refine ⟨75086704040381716402512443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200231210774351243740033181 75086704040381716402512443)
        ·
          refine ⟨112630056060572574603768665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75086704040381716402512443 112630056060572574603768665)
          ·
            refine ⟨84472542045429430952826499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112630056060572574603768665 84472542045429430952826499)
            ·
              refine ⟨126708813068144146429239749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84472542045429430952826499 126708813068144146429239749)
              ·
                refine ⟨23757902450277027455482453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 126708813068144146429239749 23757902450277027455482453)
                ·
                  refine ⟨278412919339183915493935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23757902450277027455482453 278412919339183915493935)
                  ·
                    rfl

theorem cell23_4879865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 4, 8].length) (baseStart_4879865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879865 prefixEnd_4879865 := by exact prefixLift 4879865
  have htrace : WordTrace (prefixWord ++ tailWord_4879865) baseStart_4879865 baseEnd_4879865 := by
    simpa [prefixWord, tailWord_4879865, baseEnd_4879865] using wordTrace_append hprefix tailTrace_4879865
  have hstable : (prefixWord ++ tailWord_4879865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879865).length < 2 ^ (prefixWord ++ tailWord_4879865).sum := by decide
  have hdescent : baseEnd_4879865 < baseStart_4879865 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879882 : List Nat := [3, 1, 2, 2, 2, 3, 1, 1, 8]
def baseStart_4879882 : Nat := 118140960795 + 4879882 * 2 ^ 59
def prefixEnd_4879882 : Nat := 4983230072969 + 3 ^ 40 * 4879882 * 2
def baseEnd_4879882 : Nat := 278413889247086852548093

theorem tailTrace_4879882 : CollatzResearch.WordTrace tailWord_4879882 prefixEnd_4879882 278413889247086852548093 := by
  unfold tailWord_4879882
  simp only [CollatzResearch.WordTrace]
  refine ⟨44495979626757101584738475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118655945671352270892635933 44495979626757101584738475)
  ·
    refine ⟨66743969440135652377107713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44495979626757101584738475 66743969440135652377107713)
    ·
      refine ⟨50057977080101739282830785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66743969440135652377107713 50057977080101739282830785)
      ·
        refine ⟨37543482810076304462123089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50057977080101739282830785 37543482810076304462123089)
        ·
          refine ⟨28157612107557228346592317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37543482810076304462123089 28157612107557228346592317)
          ·
            refine ⟨10559104540333960629972119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28157612107557228346592317 10559104540333960629972119)
            ·
              refine ⟨15838656810500940944958179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10559104540333960629972119 15838656810500940944958179)
              ·
                refine ⟨23757985215751411417437269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15838656810500940944958179 23757985215751411417437269)
                ·
                  refine ⟨278413889247086852548093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23757985215751411417437269 278413889247086852548093)
                  ·
                    rfl

theorem cell23_4879882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 1, 8].length) (baseStart_4879882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879882 prefixEnd_4879882 := by exact prefixLift 4879882
  have htrace : WordTrace (prefixWord ++ tailWord_4879882) baseStart_4879882 baseEnd_4879882 := by
    simpa [prefixWord, tailWord_4879882, baseEnd_4879882] using wordTrace_append hprefix tailTrace_4879882
  have hstable : (prefixWord ++ tailWord_4879882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879882).length < 2 ^ (prefixWord ++ tailWord_4879882).sum := by decide
  have hdescent : baseEnd_4879882 < baseStart_4879882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879886 : List Nat := [4, 1, 1, 2, 4, 1, 2, 1, 3, 4]
def baseStart_4879886 : Nat := 118140960795 + 4879886 * 2 ^ 59
def prefixEnd_4879886 : Nat := 4983230072969 + 3 ^ 40 * 4879886 * 2
def baseEnd_4879886 : Nat := 835242352382133219094273

theorem tailTrace_4879886 : CollatzResearch.WordTrace tailWord_4879886 prefixEnd_4879886 835242352382133219094273 := by
  unfold tailWord_4879886
  simp only [CollatzResearch.WordTrace]
  refine ⟨22248008049876739377762439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 118656042932675943348066341 22248008049876739377762439)
  ·
    refine ⟨33372012074815109066643659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22248008049876739377762439 33372012074815109066643659)
    ·
      refine ⟨50058018112222663599965489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33372012074815109066643659 50058018112222663599965489)
      ·
        refine ⟨37543513584166997699974117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50058018112222663599965489 37543513584166997699974117)
        ·
          refine ⟨7039408797031312068745147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37543513584166997699974117 7039408797031312068745147)
          ·
            refine ⟨10559113195546968103117721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7039408797031312068745147 10559113195546968103117721)
            ·
              refine ⟨7919334896660226077338291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10559113195546968103117721 7919334896660226077338291)
              ·
                refine ⟨11879002344990339116007437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7919334896660226077338291 11879002344990339116007437)
                ·
                  refine ⟨4454625879371377168502789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11879002344990339116007437 4454625879371377168502789)
                  ·
                    refine ⟨835242352382133219094273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4454625879371377168502789 835242352382133219094273)
                    ·
                      rfl

theorem cell23_4879886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 1, 3, 4].length) (baseStart_4879886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879886 prefixEnd_4879886 := by exact prefixLift 4879886
  have htrace : WordTrace (prefixWord ++ tailWord_4879886) baseStart_4879886 baseEnd_4879886 := by
    simpa [prefixWord, tailWord_4879886, baseEnd_4879886] using wordTrace_append hprefix tailTrace_4879886
  have hstable : (prefixWord ++ tailWord_4879886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879886).length < 2 ^ (prefixWord ++ tailWord_4879886).sum := by decide
  have hdescent : baseEnd_4879886 < baseStart_4879886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879929 : List Nat := [1, 2, 1, 5, 1, 2, 2, 3, 1, 5]
def baseStart_4879929 : Nat := 118140960795 + 4879929 * 2 ^ 59
def prefixEnd_4879929 : Nat := 4983230072969 + 3 ^ 40 * 4879929 * 2
def baseEnd_4879929 : Nat := 835249712271514329681707

theorem tailTrace_4879929 : CollatzResearch.WordTrace tailWord_4879929 prefixEnd_4879929 835249712271514329681707 := by
  unfold tailWord_4879929
  simp only [CollatzResearch.WordTrace]
  refine ⟨177985632737858133365914841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118657088491905422243943227 177985632737858133365914841)
  ·
    refine ⟨133489224553393600024436131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177985632737858133365914841 133489224553393600024436131)
    ·
      refine ⟨200233836830090400036654197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133489224553393600024436131 200233836830090400036654197)
      ·
        refine ⟨18771922202820975003436331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 200233836830090400036654197 18771922202820975003436331)
        ·
          refine ⟨28157883304231462505154497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18771922202820975003436331 28157883304231462505154497)
          ·
            refine ⟨21118412478173596878865873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28157883304231462505154497 21118412478173596878865873)
            ·
              refine ⟨15838809358630197659149405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21118412478173596878865873 15838809358630197659149405)
              ·
                refine ⟨5939553509486324122181027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15838809358630197659149405 5939553509486324122181027)
                ·
                  refine ⟨8909330264229486183271541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5939553509486324122181027 8909330264229486183271541)
                  ·
                    refine ⟨835249712271514329681707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8909330264229486183271541 835249712271514329681707)
                    ·
                      rfl

theorem cell23_4879929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 5].length) (baseStart_4879929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879929 prefixEnd_4879929 := by exact prefixLift 4879929
  have htrace : WordTrace (prefixWord ++ tailWord_4879929) baseStart_4879929 baseEnd_4879929 := by
    simpa [prefixWord, tailWord_4879929, baseEnd_4879929] using wordTrace_append hprefix tailTrace_4879929
  have hstable : (prefixWord ++ tailWord_4879929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879929).length < 2 ^ (prefixWord ++ tailWord_4879929).sum := by decide
  have hdescent : baseEnd_4879929 < baseStart_4879929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879943 : List Nat := [1, 1, 4, 1, 5, 2, 1, 1, 3, 1, 3]
def baseStart_4879943 : Nat := 118140960795 + 4879943 * 2 ^ 59
def prefixEnd_4879943 : Nat := 4983230072969 + 3 ^ 40 * 4879943 * 2
def baseEnd_4879943 : Nat := 2505756325543705934270057

theorem tailTrace_4879943 : CollatzResearch.WordTrace tailWord_4879943 prefixEnd_4879943 2505756325543705934270057 := by
  unfold tailWord_4879943
  simp only [CollatzResearch.WordTrace]
  refine ⟨177986143359807413756924483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118657428906538275837949655 177986143359807413756924483)
  ·
    refine ⟨266979215039711120635386725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177986143359807413756924483 266979215039711120635386725)
    ·
      refine ⟨50058602819945835119135011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 266979215039711120635386725 50058602819945835119135011)
      ·
        refine ⟨75087904229918752678702517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50058602819945835119135011 75087904229918752678702517)
        ·
          refine ⟨7039491021554883063628361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75087904229918752678702517 7039491021554883063628361)
          ·
            refine ⟨5279618266166162297721271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7039491021554883063628361 5279618266166162297721271)
            ·
              refine ⟨7919427399249243446581907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5279618266166162297721271 7919427399249243446581907)
              ·
                refine ⟨11879141098873865169872861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7919427399249243446581907 11879141098873865169872861)
                ·
                  refine ⟨4454677912077699438702323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11879141098873865169872861 4454677912077699438702323)
                  ·
                    refine ⟨6682016868116549158053485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4454677912077699438702323 6682016868116549158053485)
                    ·
                      refine ⟨2505756325543705934270057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6682016868116549158053485 2505756325543705934270057)
                      ·
                        rfl

theorem cell23_4879943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 2, 1, 1, 3, 1, 3].length) (baseStart_4879943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879943 prefixEnd_4879943 := by exact prefixLift 4879943
  have htrace : WordTrace (prefixWord ++ tailWord_4879943) baseStart_4879943 baseEnd_4879943 := by
    simpa [prefixWord, tailWord_4879943, baseEnd_4879943] using wordTrace_append hprefix tailTrace_4879943
  have hstable : (prefixWord ++ tailWord_4879943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879943).length < 2 ^ (prefixWord ++ tailWord_4879943).sum := by decide
  have hdescent : baseEnd_4879943 < baseStart_4879943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879952 : List Nat := [2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 5]
def baseStart_4879952 : Nat := 118140960795 + 4879952 * 2 ^ 59
def prefixEnd_4879952 : Nat := 4983230072969 + 3 ^ 40 * 4879952 * 2
def baseEnd_4879952 : Nat := 2505760946869596399057515

theorem tailTrace_4879952 : CollatzResearch.WordTrace tailWord_4879952 prefixEnd_4879952 2505760946869596399057515 := by
  unfold tailWord_4879952
  simp only [CollatzResearch.WordTrace]
  refine ⟨88993235808387404147001055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118657647744516538862668073 88993235808387404147001055)
  ·
    refine ⟨133489853712581106220501583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88993235808387404147001055 133489853712581106220501583)
    ·
      refine ⟨200234780568871659330752375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133489853712581106220501583 200234780568871659330752375)
      ·
        refine ⟨300352170853307488996128563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200234780568871659330752375 300352170853307488996128563)
        ·
          refine ⟨450528256279961233494192845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 300352170853307488996128563 450528256279961233494192845)
          ·
            refine ⟨168948096104985462560322317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 450528256279961233494192845 168948096104985462560322317)
            ·
              refine ⟨63355536039369548460120869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 168948096104985462560322317 63355536039369548460120869)
              ·
                refine ⟨11879163007381790336272663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63355536039369548460120869 11879163007381790336272663)
                ·
                  refine ⟨17818744511072685504408995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11879163007381790336272663 17818744511072685504408995)
                  ·
                    refine ⟨26728116766609028256613493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17818744511072685504408995 26728116766609028256613493)
                    ·
                      refine ⟨2505760946869596399057515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26728116766609028256613493 2505760946869596399057515)
                      ·
                        rfl

theorem cell23_4879952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_4879952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879952 prefixEnd_4879952 := by exact prefixLift 4879952
  have htrace : WordTrace (prefixWord ++ tailWord_4879952) baseStart_4879952 baseEnd_4879952 := by
    simpa [prefixWord, tailWord_4879952, baseEnd_4879952] using wordTrace_append hprefix tailTrace_4879952
  have hstable : (prefixWord ++ tailWord_4879952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879952).length < 2 ^ (prefixWord ++ tailWord_4879952).sum := by decide
  have hdescent : baseEnd_4879952 < baseStart_4879952 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879962 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4]
def baseStart_4879962 : Nat := 118140960795 + 4879962 * 2 ^ 59
def prefixEnd_4879962 : Nat := 4983230072969 + 3 ^ 40 * 4879962 * 2
def baseEnd_4879962 : Nat := 2505766081676141359932469

theorem tailTrace_4879962 : CollatzResearch.WordTrace tailWord_4879962 prefixEnd_4879962 2505766081676141359932469 := by
  unfold tailWord_4879962
  simp only [CollatzResearch.WordTrace]
  refine ⟨44496709086684645000466535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118657890897825720001244093 44496709086684645000466535)
  ·
    refine ⟨66745063630026967500699803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44496709086684645000466535 66745063630026967500699803)
    ·
      refine ⟨100117595445040451251049705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66745063630026967500699803 100117595445040451251049705)
      ·
        refine ⟨75088196583780338438287279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100117595445040451251049705 75088196583780338438287279)
        ·
          refine ⟨112632294875670507657430919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75088196583780338438287279 112632294875670507657430919)
          ·
            refine ⟨168948442313505761486146379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 112632294875670507657430919 168948442313505761486146379)
            ·
              refine ⟨253422663470258642229219569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 168948442313505761486146379 253422663470258642229219569)
              ·
                refine ⟨190066997602693981671914677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 253422663470258642229219569 190066997602693981671914677)
                ·
                  refine ⟨17818781025252560781742001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 190066997602693981671914677 17818781025252560781742001)
                  ·
                    refine ⟨13364085768939420586306501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17818781025252560781742001 13364085768939420586306501)
                    ·
                      refine ⟨2505766081676141359932469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13364085768939420586306501 2505766081676141359932469)
                      ·
                        rfl

theorem cell23_4879962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4].length) (baseStart_4879962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879962 prefixEnd_4879962 := by exact prefixLift 4879962
  have htrace : WordTrace (prefixWord ++ tailWord_4879962) baseStart_4879962 baseEnd_4879962 := by
    simpa [prefixWord, tailWord_4879962, baseEnd_4879962] using wordTrace_append hprefix tailTrace_4879962
  have hstable : (prefixWord ++ tailWord_4879962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879962).length < 2 ^ (prefixWord ++ tailWord_4879962).sum := by decide
  have hdescent : baseEnd_4879962 < baseStart_4879962 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879969 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 3, 2, 3]
def baseStart_4879969 : Nat := 118140960795 + 4879969 * 2 ^ 59
def prefixEnd_4879969 : Nat := 4983230072969 + 3 ^ 40 * 4879969 * 2
def baseEnd_4879969 : Nat := 2505769676040722832544937

theorem tailTrace_4879969 : CollatzResearch.WordTrace tailWord_4879969 prefixEnd_4879969 2505769676040722832544937 := by
  unfold tailWord_4879969
  simp only [CollatzResearch.WordTrace]
  refine ⟨177987091657713220197370961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118658061105142146798247307 177987091657713220197370961)
  ·
    refine ⟨133490318743284915148028221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177987091657713220197370961 133490318743284915148028221)
    ·
      refine ⟨50058869528731843180510583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133490318743284915148028221 50058869528731843180510583)
      ·
        refine ⟨75088304293097764770765875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50058869528731843180510583 75088304293097764770765875)
        ·
          refine ⟨112632456439646647156148813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75088304293097764770765875 112632456439646647156148813)
          ·
            refine ⟨42237171164867492683555805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 112632456439646647156148813 42237171164867492683555805)
            ·
              refine ⟨15838939186825309756333427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42237171164867492683555805 15838939186825309756333427)
              ·
                refine ⟨23758408780237964634500141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15838939186825309756333427 23758408780237964634500141)
                ·
                  refine ⟨8909403292589236737937553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23758408780237964634500141 8909403292589236737937553)
                  ·
                    refine ⟨6682052469441927553453165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8909403292589236737937553 6682052469441927553453165)
                    ·
                      refine ⟨2505769676040722832544937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6682052469441927553453165 2505769676040722832544937)
                      ·
                        rfl

theorem cell23_4879969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_4879969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879969 prefixEnd_4879969 := by exact prefixLift 4879969
  have htrace : WordTrace (prefixWord ++ tailWord_4879969) baseStart_4879969 baseEnd_4879969 := by
    simpa [prefixWord, tailWord_4879969, baseEnd_4879969] using wordTrace_append hprefix tailTrace_4879969
  have hstable : (prefixWord ++ tailWord_4879969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879969).length < 2 ^ (prefixWord ++ tailWord_4879969).sum := by decide
  have hdescent : baseEnd_4879969 < baseStart_4879969 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879972 : List Nat := [2, 3, 1, 1, 2, 3, 2, 9]
def baseStart_4879972 : Nat := 118140960795 + 4879972 * 2 ^ 59
def prefixEnd_4879972 : Nat := 4983230072969 + 3 ^ 40 * 4879972 * 2
def baseEnd_4879972 : Nat := 92806341351210604474349

theorem tailTrace_4879972 : CollatzResearch.WordTrace tailWord_4879972 prefixEnd_4879972 92806341351210604474349 := by
  unfold tailWord_4879972
  simp only [CollatzResearch.WordTrace]
  refine ⟨88993600538351175854865085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118658134051134901139820113 88993600538351175854865085)
  ·
    refine ⟨33372600201881690945574407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 88993600538351175854865085 33372600201881690945574407)
    ·
      refine ⟨50058900302822536418361611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33372600201881690945574407 50058900302822536418361611)
      ·
        refine ⟨75088350454233804627542417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50058900302822536418361611 75088350454233804627542417)
        ·
          refine ⟨56316262840675353470656813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75088350454233804627542417 56316262840675353470656813)
          ·
            refine ⟨21118598565253257551496305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56316262840675353470656813 21118598565253257551496305)
            ·
              refine ⟨15838948923939943163622229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21118598565253257551496305 15838948923939943163622229)
              ·
                refine ⟨92806341351210604474349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15838948923939943163622229 92806341351210604474349)
                ·
                  rfl

theorem cell23_4879972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 2, 9].length) (baseStart_4879972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879972 prefixEnd_4879972 := by exact prefixLift 4879972
  have htrace : WordTrace (prefixWord ++ tailWord_4879972) baseStart_4879972 baseEnd_4879972 := by
    simpa [prefixWord, tailWord_4879972, baseEnd_4879972] using wordTrace_append hprefix tailTrace_4879972
  have hstable : (prefixWord ++ tailWord_4879972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879972).length < 2 ^ (prefixWord ++ tailWord_4879972).sum := by decide
  have hdescent : baseEnd_4879972 < baseStart_4879972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879983 : List Nat := [1, 1, 2, 1, 3, 2, 1, 7, 1, 2, 2]
def baseStart_4879983 : Nat := 118140960795 + 4879983 * 2 ^ 59
def prefixEnd_4879983 : Nat := 4983230072969 + 3 ^ 40 * 4879983 * 2
def baseEnd_4879983 : Nat := 2505776864769885777769873

theorem tailTrace_4879983 : CollatzResearch.WordTrace tailWord_4879983 prefixEnd_4879983 2505776864769885777769873 := by
  unfold tailWord_4879983
  simp only [CollatzResearch.WordTrace]
  refine ⟨177987602279662500588380603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118658401519775000392253735 177987602279662500588380603)
  ·
    refine ⟨266981403419493750882570905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177987602279662500588380603 266981403419493750882570905)
    ·
      refine ⟨200236052564620313161928179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266981403419493750882570905 200236052564620313161928179)
      ·
        refine ⟨300354078846930469742892269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 200236052564620313161928179 300354078846930469742892269)
        ·
          refine ⟨112632779567598926153584601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 300354078846930469742892269 112632779567598926153584601)
          ·
            refine ⟨84474584675699194615188451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112632779567598926153584601 84474584675699194615188451)
            ·
              refine ⟨126711877013548791922782677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84474584675699194615188451 126711877013548791922782677)
              ·
                refine ⟨2969809617505049810690219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 126711877013548791922782677 2969809617505049810690219)
                ·
                  refine ⟨4454714426257574716035329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969809617505049810690219 4454714426257574716035329)
                  ·
                    refine ⟨3341035819693181037026497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4454714426257574716035329 3341035819693181037026497)
                    ·
                      refine ⟨2505776864769885777769873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341035819693181037026497 2505776864769885777769873)
                      ·
                        rfl

theorem cell23_4879983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 7, 1, 2, 2].length) (baseStart_4879983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879983 prefixEnd_4879983 := by exact prefixLift 4879983
  have htrace : WordTrace (prefixWord ++ tailWord_4879983) baseStart_4879983 baseEnd_4879983 := by
    simpa [prefixWord, tailWord_4879983, baseEnd_4879983] using wordTrace_append hprefix tailTrace_4879983
  have hstable : (prefixWord ++ tailWord_4879983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879983).length < 2 ^ (prefixWord ++ tailWord_4879983).sum := by decide
  have hdescent : baseEnd_4879983 < baseStart_4879983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879986 : List Nat := [3, 2, 1, 2, 3, 3, 1, 1, 1, 1, 5]
def baseStart_4879986 : Nat := 118140960795 + 4879986 * 2 ^ 59
def prefixEnd_4879986 : Nat := 4983230072969 + 3 ^ 40 * 4879986 * 2
def baseEnd_4879986 : Nat := 2505778405211849266032359

theorem tailTrace_4879986 : CollatzResearch.WordTrace tailWord_4879986 prefixEnd_4879986 2505778405211849266032359 := by
  unfold tailWord_4879986
  simp only [CollatzResearch.WordTrace]
  refine ⟨44496927924662908025184953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118658474465767754733826541 44496927924662908025184953)
  ·
    refine ⟨33372695943497181018888715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44496927924662908025184953 33372695943497181018888715)
    ·
      refine ⟨50059043915245771528333073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33372695943497181018888715 50059043915245771528333073)
      ·
        refine ⟨37544282936434328646249805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50059043915245771528333073 37544282936434328646249805)
        ·
          refine ⟨14079106101162873242343677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37544282936434328646249805 14079106101162873242343677)
          ·
            refine ⟨5279664787936077465878879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14079106101162873242343677 5279664787936077465878879)
            ·
              refine ⟨7919497181904116198818319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5279664787936077465878879 7919497181904116198818319)
              ·
                refine ⟨11879245772856174298227479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7919497181904116198818319 11879245772856174298227479)
                ·
                  refine ⟨17818868659284261447341219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11879245772856174298227479 17818868659284261447341219)
                  ·
                    refine ⟨26728302988926392171011829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17818868659284261447341219 26728302988926392171011829)
                    ·
                      refine ⟨2505778405211849266032359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26728302988926392171011829 2505778405211849266032359)
                      ·
                        rfl

theorem cell23_4879986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_4879986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879986 prefixEnd_4879986 := by exact prefixLift 4879986
  have htrace : WordTrace (prefixWord ++ tailWord_4879986) baseStart_4879986 baseEnd_4879986 := by
    simpa [prefixWord, tailWord_4879986, baseEnd_4879986] using wordTrace_append hprefix tailTrace_4879986
  have hstable : (prefixWord ++ tailWord_4879986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879986).length < 2 ^ (prefixWord ++ tailWord_4879986).sum := by decide
  have hdescent : baseEnd_4879986 < baseStart_4879986 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4879999 : List Nat := [1, 1, 2, 2, 1, 1, 1, 2, 8, 1, 3]
def baseStart_4879999 : Nat := 118140960795 + 4879999 * 2 ^ 59
def prefixEnd_4879999 : Nat := 4983230072969 + 3 ^ 40 * 4879999 * 2
def baseEnd_4879999 : Nat := 2505785080460357715169799

theorem tailTrace_4879999 : CollatzResearch.WordTrace tailWord_4879999 prefixEnd_4879999 2505785080460357715169799 := by
  unfold tailWord_4879999
  simp only [CollatzResearch.WordTrace]
  refine ⟨177988185847604535320963051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118658790565069690213975367 177988185847604535320963051)
  ·
    refine ⟨266982278771406802981444577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177988185847604535320963051 266982278771406802981444577)
    ·
      refine ⟨200236709078555102236083433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266982278771406802981444577 200236709078555102236083433)
      ·
        refine ⟨150177531808916326677062575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 200236709078555102236083433 150177531808916326677062575)
        ·
          refine ⟨225266297713374490015593863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150177531808916326677062575 225266297713374490015593863)
          ·
            refine ⟨337899446570061735023390795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225266297713374490015593863 337899446570061735023390795)
            ·
              refine ⟨506849169855092602535086193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 337899446570061735023390795 506849169855092602535086193)
              ·
                refine ⟨380136877391319451901314645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 506849169855092602535086193 380136877391319451901314645)
                ·
                  refine ⟨4454729031929524826968531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 380136877391319451901314645 4454729031929524826968531)
                  ·
                    refine ⟨6682093547894287240452797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4454729031929524826968531 6682093547894287240452797)
                    ·
                      refine ⟨2505785080460357715169799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6682093547894287240452797 2505785080460357715169799)
                      ·
                        rfl

theorem cell23_4879999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 2, 8, 1, 3].length) (baseStart_4879999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4879999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4879999 prefixEnd_4879999 := by exact prefixLift 4879999
  have htrace : WordTrace (prefixWord ++ tailWord_4879999) baseStart_4879999 baseEnd_4879999 := by
    simpa [prefixWord, tailWord_4879999, baseEnd_4879999] using wordTrace_append hprefix tailTrace_4879999
  have hstable : (prefixWord ++ tailWord_4879999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4879999).length < 2 ^ (prefixWord ++ tailWord_4879999).sum := by decide
  have hdescent : baseEnd_4879999 < baseStart_4879999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4879999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880034 : List Nat := [3, 3, 1, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_4880034 : Nat := 118140960795 + 4880034 * 2 ^ 59
def prefixEnd_4880034 : Nat := 4983230072969 + 3 ^ 40 * 4880034 * 2
def baseEnd_4880034 : Nat := 2505803052283265078232139

theorem tailTrace_4880034 : CollatzResearch.WordTrace tailWord_4880034 prefixEnd_4880034 2505803052283265078232139 := by
  unfold tailWord_4880034
  simp only [CollatzResearch.WordTrace]
  refine ⟨44497365600619434074621789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118659641601651824198991437 44497365600619434074621789)
  ·
    refine ⟨16686512100232287777983171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44497365600619434074621789 16686512100232287777983171)
    ·
      refine ⟨25029768150348431666974757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16686512100232287777983171 25029768150348431666974757)
      ·
        refine ⟨4693081528190330937557767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25029768150348431666974757 4693081528190330937557767)
        ·
          refine ⟨7039622292285496406336651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4693081528190330937557767 7039622292285496406336651)
          ·
            refine ⟨10559433438428244609504977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7039622292285496406336651 10559433438428244609504977)
            ·
              refine ⟨7919575078821183457128733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10559433438428244609504977 7919575078821183457128733)
              ·
                refine ⟨2969840654557943796423275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7919575078821183457128733 2969840654557943796423275)
                ·
                  refine ⟨4454760981836915694634913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969840654557943796423275 4454760981836915694634913)
                  ·
                    refine ⟨3341070736377686770976185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4454760981836915694634913 3341070736377686770976185)
                    ·
                      refine ⟨2505803052283265078232139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341070736377686770976185 2505803052283265078232139)
                      ·
                        rfl

theorem cell23_4880034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_4880034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880034 prefixEnd_4880034 := by exact prefixLift 4880034
  have htrace : WordTrace (prefixWord ++ tailWord_4880034) baseStart_4880034 baseEnd_4880034 := by
    simpa [prefixWord, tailWord_4880034, baseEnd_4880034] using wordTrace_append hprefix tailTrace_4880034
  have hstable : (prefixWord ++ tailWord_4880034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880034).length < 2 ^ (prefixWord ++ tailWord_4880034).sum := by decide
  have hdescent : baseEnd_4880034 < baseStart_4880034 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880077 : List Nat := [1, 6, 2, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_4880077 : Nat := 118140960795 + 4880077 * 2 ^ 59
def prefixEnd_4880077 : Nat := 4983230072969 + 3 ^ 40 * 4880077 * 2
def baseEnd_4880077 : Nat := 2505825131951408409994441

theorem tailTrace_4880077 : CollatzResearch.WordTrace tailWord_4880077 prefixEnd_4880077 2505825131951408409994441 := by
  unfold tailWord_4880077
  simp only [CollatzResearch.WordTrace]
  refine ⟨177991030741321954642302485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118660687160881303094868323 177991030741321954642302485)
  ·
    refine ⟨8343329565999466623857929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 177991030741321954642302485 8343329565999466623857929)
    ·
      refine ⟨6257497174499599967893447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8343329565999466623857929 6257497174499599967893447)
      ·
        refine ⟨9386245761749399951840171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6257497174499599967893447 9386245761749399951840171)
        ·
          refine ⟨14079368642624099927760257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9386245761749399951840171 14079368642624099927760257)
          ·
            refine ⟨10559526481968074945820193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14079368642624099927760257 10559526481968074945820193)
            ·
              refine ⟨7919644861476056209365145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10559526481968074945820193 7919644861476056209365145)
              ·
                refine ⟨5939733646107042157023859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7919644861476056209365145 5939733646107042157023859)
                ·
                  refine ⟨8909600469160563235535789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5939733646107042157023859 8909600469160563235535789)
                  ·
                    refine ⟨3341100175935211213325921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8909600469160563235535789 3341100175935211213325921)
                    ·
                      refine ⟨2505825131951408409994441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341100175935211213325921 2505825131951408409994441)
                      ·
                        rfl

theorem cell23_4880077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_4880077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880077 prefixEnd_4880077 := by exact prefixLift 4880077
  have htrace : WordTrace (prefixWord ++ tailWord_4880077) baseStart_4880077 baseEnd_4880077 := by
    simpa [prefixWord, tailWord_4880077, baseEnd_4880077] using wordTrace_append hprefix tailTrace_4880077
  have hstable : (prefixWord ++ tailWord_4880077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880077).length < 2 ^ (prefixWord ++ tailWord_4880077).sum := by decide
  have hdescent : baseEnd_4880077 < baseStart_4880077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880093 : List Nat := [1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4880093 : Nat := 118140960795 + 4880093 * 2 ^ 59
def prefixEnd_4880093 : Nat := 4983230072969 + 3 ^ 40 * 4880093 * 2
def baseEnd_4880093 : Nat := 2505833347641880347394367

theorem tailTrace_4880093 : CollatzResearch.WordTrace tailWord_4880093 prefixEnd_4880093 2505833347641880347394367 := by
  unfold tailWord_4880093
  simp only [CollatzResearch.WordTrace]
  refine ⟨177991614309263989374884933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118661076206175992916589955 177991614309263989374884933)
  ·
    refine ⟨33373427682986998007790925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 177991614309263989374884933 33373427682986998007790925)
    ·
      refine ⟨12515035381120124252921597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33373427682986998007790925 12515035381120124252921597)
      ·
        refine ⟨4693138267920046594845599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12515035381120124252921597 4693138267920046594845599)
        ·
          refine ⟨7039707401880069892268399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4693138267920046594845599 7039707401880069892268399)
          ·
            refine ⟨10559561102820104838402599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7039707401880069892268399 10559561102820104838402599)
            ·
              refine ⟨15839341654230157257603899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10559561102820104838402599 15839341654230157257603899)
              ·
                refine ⟨23759012481345235886405849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15839341654230157257603899 23759012481345235886405849)
                ·
                  refine ⟨17819259361008926914804387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23759012481345235886405849 17819259361008926914804387)
                  ·
                    refine ⟨26728889041513390372206581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17819259361008926914804387 26728889041513390372206581)
                    ·
                      refine ⟨2505833347641880347394367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26728889041513390372206581 2505833347641880347394367)
                      ·
                        rfl

theorem cell23_4880093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4880093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880093 prefixEnd_4880093 := by exact prefixLift 4880093
  have htrace : WordTrace (prefixWord ++ tailWord_4880093) baseStart_4880093 baseEnd_4880093 := by
    simpa [prefixWord, tailWord_4880093, baseEnd_4880093] using wordTrace_append hprefix tailTrace_4880093
  have hstable : (prefixWord ++ tailWord_4880093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880093).length < 2 ^ (prefixWord ++ tailWord_4880093).sum := by decide
  have hdescent : baseEnd_4880093 < baseStart_4880093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880096 : List Nat := [2, 1, 1, 3, 1, 2, 5, 3, 5]
def baseStart_4880096 : Nat := 118140960795 + 4880096 * 2 ^ 59
def prefixEnd_4880096 : Nat := 4983230072969 + 3 ^ 40 * 4880096 * 2
def baseEnd_4880096 : Nat := 278426098675982648406317

theorem tailTrace_4880096 : CollatzResearch.WordTrace tailWord_4880096 prefixEnd_4880096 278426098675982648406317 := by
  unfold tailWord_4880096
  simp only [CollatzResearch.WordTrace]
  refine ⟨88995861864126560443622071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118661149152168747258162761 88995861864126560443622071)
  ·
    refine ⟨133493792796189840665433107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88995861864126560443622071 133493792796189840665433107)
    ·
      refine ⟨200240689194284760998149661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 133493792796189840665433107 200240689194284760998149661)
      ·
        refine ⟨75090258447856785374306123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 200240689194284760998149661 75090258447856785374306123)
        ·
          refine ⟨112635387671785178061459185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75090258447856785374306123 112635387671785178061459185)
          ·
            refine ⟨84476540753838883546094389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 112635387671785178061459185 84476540753838883546094389)
            ·
              refine ⟨7919675695672395332446349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84476540753838883546094389 7919675695672395332446349)
              ·
                refine ⟨2969878385877148249667381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7919675695672395332446349 2969878385877148249667381)
                ·
                  refine ⟨278426098675982648406317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2969878385877148249667381 278426098675982648406317)
                  ·
                    rfl

theorem cell23_4880096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 5, 3, 5].length) (baseStart_4880096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880096 prefixEnd_4880096 := by exact prefixLift 4880096
  have htrace : WordTrace (prefixWord ++ tailWord_4880096) baseStart_4880096 baseEnd_4880096 := by
    simpa [prefixWord, tailWord_4880096, baseEnd_4880096] using wordTrace_append hprefix tailTrace_4880096
  have hstable : (prefixWord ++ tailWord_4880096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880096).length < 2 ^ (prefixWord ++ tailWord_4880096).sum := by decide
  have hdescent : baseEnd_4880096 < baseStart_4880096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880113 : List Nat := [1, 2, 2, 2, 2, 4, 3, 2, 5]
def baseStart_4880113 : Nat := 118140960795 + 4880113 * 2 ^ 59
def prefixEnd_4880113 : Nat := 4983230072969 + 3 ^ 40 * 4880113 * 2
def baseEnd_4880113 : Nat := 278427068583885585460475

theorem tailTrace_4880113 : CollatzResearch.WordTrace tailWord_4880113 prefixEnd_4880113 278427068583885585460475 := by
  unfold tailWord_4880113
  simp only [CollatzResearch.WordTrace]
  refine ⟨177992343769191532790612993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118661562512794355193741995 177992343769191532790612993)
  ·
    refine ⟨133494257826893649592959745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177992343769191532790612993 133494257826893649592959745)
    ·
      refine ⟨100120693370170237194719809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133494257826893649592959745 100120693370170237194719809)
      ·
        refine ⟨75090520027627677896039857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100120693370170237194719809 75090520027627677896039857)
        ·
          refine ⟨56317890020720758422029893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75090520027627677896039857 56317890020720758422029893)
          ·
            refine ⟨10559604378885142204130605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56317890020720758422029893 10559604378885142204130605)
            ·
              refine ⟨3959851642081928326548977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10559604378885142204130605 3959851642081928326548977)
              ·
                refine ⟨2969888731561446244911733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3959851642081928326548977 2969888731561446244911733)
                ·
                  refine ⟨278427068583885585460475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2969888731561446244911733 278427068583885585460475)
                  ·
                    rfl

theorem cell23_4880113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 3, 2, 5].length) (baseStart_4880113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880113 prefixEnd_4880113 := by exact prefixLift 4880113
  have htrace : WordTrace (prefixWord ++ tailWord_4880113) baseStart_4880113 baseEnd_4880113 := by
    simpa [prefixWord, tailWord_4880113, baseEnd_4880113] using wordTrace_append hprefix tailTrace_4880113
  have hstable : (prefixWord ++ tailWord_4880113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880113).length < 2 ^ (prefixWord ++ tailWord_4880113).sum := by decide
  have hdescent : baseEnd_4880113 < baseStart_4880113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880129 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 3, 3, 4]
def baseStart_4880129 : Nat := 118140960795 + 4880129 * 2 ^ 59
def prefixEnd_4880129 : Nat := 4983230072969 + 3 ^ 40 * 4880129 * 2
def baseEnd_4880129 : Nat := 2505851832945442206544201

theorem tailTrace_4880129 : CollatzResearch.WordTrace tailWord_4880129 prefixEnd_4880129 2505851832945442206544201 := by
  unfold tailWord_4880129
  simp only [CollatzResearch.WordTrace]
  refine ⟨177992927337133567523195441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118661951558089045015463627 177992927337133567523195441)
  ·
    refine ⟨133494695502850175642396581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177992927337133567523195441 133494695502850175642396581)
    ·
      refine ⟨25030255406784407932949359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 133494695502850175642396581 25030255406784407932949359)
      ·
        refine ⟨37545383110176611899424039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25030255406784407932949359 37545383110176611899424039)
        ·
          refine ⟨56318074665264917849136059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37545383110176611899424039 56318074665264917849136059)
          ·
            refine ⟨84477111997897376773704089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56318074665264917849136059 84477111997897376773704089)
            ·
              refine ⟨63357833998423032580278067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84477111997897376773704089 63357833998423032580278067)
              ·
                refine ⟨95036750997634548870417101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63357833998423032580278067 95036750997634548870417101)
                ·
                  refine ⟨35638781624112955826406413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95036750997634548870417101 35638781624112955826406413)
                  ·
                    refine ⟨13364543109042358434902405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35638781624112955826406413 13364543109042358434902405)
                    ·
                      refine ⟨2505851832945442206544201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13364543109042358434902405 2505851832945442206544201)
                      ·
                        rfl

theorem cell23_4880129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_4880129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880129 prefixEnd_4880129 := by exact prefixLift 4880129
  have htrace : WordTrace (prefixWord ++ tailWord_4880129) baseStart_4880129 baseEnd_4880129 := by
    simpa [prefixWord, tailWord_4880129, baseEnd_4880129] using wordTrace_append hprefix tailTrace_4880129
  have hstable : (prefixWord ++ tailWord_4880129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880129).length < 2 ^ (prefixWord ++ tailWord_4880129).sum := by decide
  have hdescent : baseEnd_4880129 < baseStart_4880129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880159 : List Nat := [1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 6]
def baseStart_4880159 : Nat := 118140960795 + 4880159 * 2 ^ 59
def prefixEnd_4880159 : Nat := 4983230072969 + 3 ^ 40 * 4880159 * 2
def baseEnd_4880159 : Nat := 2505867237365077089169063

theorem tailTrace_4880159 : CollatzResearch.WordTrace tailWord_4880159 prefixEnd_4880159 2505867237365077089169063 := by
  unfold tailWord_4880159
  simp only [CollatzResearch.WordTrace]
  refine ⟨177994021527024882646787531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118662681018016588431191687 177994021527024882646787531)
  ·
    refine ⟨266991032290537323970181297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 177994021527024882646787531 266991032290537323970181297)
    ·
      refine ⟨200243274217902992977635973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 266991032290537323970181297 200243274217902992977635973)
      ·
        refine ⟨37545613915856811183306745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 200243274217902992977635973 37545613915856811183306745)
        ·
          refine ⟨28159210436892608387480059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37545613915856811183306745 28159210436892608387480059)
          ·
            refine ⟨42238815655338912581220089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28159210436892608387480059 42238815655338912581220089)
            ·
              refine ⟨31679111741504184435915067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42238815655338912581220089 31679111741504184435915067)
              ·
                refine ⟨47518667612256276653872601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31679111741504184435915067 47518667612256276653872601)
                ·
                  refine ⟨35639000709192207490404451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47518667612256276653872601 35639000709192207490404451)
                  ·
                    refine ⟨53458501063788311235606677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35639000709192207490404451 53458501063788311235606677)
                    ·
                      refine ⟨2505867237365077089169063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53458501063788311235606677 2505867237365077089169063)
                      ·
                        rfl

theorem cell23_4880159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_4880159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880159 prefixEnd_4880159 := by exact prefixLift 4880159
  have htrace : WordTrace (prefixWord ++ tailWord_4880159) baseStart_4880159 baseEnd_4880159 := by
    simpa [prefixWord, tailWord_4880159, baseEnd_4880159] using wordTrace_append hprefix tailTrace_4880159
  have hstable : (prefixWord ++ tailWord_4880159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880159).length < 2 ^ (prefixWord ++ tailWord_4880159).sum := by decide
  have hdescent : baseEnd_4880159 < baseStart_4880159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880180 : List Nat := [2, 5, 1, 1, 2, 2, 1, 1, 2, 4, 2]
def baseStart_4880180 : Nat := 118140960795 + 4880180 * 2 ^ 59
def prefixEnd_4880180 : Nat := 4983230072969 + 3 ^ 40 * 4880180 * 2
def baseEnd_4880180 : Nat := 2505878020458821507006467

theorem tailTrace_4880180 : CollatzResearch.WordTrace tailWord_4880180 prefixEnd_4880180 2505878020458821507006467 := by
  unfold tailWord_4880180
  simp only [CollatzResearch.WordTrace]
  refine ⟨88997393729974401616650997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118663191639965868822201329 88997393729974401616650997)
  ·
    refine ⟨8343505662185100151561031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 88997393729974401616650997 8343505662185100151561031)
    ·
      refine ⟨12515258493277650227341547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8343505662185100151561031 12515258493277650227341547)
      ·
        refine ⟨18772887739916475341012321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12515258493277650227341547 18772887739916475341012321)
        ·
          refine ⟨14079665804937356505759241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18772887739916475341012321 14079665804937356505759241)
          ·
            refine ⟨10559749353703017379319431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14079665804937356505759241 10559749353703017379319431)
            ·
              refine ⟨15839624030554526068979147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10559749353703017379319431 15839624030554526068979147)
              ·
                refine ⟨23759436045831789103468721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15839624030554526068979147 23759436045831789103468721)
                ·
                  refine ⟨17819577034373841827601541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23759436045831789103468721 17819577034373841827601541)
                  ·
                    refine ⟨3341170693945095342675289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17819577034373841827601541 3341170693945095342675289)
                    ·
                      refine ⟨2505878020458821507006467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341170693945095342675289 2505878020458821507006467)
                      ·
                        rfl

theorem cell23_4880180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 1, 1, 2, 4, 2].length) (baseStart_4880180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880180 prefixEnd_4880180 := by exact prefixLift 4880180
  have htrace : WordTrace (prefixWord ++ tailWord_4880180) baseStart_4880180 baseEnd_4880180 := by
    simpa [prefixWord, tailWord_4880180, baseEnd_4880180] using wordTrace_append hprefix tailTrace_4880180
  have hstable : (prefixWord ++ tailWord_4880180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880180).length < 2 ^ (prefixWord ++ tailWord_4880180).sum := by decide
  have hdescent : baseEnd_4880180 < baseStart_4880180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880186 : List Nat := [3, 1, 1, 1, 5, 1, 2, 3, 6]
def baseStart_4880186 : Nat := 118140960795 + 4880186 * 2 ^ 59
def prefixEnd_4880186 : Nat := 4983230072969 + 3 ^ 40 * 4880186 * 2
def baseEnd_4880186 : Nat := 278431233482527609281271

theorem tailTrace_4880186 : CollatzResearch.WordTrace tailWord_4880186 prefixEnd_4880186 278431233482527609281271 := by
  unfold tailWord_4880186
  simp only [CollatzResearch.WordTrace]
  refine ⟨44498751574481766564505103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118663337531951377505346941 44498751574481766564505103)
  ·
    refine ⟨66748127361722649846757655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44498751574481766564505103 66748127361722649846757655)
    ·
      refine ⟨100122191042583974770136483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 66748127361722649846757655 100122191042583974770136483)
      ·
        refine ⟨150183286563875962155204725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100122191042583974770136483 150183286563875962155204725)
        ·
          refine ⟨14079683115363371452050443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 150183286563875962155204725 14079683115363371452050443)
          ·
            refine ⟨21119524673045057178075665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14079683115363371452050443 21119524673045057178075665)
            ·
              refine ⟨15839643504783792883556749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21119524673045057178075665 15839643504783792883556749)
              ·
                refine ⟨5939866314293922331333781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15839643504783792883556749 5939866314293922331333781)
                ·
                  refine ⟨278431233482527609281271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5939866314293922331333781 278431233482527609281271)
                  ·
                    rfl

theorem cell23_4880186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 2, 3, 6].length) (baseStart_4880186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880186 prefixEnd_4880186 := by exact prefixLift 4880186
  have htrace : WordTrace (prefixWord ++ tailWord_4880186) baseStart_4880186 baseEnd_4880186 := by
    simpa [prefixWord, tailWord_4880186, baseEnd_4880186] using wordTrace_append hprefix tailTrace_4880186
  have hstable : (prefixWord ++ tailWord_4880186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880186).length < 2 ^ (prefixWord ++ tailWord_4880186).sum := by decide
  have hdescent : baseEnd_4880186 < baseStart_4880186 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880220 : List Nat := [2, 2, 4, 2, 2, 2, 1, 2, 6]
def baseStart_4880220 : Nat := 118140960795 + 4880220 * 2 ^ 59
def prefixEnd_4880220 : Nat := 4983230072969 + 3 ^ 40 * 4880220 * 2
def baseEnd_4880220 : Nat := 278433173298333483389587

theorem tailTrace_4880220 : CollatzResearch.WordTrace tailWord_4880220 prefixEnd_4880220 278433173298333483389587 := by
  unfold tailWord_4880220
  simp only [CollatzResearch.WordTrace]
  refine ⟨88998123189901945032379057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118664164253202593376505409 88998123189901945032379057)
  ·
    refine ⟨66748592392426458774284293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 88998123189901945032379057 66748592392426458774284293)
    ·
      refine ⟨12515361073579961020178305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 66748592392426458774284293 12515361073579961020178305)
      ·
        refine ⟨9386520805184970765133729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12515361073579961020178305 9386520805184970765133729)
        ·
          refine ⟨7039890603888728073850297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9386520805184970765133729 7039890603888728073850297)
          ·
            refine ⟨5279917952916546055387723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7039890603888728073850297 5279917952916546055387723)
            ·
              refine ⟨7919876929374819083081585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5279917952916546055387723 7919876929374819083081585)
              ·
                refine ⟨5939907697031114312311189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7919876929374819083081585 5939907697031114312311189)
                ·
                  refine ⟨278433173298333483389587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5939907697031114312311189 278433173298333483389587)
                  ·
                    rfl

theorem cell23_4880220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 1, 2, 6].length) (baseStart_4880220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880220 prefixEnd_4880220 := by exact prefixLift 4880220
  have htrace : WordTrace (prefixWord ++ tailWord_4880220) baseStart_4880220 baseEnd_4880220 := by
    simpa [prefixWord, tailWord_4880220, baseEnd_4880220] using wordTrace_append hprefix tailTrace_4880220
  have hstable : (prefixWord ++ tailWord_4880220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880220).length < 2 ^ (prefixWord ++ tailWord_4880220).sum := by decide
  have hdescent : baseEnd_4880220 < baseStart_4880220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880264 : List Nat := [2, 1, 3, 3, 3, 2, 1, 3, 1, 1, 3]
def baseStart_4880264 : Nat := 118140960795 + 4880264 * 2 ^ 59
def prefixEnd_4880264 : Nat := 4983230072969 + 3 ^ 40 * 4880264 * 2
def baseEnd_4880264 : Nat := 2505921152833799178356081

theorem tailTrace_4880264 : CollatzResearch.WordTrace tailWord_4880264 prefixEnd_4880264 2505921152833799178356081 := by
  unfold tailWord_4880264
  simp only [CollatzResearch.WordTrace]
  refine ⟨88998925595822242789679923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118665234127762990386239897 88998925595822242789679923)
  ·
    refine ⟨133498388393733364184519885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 88998925595822242789679923 133498388393733364184519885)
    ·
      refine ⟨50061895647650011569194957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 133498388393733364184519885 50061895647650011569194957)
      ·
        refine ⟨18773210867868754338448109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50061895647650011569194957 18773210867868754338448109)
        ·
          refine ⟨7039954075450782876918041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18773210867868754338448109 7039954075450782876918041)
          ·
            refine ⟨5279965556588087157688531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7039954075450782876918041 5279965556588087157688531)
            ·
              refine ⟨7919948334882130736532797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5279965556588087157688531 7919948334882130736532797)
              ·
                refine ⟨2969980625580799026199799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7919948334882130736532797 2969980625580799026199799)
                ·
                  refine ⟨4454970938371198539299699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2969980625580799026199799 4454970938371198539299699)
                  ·
                    refine ⟨6682456407556797808949549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4454970938371198539299699 6682456407556797808949549)
                    ·
                      refine ⟨2505921152833799178356081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6682456407556797808949549 2505921152833799178356081)
                      ·
                        rfl

theorem cell23_4880264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_4880264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880264 prefixEnd_4880264 := by exact prefixLift 4880264
  have htrace : WordTrace (prefixWord ++ tailWord_4880264) baseStart_4880264 baseEnd_4880264 := by
    simpa [prefixWord, tailWord_4880264, baseEnd_4880264] using wordTrace_append hprefix tailTrace_4880264
  have hstable : (prefixWord ++ tailWord_4880264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880264).length < 2 ^ (prefixWord ++ tailWord_4880264).sum := by decide
  have hdescent : baseEnd_4880264 < baseStart_4880264 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880273 : List Nat := [1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 3]
def baseStart_4880273 : Nat := 118140960795 + 4880273 * 2 ^ 59
def prefixEnd_4880273 : Nat := 4983230072969 + 3 ^ 40 * 4880273 * 2
def baseEnd_4880273 : Nat := 2505925774159689643143539

theorem tailTrace_4880273 : CollatzResearch.WordTrace tailWord_4880273 prefixEnd_4880273 2505925774159689643143539 := by
  unfold tailWord_4880273
  simp only [CollatzResearch.WordTrace]
  refine ⟨177998179448611880116437473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 118665452965741253410958315 177998179448611880116437473)
  ·
    refine ⟨133498634586458910087328105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 177998179448611880116437473 133498634586458910087328105)
    ·
      refine ⟨100123975939844182565496079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 133498634586458910087328105 100123975939844182565496079)
      ·
        refine ⟨150185963909766273848244119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100123975939844182565496079 150185963909766273848244119)
        ·
          refine ⟨225278945864649410772366179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150185963909766273848244119 225278945864649410772366179)
          ·
            refine ⟨337918418796974116158549269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 225278945864649410772366179 337918418796974116158549269)
            ·
              refine ⟨15839925881108161694931997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 337918418796974116158549269 15839925881108161694931997)
              ·
                refine ⟨5939972205415560635599499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15839925881108161694931997 5939972205415560635599499)
                ·
                  refine ⟨8909958308123340953399249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5939972205415560635599499 8909958308123340953399249)
                  ·
                    refine ⟨6682468731092505715049437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8909958308123340953399249 6682468731092505715049437)
                    ·
                      refine ⟨2505925774159689643143539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6682468731092505715049437 2505925774159689643143539)
                      ·
                        rfl

theorem cell23_4880273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_4880273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880273 prefixEnd_4880273 := by exact prefixLift 4880273
  have htrace : WordTrace (prefixWord ++ tailWord_4880273) baseStart_4880273 baseEnd_4880273 := by
    simpa [prefixWord, tailWord_4880273, baseEnd_4880273] using wordTrace_append hprefix tailTrace_4880273
  have hstable : (prefixWord ++ tailWord_4880273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880273).length < 2 ^ (prefixWord ++ tailWord_4880273).sum := by decide
  have hdescent : baseEnd_4880273 < baseStart_4880273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880276 : List Nat := [2, 4, 2, 1, 1, 2, 11]
def baseStart_4880276 : Nat := 118140960795 + 4880276 * 2 ^ 59
def prefixEnd_4880276 : Nat := 4983230072969 + 3 ^ 40 * 4880276 * 2
def baseEnd_4880276 : Nat := 30937374254341396684025

theorem tailTrace_4880276 : CollatzResearch.WordTrace tailWord_4880276 prefixEnd_4880276 30937374254341396684025 := by
  unfold tailWord_4880276
  simp only [CollatzResearch.WordTrace]
  refine ⟨88999144433800505814398341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 118665525911734007752531121 88999144433800505814398341)
  ·
    refine ⟨16687339581337594840199689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 88999144433800505814398341 16687339581337594840199689)
    ·
      refine ⟨12515504686003196130149767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16687339581337594840199689 12515504686003196130149767)
      ·
        refine ⟨18773257029004794195224651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12515504686003196130149767 18773257029004794195224651)
        ·
          refine ⟨28159885543507191292836977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18773257029004794195224651 28159885543507191292836977)
          ·
            refine ⟨21119914157630393469627733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28159885543507191292836977 21119914157630393469627733)
            ·
              refine ⟨30937374254341396684025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 21119914157630393469627733 30937374254341396684025)
              ·
                rfl

theorem cell23_4880276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 11].length) (baseStart_4880276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880276 prefixEnd_4880276 := by exact prefixLift 4880276
  have htrace : WordTrace (prefixWord ++ tailWord_4880276) baseStart_4880276 baseEnd_4880276 := by
    simpa [prefixWord, tailWord_4880276, baseEnd_4880276] using wordTrace_append hprefix tailTrace_4880276
  have hstable : (prefixWord ++ tailWord_4880276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880276).length < 2 ^ (prefixWord ++ tailWord_4880276).sum := by decide
  have hdescent : baseEnd_4880276 < baseStart_4880276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880330 : List Nat := [3, 1, 2, 1, 2, 1, 2, 5, 1, 3, 2]
def baseStart_4880330 : Nat := 118140960795 + 4880330 * 2 ^ 59
def prefixEnd_4880330 : Nat := 4983230072969 + 3 ^ 40 * 4880330 * 2
def baseEnd_4880330 : Nat := 2505955042556995920130777

theorem tailTrace_4880330 : CollatzResearch.WordTrace tailWord_4880330 prefixEnd_4880330 2505955042556995920130777 := by
  unfold tailWord_4880330
  simp only [CollatzResearch.WordTrace]
  refine ⟨44500064602351344712815611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118666838939603585900841629 44500064602351344712815611)
  ·
    refine ⟨66750096903527017069223417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44500064602351344712815611 66750096903527017069223417)
    ·
      refine ⟨50062572677645262801917563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 66750096903527017069223417 50062572677645262801917563)
      ·
        refine ⟨75093859016467894202876345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50062572677645262801917563 75093859016467894202876345)
        ·
          refine ⟨56320394262350920652157259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75093859016467894202876345 56320394262350920652157259)
          ·
            refine ⟨84480591393526380978235889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56320394262350920652157259 84480591393526380978235889)
            ·
              refine ⟨63360443545144785733676917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84480591393526380978235889 63360443545144785733676917)
              ·
                refine ⟨5940041582357323662532211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63360443545144785733676917 5940041582357323662532211)
                ·
                  refine ⟨8910062373535985493798317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5940041582357323662532211 8910062373535985493798317)
                  ·
                    refine ⟨3341273390075994560174369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8910062373535985493798317 3341273390075994560174369)
                    ·
                      refine ⟨2505955042556995920130777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341273390075994560174369 2505955042556995920130777)
                      ·
                        rfl

theorem cell23_4880330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 5, 1, 3, 2].length) (baseStart_4880330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880330 prefixEnd_4880330 := by exact prefixLift 4880330
  have htrace : WordTrace (prefixWord ++ tailWord_4880330) baseStart_4880330 baseEnd_4880330 := by
    simpa [prefixWord, tailWord_4880330, baseEnd_4880330] using wordTrace_append hprefix tailTrace_4880330
  have hstable : (prefixWord ++ tailWord_4880330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880330).length < 2 ^ (prefixWord ++ tailWord_4880330).sum := by decide
  have hdescent : baseEnd_4880330 < baseStart_4880330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4880338 : List Nat := [3, 2, 2, 3, 2, 2, 2, 2, 1, 2, 2]
def baseStart_4880338 : Nat := 118140960795 + 4880338 * 2 ^ 59
def prefixEnd_4880338 : Nat := 4983230072969 + 3 ^ 40 * 4880338 * 2
def baseEnd_4880338 : Nat := 2505959150402231888830741

theorem tailTrace_4880338 : CollatzResearch.WordTrace tailWord_4880338 prefixEnd_4880338 2505959150402231888830741 := by
  unfold tailWord_4880338
  simp only [CollatzResearch.WordTrace]
  refine ⟨44500137548344099054388417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 118667033462250930811702445 44500137548344099054388417)
  ·
    refine ⟨33375103161258074290791313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44500137548344099054388417 33375103161258074290791313)
    ·
      refine ⟨25031327370943555718093485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33375103161258074290791313 25031327370943555718093485)
      ·
        refine ⟨9386747764103833394285057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25031327370943555718093485 9386747764103833394285057)
        ·
          refine ⟨7040060823077875045713793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9386747764103833394285057 7040060823077875045713793)
          ·
            refine ⟨5280045617308406284285345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7040060823077875045713793 5280045617308406284285345)
            ·
              refine ⟨3960034212981304713214009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5280045617308406284285345 3960034212981304713214009)
              ·
                refine ⟨2970025659735978534910507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3960034212981304713214009 2970025659735978534910507)
                ·
                  refine ⟨4455038489603967802365761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2970025659735978534910507 4455038489603967802365761)
                  ·
                    refine ⟨3341278867202975851774321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4455038489603967802365761 3341278867202975851774321)
                    ·
                      refine ⟨2505959150402231888830741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3341278867202975851774321 2505959150402231888830741)
                      ·
                        rfl

theorem cell23_4880338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_4880338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4880338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4880338 prefixEnd_4880338 := by exact prefixLift 4880338
  have htrace : WordTrace (prefixWord ++ tailWord_4880338) baseStart_4880338 baseEnd_4880338 := by
    simpa [prefixWord, tailWord_4880338, baseEnd_4880338] using wordTrace_append hprefix tailTrace_4880338
  have hstable : (prefixWord ++ tailWord_4880338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4880338).length < 2 ^ (prefixWord ++ tailWord_4880338).sum := by decide
  have hdescent : baseEnd_4880338 < baseStart_4880338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4880338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
