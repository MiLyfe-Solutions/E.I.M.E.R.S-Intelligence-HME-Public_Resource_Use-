import V185TrunkScan23Chunk0264

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1568086 : List Nat := [5, 2, 3, 1, 1, 2, 2, 1, 2, 2, 2]
def baseStart_1568086 : Nat := 118140960795 + 1568086 * 2 ^ 59
def prefixEnd_1568086 : Nat := 4983230072969 + 3 ^ 40 * 1568086 * 2
def baseEnd_1568086 : Nat := 805181825586257090013511

theorem tailTrace_1568086 : CollatzResearch.WordTrace tailWord_1568086 prefixEnd_1568086 805181825586257090013511 := by
  unfold tailWord_1568086
  simp only [CollatzResearch.WordTrace]
  refine ⟨3574549687318731538290257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38128529998066469741762741 3574549687318731538290257)
  ·
    refine ⟨2680912265489048653717693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3574549687318731538290257 2680912265489048653717693)
    ·
      refine ⟨1005342099558393245144135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2680912265489048653717693 1005342099558393245144135)
      ·
        refine ⟨1508013149337589867716203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1005342099558393245144135 1508013149337589867716203)
        ·
          refine ⟨2262019724006384801574305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1508013149337589867716203 2262019724006384801574305)
          ·
            refine ⟨1696514793004788601180729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2262019724006384801574305 1696514793004788601180729)
            ·
              refine ⟨1272386094753591450885547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1696514793004788601180729 1272386094753591450885547)
              ·
                refine ⟨1908579142130387176328321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272386094753591450885547 1908579142130387176328321)
                ·
                  refine ⟨1431434356597790382246241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1908579142130387176328321 1431434356597790382246241)
                  ·
                    refine ⟨1073575767448342786684681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1431434356597790382246241 1073575767448342786684681)
                    ·
                      refine ⟨805181825586257090013511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073575767448342786684681 805181825586257090013511)
                      ·
                        rfl

theorem cell23_1568086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_1568086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568086 prefixEnd_1568086 := by exact prefixLift 1568086
  have htrace : WordTrace (prefixWord ++ tailWord_1568086) baseStart_1568086 baseEnd_1568086 := by
    simpa [prefixWord, tailWord_1568086, baseEnd_1568086] using wordTrace_append hprefix tailTrace_1568086
  have hstable : (prefixWord ++ tailWord_1568086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568086).length < 2 ^ (prefixWord ++ tailWord_1568086).sum := by decide
  have hdescent : baseEnd_1568086 < baseStart_1568086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568120 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 3, 3, 7]
def baseStart_1568120 : Nat := 118140960795 + 1568120 * 2 ^ 59
def prefixEnd_1568120 : Nat := 4983230072969 + 3 ^ 40 * 1568120 * 2
def baseEnd_1568120 : Nat := 805199283928509956988353

theorem tailTrace_1568120 : CollatzResearch.WordTrace tailWord_1568120 prefixEnd_1568120 805199283928509956988353 := by
  unfold tailWord_1568120
  simp only [CollatzResearch.WordTrace]
  refine ⟨28597017539488264209690907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38129356719317685612921209 28597017539488264209690907)
  ·
    refine ⟨42895526309232396314536361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28597017539488264209690907 42895526309232396314536361)
    ·
      refine ⟨32171644731924297235902271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42895526309232396314536361 32171644731924297235902271)
      ·
        refine ⟨48257467097886445853853407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32171644731924297235902271 48257467097886445853853407)
        ·
          refine ⟨72386200646829668780780111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48257467097886445853853407 72386200646829668780780111)
          ·
            refine ⟨108579300970244503171170167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72386200646829668780780111 108579300970244503171170167)
            ·
              refine ⟨162868951455366754756755251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108579300970244503171170167 162868951455366754756755251)
              ·
                refine ⟨244303427183050132135132877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162868951455366754756755251 244303427183050132135132877)
                ·
                  refine ⟨91613785193643799550674829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 244303427183050132135132877 91613785193643799550674829)
                  ·
                    refine ⟨34355169447616424831503061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 91613785193643799550674829 34355169447616424831503061)
                    ·
                      refine ⟨805199283928509956988353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34355169447616424831503061 805199283928509956988353)
                      ·
                        rfl

theorem cell23_1568120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 3, 3, 7].length) (baseStart_1568120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568120 prefixEnd_1568120 := by exact prefixLift 1568120
  have htrace : WordTrace (prefixWord ++ tailWord_1568120) baseStart_1568120 baseEnd_1568120 := by
    simpa [prefixWord, tailWord_1568120, baseEnd_1568120] using wordTrace_append hprefix tailTrace_1568120
  have hstable : (prefixWord ++ tailWord_1568120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568120).length < 2 ^ (prefixWord ++ tailWord_1568120).sum := by decide
  have hdescent : baseEnd_1568120 < baseStart_1568120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568164 : List Nat := [2, 3, 1, 2, 1, 1, 1, 6, 1, 1, 4]
def baseStart_1568164 : Nat := 118140960795 + 1568164 * 2 ^ 59
def prefixEnd_1568164 : Nat := 4983230072969 + 3 ^ 40 * 1568164 * 2
def baseEnd_1568164 : Nat := 805221877077307784838151

theorem tailTrace_1568164 : CollatzResearch.WordTrace tailWord_1568164 prefixEnd_1568164 805221877077307784838151 := by
  unfold tailWord_1568164
  simp only [CollatzResearch.WordTrace]
  refine ⟨28597819945408561966991773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38130426593878082622655697 28597819945408561966991773)
  ·
    refine ⟨10724182479528210737621915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28597819945408561966991773 10724182479528210737621915)
    ·
      refine ⟨16086273719292316106432873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10724182479528210737621915 16086273719292316106432873)
      ·
        refine ⟨12064705289469237079824655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16086273719292316106432873 12064705289469237079824655)
        ·
          refine ⟨18097057934203855619736983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12064705289469237079824655 18097057934203855619736983)
          ·
            refine ⟨27145586901305783429605475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18097057934203855619736983 27145586901305783429605475)
            ·
              refine ⟨40718380351958675144408213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27145586901305783429605475 40718380351958675144408213)
              ·
                refine ⟨1908674078998062897394135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 40718380351958675144408213 1908674078998062897394135)
                ·
                  refine ⟨2863011118497094346091203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1908674078998062897394135 2863011118497094346091203)
                  ·
                    refine ⟨4294516677745641519136805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2863011118497094346091203 4294516677745641519136805)
                    ·
                      refine ⟨805221877077307784838151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4294516677745641519136805 805221877077307784838151)
                      ·
                        rfl

theorem cell23_1568164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_1568164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568164 prefixEnd_1568164 := by exact prefixLift 1568164
  have htrace : WordTrace (prefixWord ++ tailWord_1568164) baseStart_1568164 baseEnd_1568164 := by
    simpa [prefixWord, tailWord_1568164, baseEnd_1568164] using wordTrace_append hprefix tailTrace_1568164
  have hstable : (prefixWord ++ tailWord_1568164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568164).length < 2 ^ (prefixWord ++ tailWord_1568164).sum := by decide
  have hdescent : baseEnd_1568164 < baseStart_1568164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568168 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 1, 5, 2]
def baseStart_1568168 : Nat := 118140960795 + 1568168 * 2 ^ 59
def prefixEnd_1568168 : Nat := 4983230072969 + 3 ^ 40 * 1568168 * 2
def baseEnd_1568168 : Nat := 805223930999925769188133

theorem tailTrace_1568168 : CollatzResearch.WordTrace tailWord_1568168 prefixEnd_1568168 805223930999925769188133 := by
  unfold tailWord_1568168
  simp only [CollatzResearch.WordTrace]
  refine ⟨28597892891401316308564579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38130523855201755078086105 28597892891401316308564579)
  ·
    refine ⟨42896839337101974462846869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28597892891401316308564579 42896839337101974462846869)
    ·
      refine ⟨2010789343926655052945947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 42896839337101974462846869 2010789343926655052945947)
      ·
        refine ⟨3016184015889982579418921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2010789343926655052945947 3016184015889982579418921)
        ·
          refine ⟨2262138011917486934564191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3016184015889982579418921 2262138011917486934564191)
          ·
            refine ⟨3393207017876230401846287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262138011917486934564191 3393207017876230401846287)
            ·
              refine ⟨5089810526814345602769431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393207017876230401846287 5089810526814345602769431)
              ·
                refine ⟨7634715790221518404154147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5089810526814345602769431 7634715790221518404154147)
                ·
                  refine ⟨11452073685332277606231221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7634715790221518404154147 11452073685332277606231221)
                  ·
                    refine ⟨1073631907999901025584177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11452073685332277606231221 1073631907999901025584177)
                    ·
                      refine ⟨805223930999925769188133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073631907999901025584177 805223930999925769188133)
                      ·
                        rfl

theorem cell23_1568168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_1568168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568168 prefixEnd_1568168 := by exact prefixLift 1568168
  have htrace : WordTrace (prefixWord ++ tailWord_1568168) baseStart_1568168 baseEnd_1568168 := by
    simpa [prefixWord, tailWord_1568168, baseEnd_1568168] using wordTrace_append hprefix tailTrace_1568168
  have hstable : (prefixWord ++ tailWord_1568168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568168).length < 2 ^ (prefixWord ++ tailWord_1568168).sum := by decide
  have hdescent : baseEnd_1568168 < baseStart_1568168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568181 : List Nat := [1, 3, 3, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_1568181 : Nat := 118140960795 + 1568181 * 2 ^ 59
def prefixEnd_1568181 : Nat := 4983230072969 + 3 ^ 40 * 1568181 * 2
def baseEnd_1568181 : Nat := 805230606248434218325573

theorem tailTrace_1568181 : CollatzResearch.WordTrace tailWord_1568181 prefixEnd_1568181 805230606248434218325573 := by
  unfold tailWord_1568181
  simp only [CollatzResearch.WordTrace]
  refine ⟨57196259931755535837352397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38130839954503690558234931 57196259931755535837352397)
  ·
    refine ⟨21448597474408325939007149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57196259931755535837352397 21448597474408325939007149)
    ·
      refine ⟨8043224052903122227127681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21448597474408325939007149 8043224052903122227127681)
      ·
        refine ⟨6032418039677341670345761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8043224052903122227127681 6032418039677341670345761)
        ·
          refine ⟨4524313529758006252759321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6032418039677341670345761 4524313529758006252759321)
          ·
            refine ⟨3393235147318504689569491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4524313529758006252759321 3393235147318504689569491)
            ·
              refine ⟨5089852720977757034354237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393235147318504689569491 5089852720977757034354237)
              ·
                refine ⟨1908694770366658887882839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5089852720977757034354237 1908694770366658887882839)
                ·
                  refine ⟨2863042155549988331824259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1908694770366658887882839 2863042155549988331824259)
                  ·
                    refine ⟨4294563233324982497736389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2863042155549988331824259 4294563233324982497736389)
                    ·
                      refine ⟨805230606248434218325573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4294563233324982497736389 805230606248434218325573)
                      ·
                        rfl

theorem cell23_1568181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_1568181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568181 prefixEnd_1568181 := by exact prefixLift 1568181
  have htrace : WordTrace (prefixWord ++ tailWord_1568181) baseStart_1568181 baseEnd_1568181 := by
    simpa [prefixWord, tailWord_1568181, baseEnd_1568181] using wordTrace_append hprefix tailTrace_1568181
  have hstable : (prefixWord ++ tailWord_1568181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568181).length < 2 ^ (prefixWord ++ tailWord_1568181).sum := by decide
  have hdescent : baseEnd_1568181 < baseStart_1568181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568197 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 1, 9, 3]
def baseStart_1568197 : Nat := 118140960795 + 1568197 * 2 ^ 59
def prefixEnd_1568197 : Nat := 4983230072969 + 3 ^ 40 * 1568197 * 2
def baseEnd_1568197 : Nat := 805238821938906155725499

theorem tailTrace_1568197 : CollatzResearch.WordTrace tailWord_1568197 prefixEnd_1568197 805238821938906155725499 := by
  unfold tailWord_1568197
  simp only [CollatzResearch.WordTrace]
  refine ⟨57196843499697570569934845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38131228999798380379956563 57196843499697570569934845)
  ·
    refine ⟨21448816312386588963725567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57196843499697570569934845 21448816312386588963725567)
    ·
      refine ⟨32173224468579883445588351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21448816312386588963725567 32173224468579883445588351)
      ·
        refine ⟨48259836702869825168382527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32173224468579883445588351 48259836702869825168382527)
        ·
          refine ⟨72389755054304737752573791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48259836702869825168382527 72389755054304737752573791)
          ·
            refine ⟨108584632581457106628860687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72389755054304737752573791 108584632581457106628860687)
            ·
              refine ⟨162876948872185659943291031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108584632581457106628860687 162876948872185659943291031)
              ·
                refine ⟨244315423308278489914936547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 162876948872185659943291031 244315423308278489914936547)
                ·
                  refine ⟨366473134962417734872404821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244315423308278489914936547 366473134962417734872404821)
                  ·
                    refine ⟨2147303525170416415267997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 366473134962417734872404821 2147303525170416415267997)
                    ·
                      refine ⟨805238821938906155725499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2147303525170416415267997 805238821938906155725499)
                      ·
                        rfl

theorem cell23_1568197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_1568197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568197 prefixEnd_1568197 := by exact prefixLift 1568197
  have htrace : WordTrace (prefixWord ++ tailWord_1568197) baseStart_1568197 baseEnd_1568197 := by
    simpa [prefixWord, tailWord_1568197, baseEnd_1568197] using wordTrace_append hprefix tailTrace_1568197
  have hstable : (prefixWord ++ tailWord_1568197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568197).length < 2 ^ (prefixWord ++ tailWord_1568197).sum := by decide
  have hdescent : baseEnd_1568197 < baseStart_1568197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568221 : List Nat := [1, 4, 3, 1, 1, 4, 2, 7]
def baseStart_1568221 : Nat := 118140960795 + 1568221 * 2 ^ 59
def prefixEnd_1568221 : Nat := 4983230072969 + 3 ^ 40 * 1568221 * 2
def baseEnd_1568221 : Nat := 29824116499059780067607

theorem tailTrace_1568221 : CollatzResearch.WordTrace tailWord_1568221 prefixEnd_1568221 29824116499059780067607 := by
  unfold tailWord_1568221
  simp only [CollatzResearch.WordTrace]
  refine ⟨57197718851610622668808517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38131812567740415112539011 57197718851610622668808517)
  ·
    refine ⟨10724572284676991750401597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57197718851610622668808517 10724572284676991750401597)
    ·
      refine ⟨4021714606753871906400599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10724572284676991750401597 4021714606753871906400599)
      ·
        refine ⟨6032571910130807859600899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4021714606753871906400599 6032571910130807859600899)
        ·
          refine ⟨9048857865196211789401349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032571910130807859600899 9048857865196211789401349)
          ·
            refine ⟨1696660849724289710512753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9048857865196211789401349 1696660849724289710512753)
            ·
              refine ⟨1272495637293217282884565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1696660849724289710512753 1272495637293217282884565)
              ·
                refine ⟨29824116499059780067607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1272495637293217282884565 29824116499059780067607)
                ·
                  rfl

theorem cell23_1568221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 2, 7].length) (baseStart_1568221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568221 prefixEnd_1568221 := by exact prefixLift 1568221
  have htrace : WordTrace (prefixWord ++ tailWord_1568221) baseStart_1568221 baseEnd_1568221 := by
    simpa [prefixWord, tailWord_1568221, baseEnd_1568221] using wordTrace_append hprefix tailTrace_1568221
  have hstable : (prefixWord ++ tailWord_1568221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568221).length < 2 ^ (prefixWord ++ tailWord_1568221).sum := by decide
  have hdescent : baseEnd_1568221 < baseStart_1568221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568231 : List Nat := [1, 1, 5, 2, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1568231 : Nat := 118140960795 + 1568231 * 2 ^ 59
def prefixEnd_1568231 : Nat := 4983230072969 + 3 ^ 40 * 1568231 * 2
def baseEnd_1568231 : Nat := 805256280281159022700343

theorem tailTrace_1568231 : CollatzResearch.WordTrace tailWord_1568231 prefixEnd_1568231 805256280281159022700343 := by
  unfold tailWord_1568231
  simp only [CollatzResearch.WordTrace]
  refine ⟨57198083581574394376672547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38132055721049596251115031 57198083581574394376672547)
  ·
    refine ⟨85797125372361591565008821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57198083581574394376672547 85797125372361591565008821)
    ·
      refine ⟨8043480503658899209219577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 85797125372361591565008821 8043480503658899209219577)
      ·
        refine ⟨6032610377744174406914683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8043480503658899209219577 6032610377744174406914683)
        ·
          refine ⟨9048915566616261610372025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032610377744174406914683 9048915566616261610372025)
          ·
            refine ⟨6786686674962196207779019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9048915566616261610372025 6786686674962196207779019)
            ·
              refine ⟨10180030012443294311668529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6786686674962196207779019 10180030012443294311668529)
              ·
                refine ⟨7635022509332470733751397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10180030012443294311668529 7635022509332470733751397)
                ·
                  refine ⟨1431566720499838262578387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7635022509332470733751397 1431566720499838262578387)
                  ·
                    refine ⟨2147350080749757393867581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1431566720499838262578387 2147350080749757393867581)
                    ·
                      refine ⟨805256280281159022700343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2147350080749757393867581 805256280281159022700343)
                      ·
                        rfl

theorem cell23_1568231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1568231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568231 prefixEnd_1568231 := by exact prefixLift 1568231
  have htrace : WordTrace (prefixWord ++ tailWord_1568231) baseStart_1568231 baseEnd_1568231 := by
    simpa [prefixWord, tailWord_1568231, baseEnd_1568231] using wordTrace_append hprefix tailTrace_1568231
  have hstable : (prefixWord ++ tailWord_1568231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568231).length < 2 ^ (prefixWord ++ tailWord_1568231).sum := by decide
  have hdescent : baseEnd_1568231 < baseStart_1568231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568247 : List Nat := [1, 1, 3, 1, 1, 1, 1, 6, 2, 6]
def baseStart_1568247 : Nat := 118140960795 + 1568247 * 2 ^ 59
def prefixEnd_1568247 : Nat := 4983230072969 + 3 ^ 40 * 1568247 * 2
def baseEnd_1568247 : Nat := 268421498657210320033423

theorem tailTrace_1568247 : CollatzResearch.WordTrace tailWord_1568247 prefixEnd_1568247 268421498657210320033423 := by
  unfold tailWord_1568247
  simp only [CollatzResearch.WordTrace]
  refine ⟨57198667149516429109254995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38132444766344286072836663 57198667149516429109254995)
  ·
    refine ⟨85798000724274643663882493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57198667149516429109254995 85798000724274643663882493)
    ·
      refine ⟨32174250271602991373955935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85798000724274643663882493 32174250271602991373955935)
      ·
        refine ⟨48261375407404487060933903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32174250271602991373955935 48261375407404487060933903)
        ·
          refine ⟨72392063111106730591400855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48261375407404487060933903 72392063111106730591400855)
          ·
            refine ⟨108588094666660095887101283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72392063111106730591400855 108588094666660095887101283)
            ·
              refine ⟨162882141999990143830651925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108588094666660095887101283 162882141999990143830651925)
              ·
                refine ⟨7635100406249537992061809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 162882141999990143830651925 7635100406249537992061809)
                ·
                  refine ⟨5726325304687153494046357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7635100406249537992061809 5726325304687153494046357)
                  ·
                    refine ⟨268421498657210320033423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5726325304687153494046357 268421498657210320033423)
                    ·
                      rfl

theorem cell23_1568247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_1568247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568247 prefixEnd_1568247 := by exact prefixLift 1568247
  have htrace : WordTrace (prefixWord ++ tailWord_1568247) baseStart_1568247 baseEnd_1568247 := by
    simpa [prefixWord, tailWord_1568247, baseEnd_1568247] using wordTrace_append hprefix tailTrace_1568247
  have hstable : (prefixWord ++ tailWord_1568247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568247).length < 2 ^ (prefixWord ++ tailWord_1568247).sum := by decide
  have hdescent : baseEnd_1568247 < baseStart_1568247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568269 : List Nat := [1, 7, 1, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_1568269 : Nat := 118140960795 + 1568269 * 2 ^ 59
def prefixEnd_1568269 : Nat := 4983230072969 + 3 ^ 40 * 1568269 * 2
def baseEnd_1568269 : Nat := 805275792546029874025169

theorem tailTrace_1568269 : CollatzResearch.WordTrace tailWord_1568269 prefixEnd_1568269 805275792546029874025169 := by
  unfold tailWord_1568269
  simp only [CollatzResearch.WordTrace]
  refine ⟨57199469555436726866555861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38132979703624484577703907 57199469555436726866555861)
  ·
    refine ⟨1340612567705548285934903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 57199469555436726866555861 1340612567705548285934903)
    ·
      refine ⟨2010918851558322428902355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1340612567705548285934903 2010918851558322428902355)
      ·
        refine ⟨3016378277337483643353533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2010918851558322428902355 3016378277337483643353533)
        ·
          refine ⟨1131141854001556366257575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3016378277337483643353533 1131141854001556366257575)
          ·
            refine ⟨1696712781002334549386363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131141854001556366257575 1696712781002334549386363)
            ·
              refine ⟨2545069171503501824079545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1696712781002334549386363 2545069171503501824079545)
              ·
                refine ⟨1908801878627626368059659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2545069171503501824079545 1908801878627626368059659)
                ·
                  refine ⟨2863202817941439552089489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1908801878627626368059659 2863202817941439552089489)
                  ·
                    refine ⟨2147402113456079664067117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2863202817941439552089489 2147402113456079664067117)
                    ·
                      refine ⟨805275792546029874025169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2147402113456079664067117 805275792546029874025169)
                      ·
                        rfl

theorem cell23_1568269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_1568269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568269 prefixEnd_1568269 := by exact prefixLift 1568269
  have htrace : WordTrace (prefixWord ++ tailWord_1568269) baseStart_1568269 baseEnd_1568269 := by
    simpa [prefixWord, tailWord_1568269, baseEnd_1568269] using wordTrace_append hprefix tailTrace_1568269
  have hstable : (prefixWord ++ tailWord_1568269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568269).length < 2 ^ (prefixWord ++ tailWord_1568269).sum := by decide
  have hdescent : baseEnd_1568269 < baseStart_1568269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568288 : List Nat := [2, 1, 1, 6, 1, 2, 1, 2, 1, 4, 2]
def baseStart_1568288 : Nat := 118140960795 + 1568288 * 2 ^ 59
def prefixEnd_1568288 : Nat := 4983230072969 + 3 ^ 40 * 1568288 * 2
def baseEnd_1568288 : Nat := 805285548678465299687581

theorem tailTrace_1568288 : CollatzResearch.WordTrace tailWord_1568288 prefixEnd_1568288 805285548678465299687581 := by
  unfold tailWord_1568288
  simp only [CollatzResearch.WordTrace]
  refine ⟨28600081271183946555748759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38133441694911928740998345 28600081271183946555748759)
  ·
    refine ⟨42900121906775919833623139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28600081271183946555748759 42900121906775919833623139)
    ·
      refine ⟨64350182860163879750434709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42900121906775919833623139 64350182860163879750434709)
      ·
        refine ⟨3016414821570181863301627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 64350182860163879750434709 3016414821570181863301627)
        ·
          refine ⟨4524622232355272794952441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3016414821570181863301627 4524622232355272794952441)
          ·
            refine ⟨3393466674266454596214331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4524622232355272794952441 3393466674266454596214331)
            ·
              refine ⟨5090200011399681894321497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393466674266454596214331 5090200011399681894321497)
              ·
                refine ⟨3817650008549761420741123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5090200011399681894321497 3817650008549761420741123)
                ·
                  refine ⟨5726475012824642131111685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3817650008549761420741123 5726475012824642131111685)
                  ·
                    refine ⟨1073714064904620399583441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5726475012824642131111685 1073714064904620399583441)
                    ·
                      refine ⟨805285548678465299687581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073714064904620399583441 805285548678465299687581)
                      ·
                        rfl

theorem cell23_1568288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_1568288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568288 prefixEnd_1568288 := by exact prefixLift 1568288
  have htrace : WordTrace (prefixWord ++ tailWord_1568288) baseStart_1568288 baseEnd_1568288 := by
    simpa [prefixWord, tailWord_1568288, baseEnd_1568288] using wordTrace_append hprefix tailTrace_1568288
  have hstable : (prefixWord ++ tailWord_1568288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568288).length < 2 ^ (prefixWord ++ tailWord_1568288).sum := by decide
  have hdescent : baseEnd_1568288 < baseStart_1568288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568304 : List Nat := [2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 3]
def baseStart_1568304 : Nat := 118140960795 + 1568304 * 2 ^ 59
def prefixEnd_1568304 : Nat := 4983230072969 + 3 ^ 40 * 1568304 * 2
def baseEnd_1568304 : Nat := 805293764368937237087507

theorem tailTrace_1568304 : CollatzResearch.WordTrace tailWord_1568304 prefixEnd_1568304 805293764368937237087507 := by
  unfold tailWord_1568304
  simp only [CollatzResearch.WordTrace]
  refine ⟨28600373055154963922039983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38133830740206618562719977 28600373055154963922039983)
  ·
    refine ⟨42900559582732445883059975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28600373055154963922039983 42900559582732445883059975)
    ·
      refine ⟨64350839374098668824589963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42900559582732445883059975 64350839374098668824589963)
      ·
        refine ⟨96526259061148003236884945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64350839374098668824589963 96526259061148003236884945)
        ·
          refine ⟨72394694295861002427663709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96526259061148003236884945 72394694295861002427663709)
          ·
            refine ⟨27148010360947875910373891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72394694295861002427663709 27148010360947875910373891)
            ·
              refine ⟨40722015541421813865560837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27148010360947875910373891 40722015541421813865560837)
              ·
                refine ⟨7635377914016590099792657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40722015541421813865560837 7635377914016590099792657)
                ·
                  refine ⟨5726533435512442574844493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7635377914016590099792657 5726533435512442574844493)
                  ·
                    refine ⟨2147450038317165965566685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5726533435512442574844493 2147450038317165965566685)
                    ·
                      refine ⟨805293764368937237087507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2147450038317165965566685 805293764368937237087507)
                      ·
                        rfl

theorem cell23_1568304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 4, 2, 3, 3].length) (baseStart_1568304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568304 prefixEnd_1568304 := by exact prefixLift 1568304
  have htrace : WordTrace (prefixWord ++ tailWord_1568304) baseStart_1568304 baseEnd_1568304 := by
    simpa [prefixWord, tailWord_1568304, baseEnd_1568304] using wordTrace_append hprefix tailTrace_1568304
  have hstable : (prefixWord ++ tailWord_1568304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568304).length < 2 ^ (prefixWord ++ tailWord_1568304).sum := by decide
  have hdescent : baseEnd_1568304 < baseStart_1568304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568311 : List Nat := [1, 1, 3, 1, 2, 5, 1, 4, 5]
def baseStart_1568311 : Nat := 118140960795 + 1568311 * 2 ^ 59
def prefixEnd_1568311 : Nat := 4983230072969 + 3 ^ 40 * 1568311 * 2
def baseEnd_1568311 : Nat := 89477484303724301077775

theorem tailTrace_1568311 : CollatzResearch.WordTrace tailWord_1568311 prefixEnd_1568311 89477484303724301077775 := by
  unfold tailWord_1568311
  simp only [CollatzResearch.WordTrace]
  refine ⟨57201001421284568039584787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38134000947523045359723191 57201001421284568039584787)
  ·
    refine ⟨85801502131926852059377181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57201001421284568039584787 85801502131926852059377181)
    ·
      refine ⟨32175563299472569522266443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85801502131926852059377181 32175563299472569522266443)
      ·
        refine ⟨48263344949208854283399665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32175563299472569522266443 48263344949208854283399665)
        ·
          refine ⟨36197508711906640712549749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48263344949208854283399665 36197508711906640712549749)
          ·
            refine ⟨3393516441741247566801539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36197508711906640712549749 3393516441741247566801539)
            ·
              refine ⟨5090274662611871350202309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393516441741247566801539 5090274662611871350202309)
              ·
                refine ⟨954426499239725878162933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5090274662611871350202309 954426499239725878162933)
                ·
                  refine ⟨89477484303724301077775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 954426499239725878162933 89477484303724301077775)
                  ·
                    rfl

theorem cell23_1568311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 4, 5].length) (baseStart_1568311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568311 prefixEnd_1568311 := by exact prefixLift 1568311
  have htrace : WordTrace (prefixWord ++ tailWord_1568311) baseStart_1568311 baseEnd_1568311 := by
    simpa [prefixWord, tailWord_1568311, baseEnd_1568311] using wordTrace_append hprefix tailTrace_1568311
  have hstable : (prefixWord ++ tailWord_1568311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568311).length < 2 ^ (prefixWord ++ tailWord_1568311).sum := by decide
  have hdescent : baseEnd_1568311 < baseStart_1568311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568321 : List Nat := [1, 2, 5, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1568321 : Nat := 118140960795 + 1568321 * 2 ^ 59
def prefixEnd_1568321 : Nat := 4983230072969 + 3 ^ 40 * 1568321 * 2
def baseEnd_1568321 : Nat := 805302493540063670574929

theorem tailTrace_1568321 : CollatzResearch.WordTrace tailWord_1568321 prefixEnd_1568321 805302493540063670574929 := by
  unfold tailWord_1568321
  simp only [CollatzResearch.WordTrace]
  refine ⟨57201366151248339747448817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38134244100832226498299211 57201366151248339747448817)
  ·
    refine ⟨42901024613436254810586613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57201366151248339747448817 42901024613436254810586613)
    ·
      refine ⟨4021971057509648888492495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 42901024613436254810586613 4021971057509648888492495)
      ·
        refine ⟨6032956586264473332738743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4021971057509648888492495 6032956586264473332738743)
        ·
          refine ⟨9049434879396709999108115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6032956586264473332738743 9049434879396709999108115)
          ·
            refine ⟨13574152319095064998662173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9049434879396709999108115 13574152319095064998662173)
            ·
              refine ⟨5090307119660649374498315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13574152319095064998662173 5090307119660649374498315)
              ·
                refine ⟨7635460679490974061747473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5090307119660649374498315 7635460679490974061747473)
                ·
                  refine ⟨5726595509618230546310605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7635460679490974061747473 5726595509618230546310605)
                  ·
                    refine ⟨2147473316106836454866477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5726595509618230546310605 2147473316106836454866477)
                    ·
                      refine ⟨805302493540063670574929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2147473316106836454866477 805302493540063670574929)
                      ·
                        rfl

theorem cell23_1568321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1568321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568321 prefixEnd_1568321 := by exact prefixLift 1568321
  have htrace : WordTrace (prefixWord ++ tailWord_1568321) baseStart_1568321 baseEnd_1568321 := by
    simpa [prefixWord, tailWord_1568321, baseEnd_1568321] using wordTrace_append hprefix tailTrace_1568321
  have hstable : (prefixWord ++ tailWord_1568321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568321).length < 2 ^ (prefixWord ++ tailWord_1568321).sum := by decide
  have hdescent : baseEnd_1568321 < baseStart_1568321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568361 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 2, 4, 2]
def baseStart_1568361 : Nat := 118140960795 + 1568361 * 2 ^ 59
def prefixEnd_1568361 : Nat := 4983230072969 + 3 ^ 40 * 1568361 * 2
def baseEnd_1568361 : Nat := 805323032766243514074745

theorem tailTrace_1568361 : CollatzResearch.WordTrace tailWord_1568361 prefixEnd_1568361 805323032766243514074745 := by
  unfold tailWord_1568361
  simp only [CollatzResearch.WordTrace]
  refine ⟨57202825071103426578904937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38135216714068951052603291 57202825071103426578904937)
  ·
    refine ⟨42902118803327569934178703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57202825071103426578904937 42902118803327569934178703)
    ·
      refine ⟨64353178204991354901268055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42902118803327569934178703 64353178204991354901268055)
      ·
        refine ⟨96529767307487032351902083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64353178204991354901268055 96529767307487032351902083)
        ·
          refine ⟨144794650961230548527853125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96529767307487032351902083 144794650961230548527853125)
          ·
            refine ⟨27148997055230727848972461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144794650961230548527853125 27148997055230727848972461)
            ·
              refine ⟨10180873895711522943364673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27148997055230727848972461 10180873895711522943364673)
              ·
                refine ⟨7635655421783642207523505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10180873895711522943364673 7635655421783642207523505)
                ·
                  refine ⟨5726741566337731655642629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7635655421783642207523505 5726741566337731655642629)
                  ·
                    refine ⟨1073764043688324685432993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5726741566337731655642629 1073764043688324685432993)
                    ·
                      refine ⟨805323032766243514074745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073764043688324685432993 805323032766243514074745)
                      ·
                        rfl

theorem cell23_1568361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 4, 2].length) (baseStart_1568361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568361 prefixEnd_1568361 := by exact prefixLift 1568361
  have htrace : WordTrace (prefixWord ++ tailWord_1568361) baseStart_1568361 baseEnd_1568361 := by
    simpa [prefixWord, tailWord_1568361, baseEnd_1568361] using wordTrace_append hprefix tailTrace_1568361
  have hstable : (prefixWord ++ tailWord_1568361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568361).length < 2 ^ (prefixWord ++ tailWord_1568361).sum := by decide
  have hdescent : baseEnd_1568361 < baseStart_1568361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568381 : List Nat := [1, 4, 1, 1, 4, 1, 1, 2, 1, 4, 3]
def baseStart_1568381 : Nat := 118140960795 + 1568381 * 2 ^ 59
def prefixEnd_1568381 : Nat := 4983230072969 + 3 ^ 40 * 1568381 * 2
def baseEnd_1568381 : Nat := 805333302379333435824653

theorem tailTrace_1568381 : CollatzResearch.WordTrace tailWord_1568381 prefixEnd_1568381 805333302379333435824653 := by
  unfold tailWord_1568381
  simp only [CollatzResearch.WordTrace]
  refine ⟨57203554531030969994632997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38135703020687313329755331 57203554531030969994632997)
  ·
    refine ⟨10725666474568306873993687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57203554531030969994632997 10725666474568306873993687)
    ·
      refine ⟨16088499711852460310990531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10725666474568306873993687 16088499711852460310990531)
      ·
        refine ⟨24132749567778690466485797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16088499711852460310990531 24132749567778690466485797)
        ·
          refine ⟨4524890543958504462466087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24132749567778690466485797 4524890543958504462466087)
          ·
            refine ⟨6787335815937756693699131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4524890543958504462466087 6787335815937756693699131)
            ·
              refine ⟨10181003723906635040548697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6787335815937756693699131 10181003723906635040548697)
              ·
                refine ⟨7635752792929976280411523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10181003723906635040548697 7635752792929976280411523)
                ·
                  refine ⟨11453629189394964420617285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7635752792929976280411523 11453629189394964420617285)
                  ·
                    refine ⟨2147555473011555828865741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11453629189394964420617285 2147555473011555828865741)
                    ·
                      refine ⟨805333302379333435824653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2147555473011555828865741 805333302379333435824653)
                      ·
                        rfl

theorem cell23_1568381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_1568381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568381 prefixEnd_1568381 := by exact prefixLift 1568381
  have htrace : WordTrace (prefixWord ++ tailWord_1568381) baseStart_1568381 baseEnd_1568381 := by
    simpa [prefixWord, tailWord_1568381, baseEnd_1568381] using wordTrace_append hprefix tailTrace_1568381
  have hstable : (prefixWord ++ tailWord_1568381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568381).length < 2 ^ (prefixWord ++ tailWord_1568381).sum := by decide
  have hdescent : baseEnd_1568381 < baseStart_1568381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568415 : List Nat := [1, 1, 2, 7, 1, 1, 1, 2, 2, 2, 3]
def baseStart_1568415 : Nat := 118140960795 + 1568415 * 2 ^ 59
def prefixEnd_1568415 : Nat := 4983230072969 + 3 ^ 40 * 1568415 * 2
def baseEnd_1568415 : Nat := 805350760721586302799497

theorem tailTrace_1568415 : CollatzResearch.WordTrace tailWord_1568415 prefixEnd_1568415 805350760721586302799497 := by
  unfold tailWord_1568415
  simp only [CollatzResearch.WordTrace]
  refine ⟨57204794612907793801370699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38136529741938529200913799 57204794612907793801370699)
  ·
    refine ⟨85807191919361690702056049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57204794612907793801370699 85807191919361690702056049)
    ·
      refine ⟨64355393939521268026542037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85807191919361690702056049 64355393939521268026542037)
      ·
        refine ⟨1508329545457529719372079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 64355393939521268026542037 1508329545457529719372079)
        ·
          refine ⟨2262494318186294579058119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1508329545457529719372079 2262494318186294579058119)
          ·
            refine ⟨3393741477279441868587179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262494318186294579058119 3393741477279441868587179)
            ·
              refine ⟨5090612215919162802880769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393741477279441868587179 5090612215919162802880769)
              ·
                refine ⟨3817959161939372102160577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5090612215919162802880769 3817959161939372102160577)
                ·
                  refine ⟨2863469371454529076620433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3817959161939372102160577 2863469371454529076620433)
                  ·
                    refine ⟨2147602028590896807465325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2863469371454529076620433 2147602028590896807465325)
                    ·
                      refine ⟨805350760721586302799497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2147602028590896807465325 805350760721586302799497)
                      ·
                        rfl

theorem cell23_1568415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_1568415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568415 prefixEnd_1568415 := by exact prefixLift 1568415
  have htrace : WordTrace (prefixWord ++ tailWord_1568415) baseStart_1568415 baseEnd_1568415 := by
    simpa [prefixWord, tailWord_1568415, baseEnd_1568415] using wordTrace_append hprefix tailTrace_1568415
  have hstable : (prefixWord ++ tailWord_1568415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568415).length < 2 ^ (prefixWord ++ tailWord_1568415).sum := by decide
  have hdescent : baseEnd_1568415 < baseStart_1568415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568464 : List Nat := [2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 6]
def baseStart_1568464 : Nat := 118140960795 + 1568464 * 2 ^ 59
def prefixEnd_1568464 : Nat := 4983230072969 + 3 ^ 40 * 1568464 * 2
def baseEnd_1568464 : Nat := 805375921273656611086771

theorem tailTrace_1568464 : CollatzResearch.WordTrace tailWord_1568464 prefixEnd_1568464 805375921273656611086771 := by
  unfold tailWord_1568464
  simp only [CollatzResearch.WordTrace]
  refine ⟨28603290894865137584952223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38137721193153516779936297 28603290894865137584952223)
  ·
    refine ⟨42904936342297706377428335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28603290894865137584952223 42904936342297706377428335)
    ·
      refine ⟨64357404513446559566142503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42904936342297706377428335 64357404513446559566142503)
      ·
        refine ⟨96536106770169839349213755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64357404513446559566142503 96536106770169839349213755)
        ·
          refine ⟨144804160155254759023820633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96536106770169839349213755 144804160155254759023820633)
          ·
            refine ⟨108603120116441069267865475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144804160155254759023820633 108603120116441069267865475)
            ·
              refine ⟨162904680174661603901798213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108603120116441069267865475 162904680174661603901798213)
              ·
                refine ⟨30544627532749050731587165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 162904680174661603901798213 30544627532749050731587165)
                ·
                  refine ⟨11454235324780894024345187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30544627532749050731587165 11454235324780894024345187)
                  ·
                    refine ⟨17181352987171341036517781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11454235324780894024345187 17181352987171341036517781)
                    ·
                      refine ⟨805375921273656611086771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17181352987171341036517781 805375921273656611086771)
                      ·
                        rfl

theorem cell23_1568464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 6].length) (baseStart_1568464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568464 prefixEnd_1568464 := by exact prefixLift 1568464
  have htrace : WordTrace (prefixWord ++ tailWord_1568464) baseStart_1568464 baseEnd_1568464 := by
    simpa [prefixWord, tailWord_1568464, baseEnd_1568464] using wordTrace_append hprefix tailTrace_1568464
  have hstable : (prefixWord ++ tailWord_1568464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568464).length < 2 ^ (prefixWord ++ tailWord_1568464).sum := by decide
  have hdescent : baseEnd_1568464 < baseStart_1568464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568474 : List Nat := [3, 1, 1, 2, 2, 14]
def baseStart_1568474 : Nat := 118140960795 + 1568474 * 2 ^ 59
def prefixEnd_1568474 : Nat := 4983230072969 + 3 ^ 40 * 1568474 * 2
def baseEnd_1568474 : Nat := 3314325333663380954575

theorem tailTrace_1568474 : CollatzResearch.WordTrace tailWord_1568474 prefixEnd_1568474 3314325333663380954575 := by
  unfold tailWord_1568474
  simp only [CollatzResearch.WordTrace]
  refine ⟨14301736629923511719442119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38137964346462697918512317 14301736629923511719442119)
  ·
    refine ⟨21452604944885267579163179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14301736629923511719442119 21452604944885267579163179)
    ·
      refine ⟨32178907417327901368744769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21452604944885267579163179 32178907417327901368744769)
      ·
        refine ⟨24134180562995926026558577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32178907417327901368744769 24134180562995926026558577)
        ·
          refine ⟨18100635422246944519918933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24134180562995926026558577 18100635422246944519918933)
          ·
            refine ⟨3314325333663380954575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 18100635422246944519918933 3314325333663380954575)
            ·
              rfl

theorem cell23_1568474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 14].length) (baseStart_1568474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568474 prefixEnd_1568474 := by exact prefixLift 1568474
  have htrace : WordTrace (prefixWord ++ tailWord_1568474) baseStart_1568474 baseEnd_1568474 := by
    simpa [prefixWord, tailWord_1568474, baseEnd_1568474] using wordTrace_append hprefix tailTrace_1568474
  have hstable : (prefixWord ++ tailWord_1568474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568474).length < 2 ^ (prefixWord ++ tailWord_1568474).sum := by decide
  have hdescent : baseEnd_1568474 < baseStart_1568474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568485 : List Nat := [1, 3, 1, 4, 1, 1, 2, 3, 3, 2, 2]
def baseStart_1568485 : Nat := 118140960795 + 1568485 * 2 ^ 59
def prefixEnd_1568485 : Nat := 4983230072969 + 3 ^ 40 * 1568485 * 2
def baseEnd_1568485 : Nat := 805386704367401028924175

theorem tailTrace_1568485 : CollatzResearch.WordTrace tailWord_1568485 prefixEnd_1568485 805386704367401028924175 := by
  unfold tailWord_1568485
  simp only [CollatzResearch.WordTrace]
  refine ⟨57207347722654195756418909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38138231815102797170945939 57207347722654195756418909)
  ·
    refine ⟨21452755395995323408657091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57207347722654195756418909 21452755395995323408657091)
    ·
      refine ⟨32179133093992985112985637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21452755395995323408657091 32179133093992985112985637)
      ·
        refine ⟨6033587455123684708684807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32179133093992985112985637 6033587455123684708684807)
        ·
          refine ⟨9050381182685527063027211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6033587455123684708684807 9050381182685527063027211)
          ·
            refine ⟨13575571774028290594540817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9050381182685527063027211 13575571774028290594540817)
            ·
              refine ⟨10181678830521217945905613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13575571774028290594540817 10181678830521217945905613)
              ·
                refine ⟨3818129561445456729714605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10181678830521217945905613 3818129561445456729714605)
                ·
                  refine ⟨1431798585542046273642977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3818129561445456729714605 1431798585542046273642977)
                  ·
                    refine ⟨1073848939156534705232233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1431798585542046273642977 1073848939156534705232233)
                    ·
                      refine ⟨805386704367401028924175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073848939156534705232233 805386704367401028924175)
                      ·
                        rfl

theorem cell23_1568485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_1568485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568485 prefixEnd_1568485 := by exact prefixLift 1568485
  have htrace : WordTrace (prefixWord ++ tailWord_1568485) baseStart_1568485 baseEnd_1568485 := by
    simpa [prefixWord, tailWord_1568485, baseEnd_1568485] using wordTrace_append hprefix tailTrace_1568485
  have hstable : (prefixWord ++ tailWord_1568485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568485).length < 2 ^ (prefixWord ++ tailWord_1568485).sum := by decide
  have hdescent : baseEnd_1568485 < baseStart_1568485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568488 : List Nat := [2, 1, 4, 1, 3, 1, 1, 2, 3, 2, 3]
def baseStart_1568488 : Nat := 118140960795 + 1568488 * 2 ^ 59
def prefixEnd_1568488 : Nat := 4983230072969 + 3 ^ 40 * 1568488 * 2
def baseEnd_1568488 : Nat := 805388244809364517186661

theorem tailTrace_1568488 : CollatzResearch.WordTrace tailWord_1568488 prefixEnd_1568488 805388244809364517186661 := by
  unfold tailWord_1568488
  simp only [CollatzResearch.WordTrace]
  refine ⟨28603728570821663634389059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38138304761095551512518745 28603728570821663634389059)
  ·
    refine ⟨42905592856232495451583589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28603728570821663634389059 42905592856232495451583589)
    ·
      refine ⟨8044798660543592897171923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42905592856232495451583589 8044798660543592897171923)
      ·
        refine ⟨12067197990815389345757885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8044798660543592897171923 12067197990815389345757885)
        ·
          refine ⟨4525199246555771004659207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12067197990815389345757885 4525199246555771004659207)
          ·
            refine ⟨6787798869833656506988811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4525199246555771004659207 6787798869833656506988811)
            ·
              refine ⟨10181698304750484760483217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6787798869833656506988811 10181698304750484760483217)
              ·
                refine ⟨7636273728562863570362413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10181698304750484760483217 7636273728562863570362413)
                ·
                  refine ⟨2863602648211073838885905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7636273728562863570362413 2863602648211073838885905)
                  ·
                    refine ⟨2147701986158305379164429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2863602648211073838885905 2147701986158305379164429)
                    ·
                      refine ⟨805388244809364517186661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2147701986158305379164429 805388244809364517186661)
                      ·
                        rfl

theorem cell23_1568488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_1568488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568488 prefixEnd_1568488 := by exact prefixLift 1568488
  have htrace : WordTrace (prefixWord ++ tailWord_1568488) baseStart_1568488 baseEnd_1568488 := by
    simpa [prefixWord, tailWord_1568488, baseEnd_1568488] using wordTrace_append hprefix tailTrace_1568488
  have hstable : (prefixWord ++ tailWord_1568488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568488).length < 2 ^ (prefixWord ++ tailWord_1568488).sum := by decide
  have hdescent : baseEnd_1568488 < baseStart_1568488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568498 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 1, 2, 4]
def baseStart_1568498 : Nat := 118140960795 + 1568498 * 2 ^ 59
def prefixEnd_1568498 : Nat := 4983230072969 + 3 ^ 40 * 1568498 * 2
def baseEnd_1568498 : Nat := 805393379615909478061615

theorem tailTrace_1568498 : CollatzResearch.WordTrace tailWord_1568498 prefixEnd_1568498 805393379615909478061615 := by
  unfold tailWord_1568498
  simp only [CollatzResearch.WordTrace]
  refine ⟨14301955467901774744160537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38138547914404732651094765 14301955467901774744160537)
  ·
    refine ⟨10726466600926331058120403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14301955467901774744160537 10726466600926331058120403)
    ·
      refine ⟨16089699901389496587180605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10726466600926331058120403 16089699901389496587180605)
      ·
        refine ⟨6033637463021061220192727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16089699901389496587180605 6033637463021061220192727)
        ·
          refine ⟨9050456194531591830289091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6033637463021061220192727 9050456194531591830289091)
          ·
            refine ⟨13575684291797387745433637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9050456194531591830289091 13575684291797387745433637)
            ·
              refine ⟨2545440804712010202268807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13575684291797387745433637 2545440804712010202268807)
              ·
                refine ⟨3818161207068015303403211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545440804712010202268807 3818161207068015303403211)
                ·
                  refine ⟨5727241810602022955104817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818161207068015303403211 5727241810602022955104817)
                  ·
                    refine ⟨4295431357951517216328613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5727241810602022955104817 4295431357951517216328613)
                    ·
                      refine ⟨805393379615909478061615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4295431357951517216328613 805393379615909478061615)
                      ·
                        rfl

theorem cell23_1568498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_1568498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568498 prefixEnd_1568498 := by exact prefixLift 1568498
  have htrace : WordTrace (prefixWord ++ tailWord_1568498) baseStart_1568498 baseEnd_1568498 := by
    simpa [prefixWord, tailWord_1568498, baseEnd_1568498] using wordTrace_append hprefix tailTrace_1568498
  have hstable : (prefixWord ++ tailWord_1568498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568498).length < 2 ^ (prefixWord ++ tailWord_1568498).sum := by decide
  have hdescent : baseEnd_1568498 < baseStart_1568498 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568502 : List Nat := [5, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2]
def baseStart_1568502 : Nat := 118140960795 + 1568502 * 2 ^ 59
def prefixEnd_1568502 : Nat := 4983230072969 + 3 ^ 40 * 1568502 * 2
def baseEnd_1568502 : Nat := 805395433538527462411597

theorem tailTrace_1568502 : CollatzResearch.WordTrace tailWord_1568502 prefixEnd_1568502 805395433538527462411597 := by
  unfold tailWord_1568502
  simp only [CollatzResearch.WordTrace]
  refine ⟨3575497985224537978736735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38138645175728405106525173 3575497985224537978736735)
  ·
    refine ⟨5363246977836806968105103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3575497985224537978736735 5363246977836806968105103)
    ·
      refine ⟨8044870466755210452157655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5363246977836806968105103 8044870466755210452157655)
      ·
        refine ⟨12067305700132815678236483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8044870466755210452157655 12067305700132815678236483)
        ·
          refine ⟨18100958550199223517354725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12067305700132815678236483 18100958550199223517354725)
          ·
            refine ⟨3393929728162354409504011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18100958550199223517354725 3393929728162354409504011)
            ·
              refine ⟨5090894592243531614256017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393929728162354409504011 5090894592243531614256017)
              ·
                refine ⟨3818170944182648710692013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5090894592243531614256017 3818170944182648710692013)
                ·
                  refine ⟨1431814104068493266509505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3818170944182648710692013 1431814104068493266509505)
                  ·
                    refine ⟨1073860578051369949882129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1431814104068493266509505 1073860578051369949882129)
                    ·
                      refine ⟨805395433538527462411597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073860578051369949882129 805395433538527462411597)
                      ·
                        rfl

theorem cell23_1568502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2].length) (baseStart_1568502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568502 prefixEnd_1568502 := by exact prefixLift 1568502
  have htrace : WordTrace (prefixWord ++ tailWord_1568502) baseStart_1568502 baseEnd_1568502 := by
    simpa [prefixWord, tailWord_1568502, baseEnd_1568502] using wordTrace_append hprefix tailTrace_1568502
  have hstable : (prefixWord ++ tailWord_1568502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568502).length < 2 ^ (prefixWord ++ tailWord_1568502).sum := by decide
  have hdescent : baseEnd_1568502 < baseStart_1568502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568519 : List Nat := [1, 1, 4, 4, 3, 1, 2, 1, 1, 1, 4]
def baseStart_1568519 : Nat := 118140960795 + 1568519 * 2 ^ 59
def prefixEnd_1568519 : Nat := 4983230072969 + 3 ^ 40 * 1568519 * 2
def baseEnd_1568519 : Nat := 805404162709653895899019

theorem tailTrace_1568519 : CollatzResearch.WordTrace tailWord_1568519 prefixEnd_1568519 805404162709653895899019 := by
  unfold tailWord_1568519
  simp only [CollatzResearch.WordTrace]
  refine ⟨57208587804531019563156611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38139058536354013042104407 57208587804531019563156611)
  ·
    refine ⟨85812881706796529344734917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57208587804531019563156611 85812881706796529344734917)
    ·
      refine ⟨16089915320024349252137797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85812881706796529344734917 16089915320024349252137797)
      ·
        refine ⟨3016859122504565484775837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16089915320024349252137797 3016859122504565484775837)
        ·
          refine ⟨1131322170939212056790939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3016859122504565484775837 1131322170939212056790939)
          ·
            refine ⟨1696983256408818085186409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131322170939212056790939 1696983256408818085186409)
            ·
              refine ⟨1272737442306613563889807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1696983256408818085186409 1272737442306613563889807)
              ·
                refine ⟨1909106163459920345834711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272737442306613563889807 1909106163459920345834711)
                ·
                  refine ⟨2863659245189880518752067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909106163459920345834711 2863659245189880518752067)
                  ·
                    refine ⟨4295488867784820778128101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2863659245189880518752067 4295488867784820778128101)
                    ·
                      refine ⟨805404162709653895899019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4295488867784820778128101 805404162709653895899019)
                      ·
                        rfl

theorem cell23_1568519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_1568519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568519 prefixEnd_1568519 := by exact prefixLift 1568519
  have htrace : WordTrace (prefixWord ++ tailWord_1568519) baseStart_1568519 baseEnd_1568519 := by
    simpa [prefixWord, tailWord_1568519, baseEnd_1568519] using wordTrace_append hprefix tailTrace_1568519
  have hstable : (prefixWord ++ tailWord_1568519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568519).length < 2 ^ (prefixWord ++ tailWord_1568519).sum := by decide
  have hdescent : baseEnd_1568519 < baseStart_1568519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568522 : List Nat := [3, 1, 2, 2, 1, 5, 2, 1, 1, 2, 3]
def baseStart_1568522 : Nat := 118140960795 + 1568522 * 2 ^ 59
def prefixEnd_1568522 : Nat := 4983230072969 + 3 ^ 40 * 1568522 * 2
def baseEnd_1568522 : Nat := 805405703151617384161505

theorem tailTrace_1568522 : CollatzResearch.WordTrace tailWord_1568522 prefixEnd_1568522 805405703151617384161505 := by
  unfold tailWord_1568522
  simp only [CollatzResearch.WordTrace]
  refine ⟨14302174305880037768878955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38139131482346767383677213 14302174305880037768878955)
  ·
    refine ⟨21453261458820056653318433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14302174305880037768878955 21453261458820056653318433)
    ·
      refine ⟨16089946094115042489988825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21453261458820056653318433 16089946094115042489988825)
      ·
        refine ⟨12067459570586281867491619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16089946094115042489988825 12067459570586281867491619)
        ·
          refine ⟨18101189355879422801237429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12067459570586281867491619 18101189355879422801237429)
          ·
            refine ⟨1696986502113695887616009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18101189355879422801237429 1696986502113695887616009)
            ·
              refine ⟨1272739876585271915712007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1696986502113695887616009 1272739876585271915712007)
              ·
                refine ⟨1909109814877907873568011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1272739876585271915712007 1909109814877907873568011)
                ·
                  refine ⟨2863664722316861810352017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909109814877907873568011 2863664722316861810352017)
                  ·
                    refine ⟨2147748541737646357764013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2863664722316861810352017 2147748541737646357764013)
                    ·
                      refine ⟨805405703151617384161505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2147748541737646357764013 805405703151617384161505)
                      ·
                        rfl

theorem cell23_1568522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_1568522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568522 prefixEnd_1568522 := by exact prefixLift 1568522
  have htrace : WordTrace (prefixWord ++ tailWord_1568522) baseStart_1568522 baseEnd_1568522 := by
    simpa [prefixWord, tailWord_1568522, baseEnd_1568522] using wordTrace_append hprefix tailTrace_1568522
  have hstable : (prefixWord ++ tailWord_1568522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568522).length < 2 ^ (prefixWord ++ tailWord_1568522).sum := by decide
  have hdescent : baseEnd_1568522 < baseStart_1568522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568535 : List Nat := [1, 1, 3, 4, 2, 2, 1, 1, 4, 1, 3]
def baseStart_1568535 : Nat := 118140960795 + 1568535 * 2 ^ 59
def prefixEnd_1568535 : Nat := 4983230072969 + 3 ^ 40 * 1568535 * 2
def baseEnd_1568535 : Nat := 805412378400125833298945

theorem tailTrace_1568535 : CollatzResearch.WordTrace tailWord_1568535 prefixEnd_1568535 805412378400125833298945 := by
  unfold tailWord_1568535
  simp only [CollatzResearch.WordTrace]
  refine ⟨57209171372473054295739059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38139447581648702863826039 57209171372473054295739059)
  ·
    refine ⟨85813757058709581443608589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57209171372473054295739059 85813757058709581443608589)
    ·
      refine ⟨32180158897016093041353221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85813757058709581443608589 32180158897016093041353221)
      ·
        refine ⟨6033779793190517445253729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32180158897016093041353221 6033779793190517445253729)
        ·
          refine ⟨4525334844892888083940297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6033779793190517445253729 4525334844892888083940297)
          ·
            refine ⟨3394001133669666062955223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4525334844892888083940297 3394001133669666062955223)
            ·
              refine ⟨5091001700504499094432835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394001133669666062955223 5091001700504499094432835)
              ·
                refine ⟨7636502550756748641649253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5091001700504499094432835 7636502550756748641649253)
                ·
                  refine ⟨1431844228266890370309235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7636502550756748641649253 1431844228266890370309235)
                  ·
                    refine ⟨2147766342400335555463853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1431844228266890370309235 2147766342400335555463853)
                    ·
                      refine ⟨805412378400125833298945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2147766342400335555463853 805412378400125833298945)
                      ·
                        rfl

theorem cell23_1568535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_1568535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568535 prefixEnd_1568535 := by exact prefixLift 1568535
  have htrace : WordTrace (prefixWord ++ tailWord_1568535) baseStart_1568535 baseEnd_1568535 := by
    simpa [prefixWord, tailWord_1568535, baseEnd_1568535] using wordTrace_append hprefix tailTrace_1568535
  have hstable : (prefixWord ++ tailWord_1568535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568535).length < 2 ^ (prefixWord ++ tailWord_1568535).sum := by decide
  have hdescent : baseEnd_1568535 < baseStart_1568535 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568562 : List Nat := [3, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2]
def baseStart_1568562 : Nat := 118140960795 + 1568562 * 2 ^ 59
def prefixEnd_1568562 : Nat := 4983230072969 + 3 ^ 40 * 1568562 * 2
def baseEnd_1568562 : Nat := 805426242377797227661321

theorem tailTrace_1568562 : CollatzResearch.WordTrace tailWord_1568562 prefixEnd_1568562 805426242377797227661321 := by
  unfold tailWord_1568562
  simp only [CollatzResearch.WordTrace]
  refine ⟨14302539035843809476742985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38140104095583491937981293 14302539035843809476742985)
  ·
    refine ⟨10726904276882857107557239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14302539035843809476742985 10726904276882857107557239)
    ·
      refine ⟨16090356415324285661335859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10726904276882857107557239 16090356415324285661335859)
      ·
        refine ⟨24135534622986428492003789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16090356415324285661335859 24135534622986428492003789)
        ·
          refine ⟨9050825483619910684501421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24135534622986428492003789 9050825483619910684501421)
          ·
            refine ⟨3394059556357466506688033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9050825483619910684501421 3394059556357466506688033)
            ·
              refine ⟨2545544667268099880016025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3394059556357466506688033 2545544667268099880016025)
              ·
                refine ⟨1909158500451074910012019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2545544667268099880016025 1909158500451074910012019)
                ·
                  refine ⟨2863737750676612365018029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909158500451074910012019 2863737750676612365018029)
                  ·
                    refine ⟨1073901656503729636881761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2863737750676612365018029 1073901656503729636881761)
                    ·
                      refine ⟨805426242377797227661321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1073901656503729636881761 805426242377797227661321)
                      ·
                        rfl

theorem cell23_1568562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_1568562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568562 prefixEnd_1568562 := by exact prefixLift 1568562
  have htrace : WordTrace (prefixWord ++ tailWord_1568562) baseStart_1568562 baseEnd_1568562 := by
    simpa [prefixWord, tailWord_1568562, baseEnd_1568562] using wordTrace_append hprefix tailTrace_1568562
  have hstable : (prefixWord ++ tailWord_1568562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568562).length < 2 ^ (prefixWord ++ tailWord_1568562).sum := by decide
  have hdescent : baseEnd_1568562 < baseStart_1568562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568651 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 5]
def baseStart_1568651 : Nat := 118140960795 + 1568651 * 2 ^ 59
def prefixEnd_1568651 : Nat := 4983230072969 + 3 ^ 40 * 1568651 * 2
def baseEnd_1568651 : Nat := 805471942156047379448411

theorem tailTrace_1568651 : CollatzResearch.WordTrace tailWord_1568651 prefixEnd_1568651 805471942156047379448411 := by
  unfold tailWord_1568651
  simp only [CollatzResearch.WordTrace]
  refine ⟨57213402240052806106961807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38142268160035204071307871 57213402240052806106961807)
  ·
    refine ⟨85820103360079209160442711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57213402240052806106961807 85820103360079209160442711)
    ·
      refine ⟨128730155040118813740664067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85820103360079209160442711 128730155040118813740664067)
      ·
        refine ⟨193095232560178220610996101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128730155040118813740664067 193095232560178220610996101)
        ·
          refine ⟨36205356105033416364561769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193095232560178220610996101 36205356105033416364561769)
          ·
            refine ⟨27154017078775062273421327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36205356105033416364561769 27154017078775062273421327)
            ·
              refine ⟨40731025618162593410131991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27154017078775062273421327 40731025618162593410131991)
              ·
                refine ⟨61096538427243890115197987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40731025618162593410131991 61096538427243890115197987)
                ·
                  refine ⟨91644807640865835172796981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61096538427243890115197987 91644807640865835172796981)
                  ·
                    refine ⟨8591700716331172047449717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 91644807640865835172796981 8591700716331172047449717)
                    ·
                      refine ⟨805471942156047379448411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8591700716331172047449717 805471942156047379448411)
                      ·
                        rfl

theorem cell23_1568651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 5, 5].length) (baseStart_1568651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568651 prefixEnd_1568651 := by exact prefixLift 1568651
  have htrace : WordTrace (prefixWord ++ tailWord_1568651) baseStart_1568651 baseEnd_1568651 := by
    simpa [prefixWord, tailWord_1568651, baseEnd_1568651] using wordTrace_append hprefix tailTrace_1568651
  have hstable : (prefixWord ++ tailWord_1568651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568651).length < 2 ^ (prefixWord ++ tailWord_1568651).sum := by decide
  have hdescent : baseEnd_1568651 < baseStart_1568651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568735 : List Nat := [1, 1, 2, 3, 4, 1, 1, 4, 1, 5]
def baseStart_1568735 : Nat := 118140960795 + 1568735 * 2 ^ 59
def prefixEnd_1568735 : Nat := 4983230072969 + 3 ^ 40 * 1568735 * 2
def baseEnd_1568735 : Nat := 268505024843675016932675

theorem tailTrace_1568735 : CollatzResearch.WordTrace tailWord_1568735 prefixEnd_1568735 268505024843675016932675 := by
  unfold tailWord_1568735
  simp only [CollatzResearch.WordTrace]
  refine ⟨57216465971748488453019659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38144310647832325635346439 57216465971748488453019659)
  ·
    refine ⟨85824698957622732679529489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57216465971748488453019659 85824698957622732679529489)
    ·
      refine ⟨64368524218217049509647117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85824698957622732679529489 64368524218217049509647117)
      ·
        refine ⟨24138196581831393566117669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64368524218217049509647117 24138196581831393566117669)
        ·
          refine ⟨4525911859093386293647063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24138196581831393566117669 4525911859093386293647063)
          ·
            refine ⟨6788867788640079440470595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4525911859093386293647063 6788867788640079440470595)
            ·
              refine ⟨10183301682960119160705893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6788867788640079440470595 10183301682960119160705893)
              ·
                refine ⟨1909369065555022342632355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10183301682960119160705893 1909369065555022342632355)
                ·
                  refine ⟨2864053598332533513948533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909369065555022342632355 2864053598332533513948533)
                  ·
                    refine ⟨268505024843675016932675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2864053598332533513948533 268505024843675016932675)
                    ·
                      rfl

theorem cell23_1568735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 4, 1, 5].length) (baseStart_1568735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568735 prefixEnd_1568735 := by exact prefixLift 1568735
  have htrace : WordTrace (prefixWord ++ tailWord_1568735) baseStart_1568735 baseEnd_1568735 := by
    simpa [prefixWord, tailWord_1568735, baseEnd_1568735] using wordTrace_append hprefix tailTrace_1568735
  have hstable : (prefixWord ++ tailWord_1568735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568735).length < 2 ^ (prefixWord ++ tailWord_1568735).sum := by decide
  have hdescent : baseEnd_1568735 < baseStart_1568735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568748 : List Nat := [2, 2, 1, 1, 2, 1, 1, 6, 1, 6]
def baseStart_1568748 : Nat := 118140960795 + 1568748 * 2 ^ 59
def prefixEnd_1568748 : Nat := 4983230072969 + 3 ^ 40 * 1568748 * 2
def baseEnd_1568748 : Nat := 268507249926511166645155

theorem tailTrace_1568748 : CollatzResearch.WordTrace tailWord_1568748 prefixEnd_1568748 268507249926511166645155 := by
  unfold tailWord_1568748
  simp only [CollatzResearch.WordTrace]
  refine ⟨28608470060350695836621449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38144626747134261115495265 28608470060350695836621449)
  ·
    refine ⟨21456352545263021877466087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28608470060350695836621449 21456352545263021877466087)
    ·
      refine ⟨32184528817894532816199131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21456352545263021877466087 32184528817894532816199131)
      ·
        refine ⟨48276793226841799224298697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32184528817894532816199131 48276793226841799224298697)
        ·
          refine ⟨36207594920131349418224023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48276793226841799224298697 36207594920131349418224023)
          ·
            refine ⟨54311392380197024127336035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36207594920131349418224023 54311392380197024127336035)
            ·
              refine ⟨81467088570295536191004053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54311392380197024127336035 81467088570295536191004053)
              ·
                refine ⟨3818769776732603258953315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81467088570295536191004053 3818769776732603258953315)
                ·
                  refine ⟨5728154665098904888429973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818769776732603258953315 5728154665098904888429973)
                  ·
                    refine ⟨268507249926511166645155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5728154665098904888429973 268507249926511166645155)
                    ·
                      rfl

theorem cell23_1568748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_1568748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568748 prefixEnd_1568748 := by exact prefixLift 1568748
  have htrace : WordTrace (prefixWord ++ tailWord_1568748) baseStart_1568748 baseEnd_1568748 := by
    simpa [prefixWord, tailWord_1568748, baseEnd_1568748] using wordTrace_append hprefix tailTrace_1568748
  have hstable : (prefixWord ++ tailWord_1568748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568748).length < 2 ^ (prefixWord ++ tailWord_1568748).sum := by decide
  have hdescent : baseEnd_1568748 < baseStart_1568748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568765 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_1568765 : Nat := 118140960795 + 1568765 * 2 ^ 59
def prefixEnd_1568765 : Nat := 4983230072969 + 3 ^ 40 * 1568765 * 2
def baseEnd_1568765 : Nat := 268510159650219977807629

theorem tailTrace_1568765 : CollatzResearch.WordTrace tailWord_1568765 prefixEnd_1568765 268510159650219977807629 := by
  unfold tailWord_1568765
  simp only [CollatzResearch.WordTrace]
  refine ⟨57217560161639803576611749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38145040107759869051074499 57217560161639803576611749)
  ·
    refine ⟨10728292530307463170614703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57217560161639803576611749 10728292530307463170614703)
    ·
      refine ⟨16092438795461194755922055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10728292530307463170614703 16092438795461194755922055)
      ·
        refine ⟨24138658193191792133883083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16092438795461194755922055 24138658193191792133883083)
        ·
          refine ⟨36207987289787688200824625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24138658193191792133883083 36207987289787688200824625)
          ·
            refine ⟨27155990467340766150618469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36207987289787688200824625 27155990467340766150618469)
            ·
              refine ⟨5091748212626393653240963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27155990467340766150618469 5091748212626393653240963)
              ·
                refine ⟨7637622318939590479861445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5091748212626393653240963 7637622318939590479861445)
                ·
                  refine ⟨1432054184801173214974021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7637622318939590479861445 1432054184801173214974021)
                  ·
                    refine ⟨268510159650219977807629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1432054184801173214974021 268510159650219977807629)
                    ·
                      rfl

theorem cell23_1568765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_1568765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568765 prefixEnd_1568765 := by exact prefixLift 1568765
  have htrace : WordTrace (prefixWord ++ tailWord_1568765) baseStart_1568765 baseEnd_1568765 := by
    simpa [prefixWord, tailWord_1568765, baseEnd_1568765] using wordTrace_append hprefix tailTrace_1568765
  have hstable : (prefixWord ++ tailWord_1568765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568765).length < 2 ^ (prefixWord ++ tailWord_1568765).sum := by decide
  have hdescent : baseEnd_1568765 < baseStart_1568765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568766 : List Nat := [4, 2, 2, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_1568766 : Nat := 118140960795 + 1568766 * 2 ^ 59
def prefixEnd_1568766 : Nat := 4983230072969 + 3 ^ 40 * 1568766 * 2
def baseEnd_1568766 : Nat := 805530992431314429510383

theorem tailTrace_1568766 : CollatzResearch.WordTrace tailWord_1568766 prefixEnd_1568766 805530992431314429510383 := by
  unfold tailWord_1568766
  simp only [CollatzResearch.WordTrace]
  refine ⟨7152199579329522593424769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38145064423090787164932101 7152199579329522593424769)
  ·
    refine ⟨5364149684497141945068577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7152199579329522593424769 5364149684497141945068577)
    ·
      refine ⟨4023112263372856458801433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5364149684497141945068577 4023112263372856458801433)
      ·
        refine ⟨3017334197529642344101075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4023112263372856458801433 3017334197529642344101075)
        ·
          refine ⟨4526001296294463516151613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3017334197529642344101075 4526001296294463516151613)
          ·
            refine ⟨1697250486110423818556855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4526001296294463516151613 1697250486110423818556855)
            ·
              refine ⟨2545875729165635727835283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697250486110423818556855 2545875729165635727835283)
              ·
                refine ⟨3818813593748453591752925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545875729165635727835283 3818813593748453591752925)
                ·
                  refine ⟨1432055097655670096907347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3818813593748453591752925 1432055097655670096907347)
                  ·
                    refine ⟨2148082646483505145361021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1432055097655670096907347 2148082646483505145361021)
                    ·
                      refine ⟨805530992431314429510383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2148082646483505145361021 805530992431314429510383)
                      ·
                        rfl

theorem cell23_1568766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_1568766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568766 prefixEnd_1568766 := by exact prefixLift 1568766
  have htrace : WordTrace (prefixWord ++ tailWord_1568766) baseStart_1568766 baseEnd_1568766 := by
    simpa [prefixWord, tailWord_1568766, baseEnd_1568766] using wordTrace_append hprefix tailTrace_1568766
  have hstable : (prefixWord ++ tailWord_1568766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568766).length < 2 ^ (prefixWord ++ tailWord_1568766).sum := by decide
  have hdescent : baseEnd_1568766 < baseStart_1568766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568768 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 4]
def baseStart_1568768 : Nat := 118140960795 + 1568768 * 2 ^ 59
def prefixEnd_1568768 : Nat := 4983230072969 + 3 ^ 40 * 1568768 * 2
def baseEnd_1568768 : Nat := 805532019392623421685373

theorem tailTrace_1568768 : CollatzResearch.WordTrace tailWord_1568768 prefixEnd_1568768 805532019392623421685373 := by
  unfold tailWord_1568768
  simp only [CollatzResearch.WordTrace]
  refine ⟨28608834790314467544485479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38145113053752623392647305 28608834790314467544485479)
  ·
    refine ⟨42913252185471701316728219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28608834790314467544485479 42913252185471701316728219)
    ·
      refine ⟨64369878278207551975092329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42913252185471701316728219 64369878278207551975092329)
      ·
        refine ⟨48277408708655663981319247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64369878278207551975092329 48277408708655663981319247)
        ·
          refine ⟨72416113062983495971978871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48277408708655663981319247 72416113062983495971978871)
          ·
            refine ⟨108624169594475243957968307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72416113062983495971978871 108624169594475243957968307)
            ·
              refine ⟨162936254391712865936952461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108624169594475243957968307 162936254391712865936952461)
              ·
                refine ⟨61101095396892324726357173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 162936254391712865936952461 61101095396892324726357173)
                ·
                  refine ⟨5728227693458655443095985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61101095396892324726357173 5728227693458655443095985)
                  ·
                    refine ⟨4296170770093991582321989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5728227693458655443095985 4296170770093991582321989)
                    ·
                      refine ⟨805532019392623421685373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4296170770093991582321989 805532019392623421685373)
                      ·
                        rfl

theorem cell23_1568768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 2, 4].length) (baseStart_1568768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568768 prefixEnd_1568768 := by exact prefixLift 1568768
  have htrace : WordTrace (prefixWord ++ tailWord_1568768) baseStart_1568768 baseEnd_1568768 := by
    simpa [prefixWord, tailWord_1568768, baseEnd_1568768] using wordTrace_append hprefix tailTrace_1568768
  have hstable : (prefixWord ++ tailWord_1568768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568768).length < 2 ^ (prefixWord ++ tailWord_1568768).sum := by decide
  have hdescent : baseEnd_1568768 < baseStart_1568768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568775 : List Nat := [1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 5]
def baseStart_1568775 : Nat := 118140960795 + 1568775 * 2 ^ 59
def prefixEnd_1568775 : Nat := 4983230072969 + 3 ^ 40 * 1568775 * 2
def baseEnd_1568775 : Nat := 805535613757204894297841

theorem tailTrace_1568775 : CollatzResearch.WordTrace tailWord_1568775 prefixEnd_1568775 805535613757204894297841 := by
  unfold tailWord_1568775
  simp only [CollatzResearch.WordTrace]
  refine ⟨57217924891603575284475779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38145283261069050189650519 57217924891603575284475779)
  ·
    refine ⟨85826887337405362926713669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57217924891603575284475779 85826887337405362926713669)
    ·
      refine ⟨16092541375763505548758813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 85826887337405362926713669 16092541375763505548758813)
      ·
        refine ⟨6034703015911314580784555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16092541375763505548758813 6034703015911314580784555)
        ·
          refine ⟨9052054523866971871176833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6034703015911314580784555 9052054523866971871176833)
          ·
            refine ⟨6789040892900228903382625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9052054523866971871176833 6789040892900228903382625)
            ·
              refine ⟨5091780669675171677536969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6789040892900228903382625 5091780669675171677536969)
              ·
                refine ⟨3818835502256378758152727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5091780669675171677536969 3818835502256378758152727)
                ·
                  refine ⟨5728253253384568137229091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3818835502256378758152727 5728253253384568137229091)
                  ·
                    refine ⟨8592379880076852205843637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5728253253384568137229091 8592379880076852205843637)
                    ·
                      refine ⟨805535613757204894297841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8592379880076852205843637 805535613757204894297841)
                      ·
                        rfl

theorem cell23_1568775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_1568775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568775 prefixEnd_1568775 := by exact prefixLift 1568775
  have htrace : WordTrace (prefixWord ++ tailWord_1568775) baseStart_1568775 baseEnd_1568775 := by
    simpa [prefixWord, tailWord_1568775, baseEnd_1568775] using wordTrace_append hprefix tailTrace_1568775
  have hstable : (prefixWord ++ tailWord_1568775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568775).length < 2 ^ (prefixWord ++ tailWord_1568775).sum := by decide
  have hdescent : baseEnd_1568775 < baseStart_1568775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568782 : List Nat := [4, 1, 1, 2, 2, 1, 3, 3, 2, 4]
def baseStart_1568782 : Nat := 118140960795 + 1568782 * 2 ^ 59
def prefixEnd_1568782 : Nat := 4983230072969 + 3 ^ 40 * 1568782 * 2
def baseEnd_1568782 : Nat := 268513069373928788970103

theorem tailTrace_1568782 : CollatzResearch.WordTrace tailWord_1568782 prefixEnd_1568782 268513069373928788970103 := by
  unfold tailWord_1568782
  simp only [CollatzResearch.WordTrace]
  refine ⟨7152272525322276934997575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38145453468385476986653733 7152272525322276934997575)
  ·
    refine ⟨10728408787983415402496363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7152272525322276934997575 10728408787983415402496363)
    ·
      refine ⟨16092613181975123103744545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10728408787983415402496363 16092613181975123103744545)
      ·
        refine ⟨12069459886481342327808409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16092613181975123103744545 12069459886481342327808409)
        ·
          refine ⟨9052094914861006745856307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12069459886481342327808409 9052094914861006745856307)
          ·
            refine ⟨13578142372291510118784461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9052094914861006745856307 13578142372291510118784461)
            ·
              refine ⟨5091803389609316294544173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13578142372291510118784461 5091803389609316294544173)
              ·
                refine ⟨1909426271103493610454065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5091803389609316294544173 1909426271103493610454065)
                ·
                  refine ⟨1432069703327620207840549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1909426271103493610454065 1432069703327620207840549)
                  ·
                    refine ⟨268513069373928788970103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1432069703327620207840549 268513069373928788970103)
                    ·
                      rfl

theorem cell23_1568782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 3, 3, 2, 4].length) (baseStart_1568782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568782 prefixEnd_1568782 := by exact prefixLift 1568782
  have htrace : WordTrace (prefixWord ++ tailWord_1568782) baseStart_1568782 baseEnd_1568782 := by
    simpa [prefixWord, tailWord_1568782, baseEnd_1568782] using wordTrace_append hprefix tailTrace_1568782
  have hstable : (prefixWord ++ tailWord_1568782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568782).length < 2 ^ (prefixWord ++ tailWord_1568782).sum := by decide
  have hdescent : baseEnd_1568782 < baseStart_1568782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568789 : List Nat := [1, 3, 2, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_1568789 : Nat := 118140960795 + 1568789 * 2 ^ 59
def prefixEnd_1568789 : Nat := 4983230072969 + 3 ^ 40 * 1568789 * 2
def baseEnd_1568789 : Nat := 805542802486367839522777

theorem tailTrace_1568789 : CollatzResearch.WordTrace tailWord_1568789 prefixEnd_1568789 805542802486367839522777 := by
  unfold tailWord_1568789
  simp only [CollatzResearch.WordTrace]
  refine ⟨57218435513552855675485421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38145623675701903783656947 57218435513552855675485421)
  ·
    refine ⟨21456913317582320878307033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57218435513552855675485421 21456913317582320878307033)
    ·
      refine ⟨16092684988186740658730275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21456913317582320878307033 16092684988186740658730275)
      ·
        refine ⟨24139027482280110988095413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16092684988186740658730275 24139027482280110988095413)
        ·
          refine ⟨2263033826463760405133945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24139027482280110988095413 2263033826463760405133945)
          ·
            refine ⟨1697275369847820303850459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2263033826463760405133945 1697275369847820303850459)
            ·
              refine ⟨2545913054771730455775689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697275369847820303850459 2545913054771730455775689)
              ·
                refine ⟨1909434791078797841831767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2545913054771730455775689 1909434791078797841831767)
                ·
                  refine ⟨2864152186618196762747651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909434791078797841831767 2864152186618196762747651)
                  ·
                    refine ⟨4296228279927295144121477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2864152186618196762747651 4296228279927295144121477)
                    ·
                      refine ⟨805542802486367839522777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4296228279927295144121477 805542802486367839522777)
                      ·
                        rfl

theorem cell23_1568789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_1568789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568789 prefixEnd_1568789 := by exact prefixLift 1568789
  have htrace : WordTrace (prefixWord ++ tailWord_1568789) baseStart_1568789 baseEnd_1568789 := by
    simpa [prefixWord, tailWord_1568789, baseEnd_1568789] using wordTrace_append hprefix tailTrace_1568789
  have hstable : (prefixWord ++ tailWord_1568789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568789).length < 2 ^ (prefixWord ++ tailWord_1568789).sum := by decide
  have hdescent : baseEnd_1568789 < baseStart_1568789 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568805 : List Nat := [1, 3, 1, 2, 2, 3, 1, 1, 3, 3, 3]
def baseStart_1568805 : Nat := 118140960795 + 1568805 * 2 ^ 59
def prefixEnd_1568805 : Nat := 4983230072969 + 3 ^ 40 * 1568805 * 2
def baseEnd_1568805 : Nat := 805551018176839776922703

theorem tailTrace_1568805 : CollatzResearch.WordTrace tailWord_1568805 prefixEnd_1568805 805551018176839776922703 := by
  unfold tailWord_1568805
  simp only [CollatzResearch.WordTrace]
  refine ⟨57219019081494890408067869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38146012720996593605378579 57219019081494890408067869)
  ·
    refine ⟨21457132155560583903025451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57219019081494890408067869 21457132155560583903025451)
    ·
      refine ⟨32185698233340875854538177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21457132155560583903025451 32185698233340875854538177)
      ·
        refine ⟨24139273675005656890903633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32185698233340875854538177 24139273675005656890903633)
        ·
          refine ⟨18104455256254242668177725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24139273675005656890903633 18104455256254242668177725)
          ·
            refine ⟨6789170721095341000566647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18104455256254242668177725 6789170721095341000566647)
            ·
              refine ⟨10183756081643011500849971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6789170721095341000566647 10183756081643011500849971)
              ·
                refine ⟨15275634122464517251274957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10183756081643011500849971 15275634122464517251274957)
                ·
                  refine ⟨5728362795924193969228109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15275634122464517251274957 5728362795924193969228109)
                  ·
                    refine ⟨2148136048471572738460541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5728362795924193969228109 2148136048471572738460541)
                    ·
                      refine ⟨805551018176839776922703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2148136048471572738460541 805551018176839776922703)
                      ·
                        rfl

theorem cell23_1568805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_1568805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568805 prefixEnd_1568805 := by exact prefixLift 1568805
  have htrace : WordTrace (prefixWord ++ tailWord_1568805) baseStart_1568805 baseEnd_1568805 := by
    simpa [prefixWord, tailWord_1568805, baseEnd_1568805] using wordTrace_append hprefix tailTrace_1568805
  have hstable : (prefixWord ++ tailWord_1568805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568805).length < 2 ^ (prefixWord ++ tailWord_1568805).sum := by decide
  have hdescent : baseEnd_1568805 < baseStart_1568805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568822 : List Nat := [5, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1568822 : Nat := 118140960795 + 1568822 * 2 ^ 59
def prefixEnd_1568822 : Nat := 4983230072969 + 3 ^ 40 * 1568822 * 2
def baseEnd_1568822 : Nat := 805559747347966210410125

theorem tailTrace_1568822 : CollatzResearch.WordTrace tailWord_1568822 prefixEnd_1568822 805559747347966210410125 := by
  unfold tailWord_1568822
  simp only [CollatzResearch.WordTrace]
  refine ⟨3576227445152081394464795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38146426081622201540957813 3576227445152081394464795)
  ·
    refine ⟨5364341167728122091697193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3576227445152081394464795 5364341167728122091697193)
    ·
      refine ⟨4023255875796091568772895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5364341167728122091697193 4023255875796091568772895)
      ·
        refine ⟨6034883813694137353159343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4023255875796091568772895 6034883813694137353159343)
        ·
          refine ⟨9052325720541206029739015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6034883813694137353159343 9052325720541206029739015)
          ·
            refine ⟨13578488580811809044608523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9052325720541206029739015 13578488580811809044608523)
            ·
              refine ⟨20367732871217713566912785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13578488580811809044608523 20367732871217713566912785)
              ·
                refine ⟨15275799653413285175184589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20367732871217713566912785 15275799653413285175184589)
                ·
                  refine ⟨5728424870029981940694221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15275799653413285175184589 5728424870029981940694221)
                  ·
                    refine ⟨2148159326261243227760333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5728424870029981940694221 2148159326261243227760333)
                    ·
                      refine ⟨805559747347966210410125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2148159326261243227760333 805559747347966210410125)
                      ·
                        rfl

theorem cell23_1568822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1568822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568822 prefixEnd_1568822 := by exact prefixLift 1568822
  have htrace : WordTrace (prefixWord ++ tailWord_1568822) baseStart_1568822 baseEnd_1568822 := by
    simpa [prefixWord, tailWord_1568822, baseEnd_1568822] using wordTrace_append hprefix tailTrace_1568822
  have hstable : (prefixWord ++ tailWord_1568822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568822).length < 2 ^ (prefixWord ++ tailWord_1568822).sum := by decide
  have hdescent : baseEnd_1568822 < baseStart_1568822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568832 : List Nat := [2, 1, 1, 2, 2, 4, 1, 2, 3, 3, 2]
def baseStart_1568832 : Nat := 118140960795 + 1568832 * 2 ^ 59
def prefixEnd_1568832 : Nat := 4983230072969 + 3 ^ 40 * 1568832 * 2
def baseEnd_1568832 : Nat := 805564882154511171285079

theorem tailTrace_1568832 : CollatzResearch.WordTrace tailWord_1568832 prefixEnd_1568832 805564882154511171285079 := by
  unfold tailWord_1568832
  simp only [CollatzResearch.WordTrace]
  refine ⟨28610001926198537009650375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38146669234931382679533833 28610001926198537009650375)
  ·
    refine ⟨42915002889297805514475563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28610001926198537009650375 42915002889297805514475563)
    ·
      refine ⟨64372504333946708271713345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42915002889297805514475563 64372504333946708271713345)
      ·
        refine ⟨48279378250460031203785009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64372504333946708271713345 48279378250460031203785009)
        ·
          refine ⟨36209533687845023402838757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48279378250460031203785009 36209533687845023402838757)
          ·
            refine ⟨6789287566470941888032267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36209533687845023402838757 6789287566470941888032267)
            ·
              refine ⟨10183931349706412832048401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6789287566470941888032267 10183931349706412832048401)
              ·
                refine ⟨7637948512279809624036301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10183931349706412832048401 7637948512279809624036301)
                ·
                  refine ⟨2864230692104928609013613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7637948512279809624036301 2864230692104928609013613)
                  ·
                    refine ⟨1074086509539348228380105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2864230692104928609013613 1074086509539348228380105)
                    ·
                      refine ⟨805564882154511171285079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074086509539348228380105 805564882154511171285079)
                      ·
                        rfl

theorem cell23_1568832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 2, 3, 3, 2].length) (baseStart_1568832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568832 prefixEnd_1568832 := by exact prefixLift 1568832
  have htrace : WordTrace (prefixWord ++ tailWord_1568832) baseStart_1568832 baseEnd_1568832 := by
    simpa [prefixWord, tailWord_1568832, baseEnd_1568832] using wordTrace_append hprefix tailTrace_1568832
  have hstable : (prefixWord ++ tailWord_1568832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568832).length < 2 ^ (prefixWord ++ tailWord_1568832).sum := by decide
  have hdescent : baseEnd_1568832 < baseStart_1568832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568879 : List Nat := [1, 1, 2, 1, 3, 5, 1, 1, 4, 2, 2]
def baseStart_1568879 : Nat := 118140960795 + 1568879 * 2 ^ 59
def prefixEnd_1568879 : Nat := 4983230072969 + 3 ^ 40 * 1568879 * 2
def baseEnd_1568879 : Nat := 805589015745272487397363

theorem tailTrace_1568879 : CollatzResearch.WordTrace tailWord_1568879 prefixEnd_1568879 805589015745272487397363 := by
  unfold tailWord_1568879
  simp only [CollatzResearch.WordTrace]
  refine ⟨57221718083226801046261691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38147812055484534030841127 57221718083226801046261691)
  ·
    refine ⟨85832577124840201569392537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57221718083226801046261691 85832577124840201569392537)
    ·
      refine ⟨64374432843630151177044403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85832577124840201569392537 64374432843630151177044403)
      ·
        refine ⟨96561649265445226765566605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64374432843630151177044403 96561649265445226765566605)
        ·
          refine ⟨36210618474541960037087477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96561649265445226765566605 36210618474541960037087477)
          ·
            refine ⟨3394745481988308753476951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36210618474541960037087477 3394745481988308753476951)
            ·
              refine ⟨5092118222982463130215427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3394745481988308753476951 5092118222982463130215427)
              ·
                refine ⟨7638177334473694695323141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5092118222982463130215427 7638177334473694695323141)
                ·
                  refine ⟨1432158250213817755373089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7638177334473694695323141 1432158250213817755373089)
                  ·
                    refine ⟨1074118687660363316529817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1432158250213817755373089 1074118687660363316529817)
                    ·
                      refine ⟨805589015745272487397363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074118687660363316529817 805589015745272487397363)
                      ·
                        rfl

theorem cell23_1568879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 2, 2].length) (baseStart_1568879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568879 prefixEnd_1568879 := by exact prefixLift 1568879
  have htrace : WordTrace (prefixWord ++ tailWord_1568879) baseStart_1568879 baseEnd_1568879 := by
    simpa [prefixWord, tailWord_1568879, baseEnd_1568879] using wordTrace_append hprefix tailTrace_1568879
  have hstable : (prefixWord ++ tailWord_1568879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568879).length < 2 ^ (prefixWord ++ tailWord_1568879).sum := by decide
  have hdescent : baseEnd_1568879 < baseStart_1568879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568915 : List Nat := [1, 1, 1, 2, 1, 2, 3, 5, 2, 5]
def baseStart_1568915 : Nat := 118140960795 + 1568915 * 2 ^ 59
def prefixEnd_1568915 : Nat := 4983230072969 + 3 ^ 40 * 1568915 * 2
def baseEnd_1568915 : Nat := 268535833682944782182399

theorem tailTrace_1568915 : CollatzResearch.WordTrace tailWord_1568915 prefixEnd_1568915 268535833682944782182399 := by
  unfold tailWord_1568915
  simp only [CollatzResearch.WordTrace]
  refine ⟨57223031111096379194572199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38148687407397586129714799 57223031111096379194572199)
  ·
    refine ⟨85834546666644568791858299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57223031111096379194572199 85834546666644568791858299)
    ·
      refine ⟨128751819999966853187787449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85834546666644568791858299 128751819999966853187787449)
      ·
        refine ⟨96563864999975139890840587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128751819999966853187787449 96563864999975139890840587)
        ·
          refine ⟨144845797499962709836260881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96563864999975139890840587 144845797499962709836260881)
          ·
            refine ⟨108634348124972032377195661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144845797499962709836260881 108634348124972032377195661)
            ·
              refine ⟨40737880546864512141448373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108634348124972032377195661 40737880546864512141448373)
              ·
                refine ⟨3819176301268548013260785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40737880546864512141448373 3819176301268548013260785)
                ·
                  refine ⟨2864382225951411009945589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3819176301268548013260785 2864382225951411009945589)
                  ·
                    refine ⟨268535833682944782182399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2864382225951411009945589 268535833682944782182399)
                    ·
                      rfl

theorem cell23_1568915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 5, 2, 5].length) (baseStart_1568915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568915 prefixEnd_1568915 := by exact prefixLift 1568915
  have htrace : WordTrace (prefixWord ++ tailWord_1568915) baseStart_1568915 baseEnd_1568915 := by
    simpa [prefixWord, tailWord_1568915, baseEnd_1568915] using wordTrace_append hprefix tailTrace_1568915
  have hstable : (prefixWord ++ tailWord_1568915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568915).length < 2 ^ (prefixWord ++ tailWord_1568915).sum := by decide
  have hdescent : baseEnd_1568915 < baseStart_1568915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568952 : List Nat := [2, 1, 2, 1, 2, 1, 4, 1, 1, 6, 2]
def baseStart_1568952 : Nat := 118140960795 + 1568952 * 2 ^ 59
def prefixEnd_1568952 : Nat := 4983230072969 + 3 ^ 40 * 1568952 * 2
def baseEnd_1568952 : Nat := 805626499833050701784527

theorem tailTrace_1568952 : CollatzResearch.WordTrace tailWord_1568952 prefixEnd_1568952 805626499833050701784527 := by
  unfold tailWord_1568952
  simp only [CollatzResearch.WordTrace]
  refine ⟨28612190305981167256834555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38149587074641556342446073 28612190305981167256834555)
  ·
    refine ⟨42918285458971750885251833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28612190305981167256834555 42918285458971750885251833)
    ·
      refine ⟨32188714094228813163938875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42918285458971750885251833 32188714094228813163938875)
      ·
        refine ⟨48283071141343219745908313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32188714094228813163938875 48283071141343219745908313)
        ·
          refine ⟨36212303356007414809431235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48283071141343219745908313 36212303356007414809431235)
          ·
            refine ⟨54318455034011122214146853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36212303356007414809431235 54318455034011122214146853)
            ·
              refine ⟨10184710318877085415152535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54318455034011122214146853 10184710318877085415152535)
              ·
                refine ⟨15277065478315628122728803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10184710318877085415152535 15277065478315628122728803)
                ·
                  refine ⟨22915598217473442184093205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15277065478315628122728803 22915598217473442184093205)
                  ·
                    refine ⟨1074168666444067602379369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22915598217473442184093205 1074168666444067602379369)
                    ·
                      refine ⟨805626499833050701784527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074168666444067602379369 805626499833050701784527)
                      ·
                        rfl

theorem cell23_1568952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 1, 1, 6, 2].length) (baseStart_1568952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568952 prefixEnd_1568952 := by exact prefixLift 1568952
  have htrace : WordTrace (prefixWord ++ tailWord_1568952) baseStart_1568952 baseEnd_1568952 := by
    simpa [prefixWord, tailWord_1568952, baseEnd_1568952] using wordTrace_append hprefix tailTrace_1568952
  have hstable : (prefixWord ++ tailWord_1568952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568952).length < 2 ^ (prefixWord ++ tailWord_1568952).sum := by decide
  have hdescent : baseEnd_1568952 < baseStart_1568952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568965 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_1568965 : Nat := 118140960795 + 1568965 * 2 ^ 59
def prefixEnd_1568965 : Nat := 4983230072969 + 3 ^ 40 * 1568965 * 2
def baseEnd_1568965 : Nat := 805633175081559150921967

theorem tailTrace_1568965 : CollatzResearch.WordTrace tailWord_1568965 prefixEnd_1568965 805633175081559150921967 := by
  unfold tailWord_1568965
  simp only [CollatzResearch.WordTrace]
  refine ⟨57224854760915237733892349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38149903173943491822594899 57224854760915237733892349)
  ·
    refine ⟨21459320535343214150209631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57224854760915237733892349 21459320535343214150209631)
    ·
      refine ⟨32188980803014821225314447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21459320535343214150209631 32188980803014821225314447)
      ·
        refine ⟨48283471204522231837971671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32188980803014821225314447 48283471204522231837971671)
        ·
          refine ⟨72425206806783347756957507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48283471204522231837971671 72425206806783347756957507)
          ·
            refine ⟨108637810210175021635436261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72425206806783347756957507 108637810210175021635436261)
            ·
              refine ⟨20369589414407816556644299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108637810210175021635436261 20369589414407816556644299)
              ·
                refine ⟨30554384121611724834966449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20369589414407816556644299 30554384121611724834966449)
                ·
                  refine ⟨22915788091208793626224837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30554384121611724834966449 22915788091208793626224837)
                  ·
                    refine ⟨4296710267101648804917157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22915788091208793626224837 4296710267101648804917157)
                    ·
                      refine ⟨805633175081559150921967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4296710267101648804917157 805633175081559150921967)
                      ·
                        rfl

theorem cell23_1568965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_1568965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568965 prefixEnd_1568965 := by exact prefixLift 1568965
  have htrace : WordTrace (prefixWord ++ tailWord_1568965) baseStart_1568965 baseEnd_1568965 := by
    simpa [prefixWord, tailWord_1568965, baseEnd_1568965] using wordTrace_append hprefix tailTrace_1568965
  have hstable : (prefixWord ++ tailWord_1568965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568965).length < 2 ^ (prefixWord ++ tailWord_1568965).sum := by decide
  have hdescent : baseEnd_1568965 < baseStart_1568965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1568992 : List Nat := [2, 1, 1, 3, 1, 3, 4, 2, 6]
def baseStart_1568992 : Nat := 118140960795 + 1568992 * 2 ^ 59
def prefixEnd_1568992 : Nat := 4983230072969 + 3 ^ 40 * 1568992 * 2
def baseEnd_1568992 : Nat := 89516337673247838364927

theorem tailTrace_1568992 : CollatzResearch.WordTrace tailWord_1568992 prefixEnd_1568992 89516337673247838364927 := by
  unfold tailWord_1568992
  simp only [CollatzResearch.WordTrace]
  refine ⟨28612919765908710672562615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38150559687878280896750153 28612919765908710672562615)
  ·
    refine ⟨42919379648863066008843923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28612919765908710672562615 42919379648863066008843923)
    ·
      refine ⟨64379069473294599013265885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42919379648863066008843923 64379069473294599013265885)
      ·
        refine ⟨24142151052485474629974707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64379069473294599013265885 24142151052485474629974707)
        ·
          refine ⟨36213226578728211944962061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24142151052485474629974707 36213226578728211944962061)
          ·
            refine ⟨13579959967023079479360773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36213226578728211944962061 13579959967023079479360773)
            ·
              refine ⟨2546242493816827402380145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13579959967023079479360773 2546242493816827402380145)
              ·
                refine ⟨1909681870362620551785109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2546242493816827402380145 1909681870362620551785109)
                ·
                  refine ⟨89516337673247838364927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1909681870362620551785109 89516337673247838364927)
                  ·
                    rfl

theorem cell23_1568992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 2, 6].length) (baseStart_1568992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1568992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1568992 prefixEnd_1568992 := by exact prefixLift 1568992
  have htrace : WordTrace (prefixWord ++ tailWord_1568992) baseStart_1568992 baseEnd_1568992 := by
    simpa [prefixWord, tailWord_1568992, baseEnd_1568992] using wordTrace_append hprefix tailTrace_1568992
  have hstable : (prefixWord ++ tailWord_1568992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1568992).length < 2 ^ (prefixWord ++ tailWord_1568992).sum := by decide
  have hdescent : baseEnd_1568992 < baseStart_1568992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1568992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569029 : List Nat := [1, 3, 1, 1, 2, 1, 2, 5, 2, 3, 2]
def baseStart_1569029 : Nat := 118140960795 + 1569029 * 2 ^ 59
def prefixEnd_1569029 : Nat := 4983230072969 + 3 ^ 40 * 1569029 * 2
def baseEnd_1569029 : Nat := 805666037843446900521673

theorem tailTrace_1569029 : CollatzResearch.WordTrace tailWord_1569029 prefixEnd_1569029 805666037843446900521673 := by
  unfold tailWord_1569029
  simp only [CollatzResearch.WordTrace]
  refine ⟨57227189032683376664222141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38151459355122251109481427 57227189032683376664222141)
  ·
    refine ⟨21460195887256266249083303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57227189032683376664222141 21460195887256266249083303)
    ·
      refine ⟨32190293830884399373624955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21460195887256266249083303 32190293830884399373624955)
      ·
        refine ⟨48285440746326599060437433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32190293830884399373624955 48285440746326599060437433)
        ·
          refine ⟨36214080559744949295328075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48285440746326599060437433 36214080559744949295328075)
          ·
            refine ⟨54321120839617423942992113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36214080559744949295328075 54321120839617423942992113)
            ·
              refine ⟨40740840629713067957244085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54321120839617423942992113 40740840629713067957244085)
              ·
                refine ⟨3819453809035600120991633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40740840629713067957244085 3819453809035600120991633)
                ·
                  refine ⟨2864590356776700090743725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3819453809035600120991633 2864590356776700090743725)
                  ·
                    refine ⟨1074221383791262534028897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2864590356776700090743725 1074221383791262534028897)
                    ·
                      refine ⟨805666037843446900521673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074221383791262534028897 805666037843446900521673)
                      ·
                        rfl

theorem cell23_1569029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 3, 2].length) (baseStart_1569029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569029 prefixEnd_1569029 := by exact prefixLift 1569029
  have htrace : WordTrace (prefixWord ++ tailWord_1569029) baseStart_1569029 baseEnd_1569029 := by
    simpa [prefixWord, tailWord_1569029, baseEnd_1569029] using wordTrace_append hprefix tailTrace_1569029
  have hstable : (prefixWord ++ tailWord_1569029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569029).length < 2 ^ (prefixWord ++ tailWord_1569029).sum := by decide
  have hdescent : baseEnd_1569029 < baseStart_1569029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569053 : List Nat := [1, 4, 2, 3, 2, 1, 2, 1, 3, 1, 3]
def baseStart_1569053 : Nat := 118140960795 + 1569053 * 2 ^ 59
def prefixEnd_1569053 : Nat := 4983230072969 + 3 ^ 40 * 1569053 * 2
def baseEnd_1569053 : Nat := 805678361379154806621563

theorem tailTrace_1569053 : CollatzResearch.WordTrace tailWord_1569053 prefixEnd_1569053 805678361379154806621563 := by
  unfold tailWord_1569053
  simp only [CollatzResearch.WordTrace]
  refine ⟨57228064384596428763095813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38152042923064285842063875 57228064384596428763095813)
  ·
    refine ⟨10730262072111830393080465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57228064384596428763095813 10730262072111830393080465)
    ·
      refine ⟨8047696554083872794810349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10730262072111830393080465 8047696554083872794810349)
      ·
        refine ⟨3017886207781452298053881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8047696554083872794810349 3017886207781452298053881)
        ·
          refine ⟨2263414655836089223540411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3017886207781452298053881 2263414655836089223540411)
          ·
            refine ⟨3395121983754133835310617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263414655836089223540411 3395121983754133835310617)
            ·
              refine ⟨2546341487815600376482963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3395121983754133835310617 2546341487815600376482963)
              ·
                refine ⟨3819512231723400564724445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546341487815600376482963 3819512231723400564724445)
                ·
                  refine ⟨1432317086896275211771667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3819512231723400564724445 1432317086896275211771667)
                  ·
                    refine ⟨2148475630344412817657501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1432317086896275211771667 2148475630344412817657501)
                    ·
                      refine ⟨805678361379154806621563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2148475630344412817657501 805678361379154806621563)
                      ·
                        rfl

theorem cell23_1569053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_1569053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569053 prefixEnd_1569053 := by exact prefixLift 1569053
  have htrace : WordTrace (prefixWord ++ tailWord_1569053) baseStart_1569053 baseEnd_1569053 := by
    simpa [prefixWord, tailWord_1569053, baseEnd_1569053] using wordTrace_append hprefix tailTrace_1569053
  have hstable : (prefixWord ++ tailWord_1569053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569053).length < 2 ^ (prefixWord ++ tailWord_1569053).sum := by decide
  have hdescent : baseEnd_1569053 < baseStart_1569053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569072 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 4]
def baseStart_1569072 : Nat := 118140960795 + 1569072 * 2 ^ 59
def prefixEnd_1569072 : Nat := 4983230072969 + 3 ^ 40 * 1569072 * 2
def baseEnd_1569072 : Nat := 805688117511590232283975

theorem tailTrace_1569072 : CollatzResearch.WordTrace tailWord_1569072 prefixEnd_1569072 805688117511590232283975 := by
  unfold tailWord_1569072
  simp only [CollatzResearch.WordTrace]
  refine ⟨28614378685763797504018735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38152504914351730005358313 28614378685763797504018735)
  ·
    refine ⟨42921568028645696256028103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28614378685763797504018735 42921568028645696256028103)
    ·
      refine ⟨64382352042968544384042155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42921568028645696256028103 64382352042968544384042155)
      ·
        refine ⟨96573528064452816576063233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64382352042968544384042155 96573528064452816576063233)
        ·
          refine ⟨72430146048339612432047425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96573528064452816576063233 72430146048339612432047425)
          ·
            refine ⟨54322609536254709324035569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72430146048339612432047425 54322609536254709324035569)
            ·
              refine ⟨40741957152191031993026677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54322609536254709324035569 40741957152191031993026677)
              ·
                refine ⟨3819558483017909249346251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40741957152191031993026677 3819558483017909249346251)
                ·
                  refine ⟨5729337724526863874019377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3819558483017909249346251 5729337724526863874019377)
                  ·
                    refine ⟨4297003293395147905514533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5729337724526863874019377 4297003293395147905514533)
                    ·
                      refine ⟨805688117511590232283975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4297003293395147905514533 805688117511590232283975)
                      ·
                        rfl

theorem cell23_1569072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 4].length) (baseStart_1569072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569072 prefixEnd_1569072 := by exact prefixLift 1569072
  have htrace : WordTrace (prefixWord ++ tailWord_1569072) baseStart_1569072 baseEnd_1569072 := by
    simpa [prefixWord, tailWord_1569072, baseEnd_1569072] using wordTrace_append hprefix tailTrace_1569072
  have hstable : (prefixWord ++ tailWord_1569072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569072).length < 2 ^ (prefixWord ++ tailWord_1569072).sum := by decide
  have hdescent : baseEnd_1569072 < baseStart_1569072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569076 : List Nat := [2, 5, 1, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_1569076 : Nat := 118140960795 + 1569076 * 2 ^ 59
def prefixEnd_1569076 : Nat := 4983230072969 + 3 ^ 40 * 1569076 * 2
def baseEnd_1569076 : Nat := 805690171434208216633957

theorem tailTrace_1569076 : CollatzResearch.WordTrace tailWord_1569076 prefixEnd_1569076 805690171434208216633957 := by
  unfold tailWord_1569076
  simp only [CollatzResearch.WordTrace]
  refine ⟨28614451631756551845591541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38152602175675402460788721 28614451631756551845591541)
  ·
    refine ⟨2682604840477176735524207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28614451631756551845591541 2682604840477176735524207)
    ·
      refine ⟨4023907260715765103286311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2682604840477176735524207 4023907260715765103286311)
      ·
        refine ⟨6035860891073647654929467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4023907260715765103286311 6035860891073647654929467)
        ·
          refine ⟨9053791336610471482394201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6035860891073647654929467 9053791336610471482394201)
          ·
            refine ⟨6790343502457853611795651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9053791336610471482394201 6790343502457853611795651)
            ·
              refine ⟨10185515253686780417693477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6790343502457853611795651 10185515253686780417693477)
              ·
                refine ⟨1909784110066271328317527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10185515253686780417693477 1909784110066271328317527)
                ·
                  refine ⟨2864676165099406992476291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1909784110066271328317527 2864676165099406992476291)
                  ·
                    refine ⟨4297014247649110488714437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2864676165099406992476291 4297014247649110488714437)
                    ·
                      refine ⟨805690171434208216633957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4297014247649110488714437 805690171434208216633957)
                      ·
                        rfl

theorem cell23_1569076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_1569076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569076 prefixEnd_1569076 := by exact prefixLift 1569076
  have htrace : WordTrace (prefixWord ++ tailWord_1569076) baseStart_1569076 baseEnd_1569076 := by
    simpa [prefixWord, tailWord_1569076, baseEnd_1569076] using wordTrace_append hprefix tailTrace_1569076
  have hstable : (prefixWord ++ tailWord_1569076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569076).length < 2 ^ (prefixWord ++ tailWord_1569076).sum := by decide
  have hdescent : baseEnd_1569076 < baseStart_1569076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569082 : List Nat := [3, 1, 1, 1, 4, 3, 1, 9]
def baseStart_1569082 : Nat := 118140960795 + 1569082 * 2 ^ 59
def prefixEnd_1569082 : Nat := 4983230072969 + 3 ^ 40 * 1569082 * 2
def baseEnd_1569082 : Nat := 29840490826597599746627

theorem tailTrace_1569082 : CollatzResearch.WordTrace tailWord_1569082 prefixEnd_1569082 29840490826597599746627 := by
  unfold tailWord_1569082
  simp only [CollatzResearch.WordTrace]
  refine ⟨14307280525372841678975375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38152748067660911143934333 14307280525372841678975375)
  ·
    refine ⟨21460920788059262518463063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14307280525372841678975375 21460920788059262518463063)
    ·
      refine ⟨32191381182088893777694595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21460920788059262518463063 32191381182088893777694595)
      ·
        refine ⟨48287071773133340666541893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32191381182088893777694595 48287071773133340666541893)
        ·
          refine ⟨9053825957462501374976605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48287071773133340666541893 9053825957462501374976605)
          ·
            refine ⟨3395184734048438015616227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9053825957462501374976605 3395184734048438015616227)
            ·
              refine ⟨5092777101072657023424341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3395184734048438015616227 5092777101072657023424341)
              ·
                refine ⟨29840490826597599746627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5092777101072657023424341 29840490826597599746627)
                ·
                  rfl

theorem cell23_1569082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 9].length) (baseStart_1569082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569082 prefixEnd_1569082 := by exact prefixLift 1569082
  have htrace : WordTrace (prefixWord ++ tailWord_1569082) baseStart_1569082 baseEnd_1569082 := by
    simpa [prefixWord, tailWord_1569082, baseEnd_1569082] using wordTrace_append hprefix tailTrace_1569082
  have hstable : (prefixWord ++ tailWord_1569082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569082).length < 2 ^ (prefixWord ++ tailWord_1569082).sum := by decide
  have hdescent : baseEnd_1569082 < baseStart_1569082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569116 : List Nat := [2, 2, 4, 3, 1, 1, 2, 8]
def baseStart_1569116 : Nat := 118140960795 + 1569116 * 2 ^ 59
def prefixEnd_1569116 : Nat := 4983230072969 + 3 ^ 40 * 1569116 * 2
def baseEnd_1569116 : Nat := 29841137431866224449399

theorem tailTrace_1569116 : CollatzResearch.WordTrace tailWord_1569116 prefixEnd_1569116 29841137431866224449399 := by
  unfold tailWord_1569116
  simp only [CollatzResearch.WordTrace]
  refine ⟨28615181091684095261319601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38153574788912127015092801 28615181091684095261319601)
  ·
    refine ⟨21461385818763071445989701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28615181091684095261319601 21461385818763071445989701)
    ·
      refine ⟨4024009841018075896123069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21461385818763071445989701 4024009841018075896123069)
      ·
        refine ⟨1509003690381778461046151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4024009841018075896123069 1509003690381778461046151)
        ·
          refine ⟨2263505535572667691569227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509003690381778461046151 2263505535572667691569227)
          ·
            refine ⟨3395258303359001537353841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263505535572667691569227 3395258303359001537353841)
            ·
              refine ⟨2546443727519251153015381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3395258303359001537353841 2546443727519251153015381)
              ·
                refine ⟨29841137431866224449399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2546443727519251153015381 29841137431866224449399)
                ·
                  rfl

theorem cell23_1569116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 8].length) (baseStart_1569116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569116 prefixEnd_1569116 := by exact prefixLift 1569116
  have htrace : WordTrace (prefixWord ++ tailWord_1569116) baseStart_1569116 baseEnd_1569116 := by
    simpa [prefixWord, tailWord_1569116, baseEnd_1569116] using wordTrace_append hprefix tailTrace_1569116
  have hstable : (prefixWord ++ tailWord_1569116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569116).length < 2 ^ (prefixWord ++ tailWord_1569116).sum := by decide
  have hdescent : baseEnd_1569116 < baseStart_1569116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569120 : List Nat := [2, 1, 1, 3, 6, 1, 2, 1, 2, 4]
def baseStart_1569120 : Nat := 118140960795 + 1569120 * 2 ^ 59
def prefixEnd_1569120 : Nat := 4983230072969 + 3 ^ 40 * 1569120 * 2
def baseEnd_1569120 : Nat := 268570921527668681494585

theorem tailTrace_1569120 : CollatzResearch.WordTrace tailWord_1569120 prefixEnd_1569120 268570921527668681494585 := by
  unfold tailWord_1569120
  simp only [CollatzResearch.WordTrace]
  refine ⟨28615254037676849602892407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38153672050235799470523209 28615254037676849602892407)
  ·
    refine ⟨42922881056515274404338611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28615254037676849602892407 42922881056515274404338611)
    ·
      refine ⟨64384321584772911606507917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42922881056515274404338611 64384321584772911606507917)
      ·
        refine ⟨24144120594289841852440469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64384321584772911606507917 24144120594289841852440469)
        ·
          refine ⟨1131755652857336336833147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24144120594289841852440469 1131755652857336336833147)
          ·
            refine ⟨1697633479286004505249721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131755652857336336833147 1697633479286004505249721)
            ·
              refine ⟨1273225109464503378937291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697633479286004505249721 1273225109464503378937291)
              ·
                refine ⟨1909837664196755068405937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273225109464503378937291 1909837664196755068405937)
                ·
                  refine ⟨1432378248147566301304453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1909837664196755068405937 1432378248147566301304453)
                  ·
                    refine ⟨268570921527668681494585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1432378248147566301304453 268570921527668681494585)
                    ·
                      rfl

theorem cell23_1569120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 6, 1, 2, 1, 2, 4].length) (baseStart_1569120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569120 prefixEnd_1569120 := by exact prefixLift 1569120
  have htrace : WordTrace (prefixWord ++ tailWord_1569120) baseStart_1569120 baseEnd_1569120 := by
    simpa [prefixWord, tailWord_1569120, baseEnd_1569120] using wordTrace_append hprefix tailTrace_1569120
  have hstable : (prefixWord ++ tailWord_1569120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569120).length < 2 ^ (prefixWord ++ tailWord_1569120).sum := by decide
  have hdescent : baseEnd_1569120 < baseStart_1569120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569136 : List Nat := [2, 1, 1, 1, 4, 4, 1, 1, 3, 3, 2]
def baseStart_1569136 : Nat := 118140960795 + 1569136 * 2 ^ 59
def prefixEnd_1569136 : Nat := 4983230072969 + 3 ^ 40 * 1569136 * 2
def baseEnd_1569136 : Nat := 805720980273477981883681

theorem tailTrace_1569136 : CollatzResearch.WordTrace tailWord_1569136 prefixEnd_1569136 805720980273477981883681 := by
  unfold tailWord_1569136
  simp only [CollatzResearch.WordTrace]
  refine ⟨28615545821647866969183631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38154061095530489292244841 28615545821647866969183631)
  ·
    refine ⟨42923318732471800453775447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28615545821647866969183631 42923318732471800453775447)
    ·
      refine ⟨64384978098707700680663171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42923318732471800453775447 64384978098707700680663171)
      ·
        refine ⟨96577467148061551020994757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64384978098707700680663171 96577467148061551020994757)
        ·
          refine ⟨18108275090261540816436517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96577467148061551020994757 18108275090261540816436517)
          ·
            refine ⟨3395301579424038903081847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18108275090261540816436517 3395301579424038903081847)
            ·
              refine ⟨5092952369136058354622771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3395301579424038903081847 5092952369136058354622771)
              ·
                refine ⟨7639428553704087531934157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5092952369136058354622771 7639428553704087531934157)
                ·
                  refine ⟨2864785707639032824475309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7639428553704087531934157 2864785707639032824475309)
                  ·
                    refine ⟨1074294640364637309178241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2864785707639032824475309 1074294640364637309178241)
                    ·
                      refine ⟨805720980273477981883681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074294640364637309178241 805720980273477981883681)
                      ·
                        rfl

theorem cell23_1569136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 1, 3, 3, 2].length) (baseStart_1569136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569136 prefixEnd_1569136 := by exact prefixLift 1569136
  have htrace : WordTrace (prefixWord ++ tailWord_1569136) baseStart_1569136 baseEnd_1569136 := by
    simpa [prefixWord, tailWord_1569136, baseEnd_1569136] using wordTrace_append hprefix tailTrace_1569136
  have hstable : (prefixWord ++ tailWord_1569136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569136).length < 2 ^ (prefixWord ++ tailWord_1569136).sum := by decide
  have hdescent : baseEnd_1569136 < baseStart_1569136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569183 : List Nat := [1, 1, 2, 5, 1, 1, 1, 5, 2, 2, 2]
def baseStart_1569183 : Nat := 118140960795 + 1569183 * 2 ^ 59
def prefixEnd_1569183 : Nat := 4983230072969 + 3 ^ 40 * 1569183 * 2
def baseEnd_1569183 : Nat := 805745113864239297995965

theorem tailTrace_1569183 : CollatzResearch.WordTrace tailWord_1569183 prefixEnd_1569183 805745113864239297995965 := by
  unfold tailWord_1569183
  simp only [CollatzResearch.WordTrace]
  refine ⟨57232805874125460965328203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38155203916083640643552135 57232805874125460965328203)
  ·
    refine ⟨85849208811188191447992305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57232805874125460965328203 85849208811188191447992305)
    ·
      refine ⟨64386906608391143585994229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85849208811188191447992305 64386906608391143585994229)
      ·
        refine ⟨6036272494536669711186959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64386906608391143585994229 6036272494536669711186959)
        ·
          refine ⟨9054408741805004566780439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6036272494536669711186959 9054408741805004566780439)
          ·
            refine ⟨13581613112707506850170659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9054408741805004566780439 13581613112707506850170659)
            ·
              refine ⟨20372419669061260275255989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13581613112707506850170659 20372419669061260275255989)
              ·
                refine ⟨1909914343974493150805249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20372419669061260275255989 1909914343974493150805249)
                ·
                  refine ⟨1432435757980869863103937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1909914343974493150805249 1432435757980869863103937)
                  ·
                    refine ⟨1074326818485652397327953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1432435757980869863103937 1074326818485652397327953)
                    ·
                      refine ⟨805745113864239297995965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074326818485652397327953 805745113864239297995965)
                      ·
                        rfl

theorem cell23_1569183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_1569183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569183 prefixEnd_1569183 := by exact prefixLift 1569183
  have htrace : WordTrace (prefixWord ++ tailWord_1569183) baseStart_1569183 baseEnd_1569183 := by
    simpa [prefixWord, tailWord_1569183, baseEnd_1569183] using wordTrace_append hprefix tailTrace_1569183
  have hstable : (prefixWord ++ tailWord_1569183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569183).length < 2 ^ (prefixWord ++ tailWord_1569183).sum := by decide
  have hdescent : baseEnd_1569183 < baseStart_1569183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569232 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 4, 8]
def baseStart_1569232 : Nat := 118140960795 + 1569232 * 2 ^ 59
def prefixEnd_1569232 : Nat := 4983230072969 + 3 ^ 40 * 1569232 * 2
def baseEnd_1569232 : Nat := 268590091472103202094413

theorem tailTrace_1569232 : CollatzResearch.WordTrace tailWord_1569232 prefixEnd_1569232 268590091472103202094413 := by
  unfold tailWord_1569232
  simp only [CollatzResearch.WordTrace]
  refine ⟨28617296525473971166930975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38156395367298628222574633 28617296525473971166930975)
  ·
    refine ⟨42925944788210956750396463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28617296525473971166930975 42925944788210956750396463)
    ·
      refine ⟨64388917182316435125594695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42925944788210956750396463 64388917182316435125594695)
      ·
        refine ⟨96583375773474652688392043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64388917182316435125594695 96583375773474652688392043)
        ·
          refine ⟨144875063660211979032588065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96583375773474652688392043 144875063660211979032588065)
          ·
            refine ⟨108656297745158984274441049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144875063660211979032588065 108656297745158984274441049)
            ·
              refine ⟨81492223308869238205830787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108656297745158984274441049 81492223308869238205830787)
              ·
                refine ⟨122238334963303857308746181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81492223308869238205830787 122238334963303857308746181)
                ·
                  refine ⟨22919687805619473245389909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122238334963303857308746181 22919687805619473245389909)
                  ·
                    refine ⟨268590091472103202094413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 22919687805619473245389909 268590091472103202094413)
                    ·
                      rfl

theorem cell23_1569232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 4, 8].length) (baseStart_1569232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569232 prefixEnd_1569232 := by exact prefixLift 1569232
  have htrace : WordTrace (prefixWord ++ tailWord_1569232) baseStart_1569232 baseEnd_1569232 := by
    simpa [prefixWord, tailWord_1569232, baseEnd_1569232] using wordTrace_append hprefix tailTrace_1569232
  have hstable : (prefixWord ++ tailWord_1569232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569232).length < 2 ^ (prefixWord ++ tailWord_1569232).sum := by decide
  have hdescent : baseEnd_1569232 < baseStart_1569232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569234 : List Nat := [3, 2, 2, 4, 1, 1, 3, 1, 2, 2, 2]
def baseStart_1569234 : Nat := 118140960795 + 1569234 * 2 ^ 59
def prefixEnd_1569234 : Nat := 4983230072969 + 3 ^ 40 * 1569234 * 2
def baseEnd_1569234 : Nat := 805771301377618598458231

theorem tailTrace_1569234 : CollatzResearch.WordTrace tailWord_1569234 prefixEnd_1569234 805771301377618598458231 := by
  unfold tailWord_1569234
  simp only [CollatzResearch.WordTrace]
  refine ⟨14308666499235174168858689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38156443997960464450289837 14308666499235174168858689)
  ·
    refine ⟨10731499874426380626644017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14308666499235174168858689 10731499874426380626644017)
    ·
      refine ⟨8048624905819785469983013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10731499874426380626644017 8048624905819785469983013)
      ·
        refine ⟨1509117169841209775621815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8048624905819785469983013 1509117169841209775621815)
        ·
          refine ⟨2263675754761814663432723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509117169841209775621815 2263675754761814663432723)
          ·
            refine ⟨3395513632142721995149085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263675754761814663432723 3395513632142721995149085)
            ·
              refine ⟨1273317612053520748180907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3395513632142721995149085 1273317612053520748180907)
              ·
                refine ⟨1909976418080281122271361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273317612053520748180907 1909976418080281122271361)
                ·
                  refine ⟨1432482313560210841703521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1909976418080281122271361 1432482313560210841703521)
                  ·
                    refine ⟨1074361735170158131277641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1432482313560210841703521 1074361735170158131277641)
                    ·
                      refine ⟨805771301377618598458231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074361735170158131277641 805771301377618598458231)
                      ·
                        rfl

theorem cell23_1569234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_1569234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569234 prefixEnd_1569234 := by exact prefixLift 1569234
  have htrace : WordTrace (prefixWord ++ tailWord_1569234) baseStart_1569234 baseEnd_1569234 := by
    simpa [prefixWord, tailWord_1569234, baseEnd_1569234] using wordTrace_append hprefix tailTrace_1569234
  have hstable : (prefixWord ++ tailWord_1569234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569234).length < 2 ^ (prefixWord ++ tailWord_1569234).sum := by decide
  have hdescent : baseEnd_1569234 < baseStart_1569234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569259 : List Nat := [1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 3]
def baseStart_1569259 : Nat := 118140960795 + 1569259 * 2 ^ 59
def prefixEnd_1569259 : Nat := 4983230072969 + 3 ^ 40 * 1569259 * 2
def baseEnd_1569259 : Nat := 805784138393981000645615

theorem tailTrace_1569259 : CollatzResearch.WordTrace tailWord_1569259 prefixEnd_1569259 805784138393981000645615 := by
  unfold tailWord_1569259
  simp only [CollatzResearch.WordTrace]
  refine ⟨57235577821850125945094831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38157051881233417296729887 57235577821850125945094831)
  ·
    refine ⟨85853366732775188917642247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57235577821850125945094831 85853366732775188917642247)
    ·
      refine ⟨128780050099162783376463371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85853366732775188917642247 128780050099162783376463371)
      ·
        refine ⟨193170075148744175064695057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128780050099162783376463371 193170075148744175064695057)
        ·
          refine ⟨144877556361558131298521293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193170075148744175064695057 144877556361558131298521293)
          ·
            refine ⟨54329083635584299236945485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 144877556361558131298521293 54329083635584299236945485)
            ·
              refine ⟨20373406363344112213854557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54329083635584299236945485 20373406363344112213854557)
              ·
                refine ⟨7640027386254042080195459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20373406363344112213854557 7640027386254042080195459)
                ·
                  refine ⟨11460041079381063120293189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7640027386254042080195459 11460041079381063120293189)
                  ·
                    refine ⟨2148757702383949335054973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11460041079381063120293189 2148757702383949335054973)
                    ·
                      refine ⟨805784138393981000645615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2148757702383949335054973 805784138393981000645615)
                      ·
                        rfl

theorem cell23_1569259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 3, 1, 4, 3].length) (baseStart_1569259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569259 prefixEnd_1569259 := by exact prefixLift 1569259
  have htrace : WordTrace (prefixWord ++ tailWord_1569259) baseStart_1569259 baseEnd_1569259 := by
    simpa [prefixWord, tailWord_1569259, baseEnd_1569259] using wordTrace_append hprefix tailTrace_1569259
  have hstable : (prefixWord ++ tailWord_1569259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569259).length < 2 ^ (prefixWord ++ tailWord_1569259).sum := by decide
  have hdescent : baseEnd_1569259 < baseStart_1569259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569279 : List Nat := [1, 1, 2, 2, 1, 2, 4, 4, 6]
def baseStart_1569279 : Nat := 118140960795 + 1569279 * 2 ^ 59
def prefixEnd_1569279 : Nat := 4983230072969 + 3 ^ 40 * 1569279 * 2
def baseEnd_1569279 : Nat := 89532712000785658043947

theorem tailTrace_1569279 : CollatzResearch.WordTrace tailWord_1569279 prefixEnd_1569279 89532712000785658043947 := by
  unfold tailWord_1569279
  simp only [CollatzResearch.WordTrace]
  refine ⟨57236307281777669360822891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38157538187851779573881927 57236307281777669360822891)
  ·
    refine ⟨85854460922666504041234337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57236307281777669360822891 85854460922666504041234337)
    ·
      refine ⟨64390845691999878030925753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85854460922666504041234337 64390845691999878030925753)
      ·
        refine ⟨48293134268999908523194315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64390845691999878030925753 48293134268999908523194315)
        ·
          refine ⟨72439701403499862784791473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48293134268999908523194315 72439701403499862784791473)
          ·
            refine ⟨54329776052624897088593605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72439701403499862784791473 54329776052624897088593605)
            ·
              refine ⟨10186833009867168204111301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54329776052624897088593605 10186833009867168204111301)
              ·
                refine ⟨1910031189350094038270869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10186833009867168204111301 1910031189350094038270869)
                ·
                  refine ⟨89532712000785658043947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1910031189350094038270869 89532712000785658043947)
                  ·
                    rfl

theorem cell23_1569279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 4, 6].length) (baseStart_1569279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569279 prefixEnd_1569279 := by exact prefixLift 1569279
  have htrace : WordTrace (prefixWord ++ tailWord_1569279) baseStart_1569279 baseEnd_1569279 := by
    simpa [prefixWord, tailWord_1569279, baseEnd_1569279] using wordTrace_append hprefix tailTrace_1569279
  have hstable : (prefixWord ++ tailWord_1569279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569279).length < 2 ^ (prefixWord ++ tailWord_1569279).sum := by decide
  have hdescent : baseEnd_1569279 < baseStart_1569279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569289 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 2, 5, 3]
def baseStart_1569289 : Nat := 118140960795 + 1569289 * 2 ^ 59
def prefixEnd_1569289 : Nat := 4983230072969 + 3 ^ 40 * 1569289 * 2
def baseEnd_1569289 : Nat := 805799542813615883270477

theorem tailTrace_1569289 : CollatzResearch.WordTrace tailWord_1569289 prefixEnd_1569289 805799542813615883270477 := by
  unfold tailWord_1569289
  simp only [CollatzResearch.WordTrace]
  refine ⟨57236672011741441068686921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38157781341160960712457947 57236672011741441068686921)
  ·
    refine ⟨42927504008806080801515191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57236672011741441068686921 42927504008806080801515191)
    ·
      refine ⟨64391256013209121202272787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42927504008806080801515191 64391256013209121202272787)
      ·
        refine ⟨96586884019813681803409181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64391256013209121202272787 96586884019813681803409181)
        ·
          refine ⟨36220081507430130676278443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96586884019813681803409181 36220081507430130676278443)
          ·
            refine ⟨54330122261145196014417665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36220081507430130676278443 54330122261145196014417665)
            ·
              refine ⟨40747591695858897010813249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54330122261145196014417665 40747591695858897010813249)
              ·
                refine ⟨30560693771894172758109937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40747591695858897010813249 30560693771894172758109937)
                ·
                  refine ⟨22920520328920629568582453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30560693771894172758109937 22920520328920629568582453)
                  ·
                    refine ⟨2148798780836309022054605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22920520328920629568582453 2148798780836309022054605)
                    ·
                      refine ⟨805799542813615883270477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2148798780836309022054605 805799542813615883270477)
                      ·
                        rfl

theorem cell23_1569289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 2, 5, 3].length) (baseStart_1569289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569289 prefixEnd_1569289 := by exact prefixLift 1569289
  have htrace : WordTrace (prefixWord ++ tailWord_1569289) baseStart_1569289 baseEnd_1569289 := by
    simpa [prefixWord, tailWord_1569289, baseEnd_1569289] using wordTrace_append hprefix tailTrace_1569289
  have hstable : (prefixWord ++ tailWord_1569289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569289).length < 2 ^ (prefixWord ++ tailWord_1569289).sum := by decide
  have hdescent : baseEnd_1569289 < baseStart_1569289 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569333 : List Nat := [1, 3, 3, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_1569333 : Nat := 118140960795 + 1569333 * 2 ^ 59
def prefixEnd_1569333 : Nat := 4983230072969 + 3 ^ 40 * 1569333 * 2
def baseEnd_1569333 : Nat := 805822135962413711120275

theorem tailTrace_1569333 : CollatzResearch.WordTrace tailWord_1569333 prefixEnd_1569333 805822135962413711120275 := by
  unfold tailWord_1569333
  simp only [CollatzResearch.WordTrace]
  refine ⟨57238276823582036583288653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38158851215721357722192435 57238276823582036583288653)
  ·
    refine ⟨21464353808843263718733245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57238276823582036583288653 21464353808843263718733245)
    ·
      refine ⟨8049132678316223894524967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21464353808843263718733245 8049132678316223894524967)
      ·
        refine ⟨12073699017474335841787451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8049132678316223894524967 12073699017474335841787451)
        ·
          refine ⟨18110548526211503762681177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12073699017474335841787451 18110548526211503762681177)
          ·
            refine ⟨13582911394658627822010883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18110548526211503762681177 13582911394658627822010883)
            ·
              refine ⟨20374367091987941733016325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13582911394658627822010883 20374367091987941733016325)
              ·
                refine ⟨3820193829747739074940561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20374367091987941733016325 3820193829747739074940561)
                ·
                  refine ⟨2865145372310804306205421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3820193829747739074940561 2865145372310804306205421)
                  ·
                    refine ⟨1074429514616551614827033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2865145372310804306205421 1074429514616551614827033)
                    ·
                      refine ⟨805822135962413711120275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074429514616551614827033 805822135962413711120275)
                      ·
                        rfl

theorem cell23_1569333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_1569333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569333 prefixEnd_1569333 := by exact prefixLift 1569333
  have htrace : WordTrace (prefixWord ++ tailWord_1569333) baseStart_1569333 baseEnd_1569333 := by
    simpa [prefixWord, tailWord_1569333, baseEnd_1569333] using wordTrace_append hprefix tailTrace_1569333
  have hstable : (prefixWord ++ tailWord_1569333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569333).length < 2 ^ (prefixWord ++ tailWord_1569333).sum := by decide
  have hdescent : baseEnd_1569333 < baseStart_1569333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569334 : List Nat := [5, 1, 2, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1569334 : Nat := 118140960795 + 1569334 * 2 ^ 59
def prefixEnd_1569334 : Nat := 4983230072969 + 3 ^ 40 * 1569334 * 2
def baseEnd_1569334 : Nat := 268607549814356069069257

theorem tailTrace_1569334 : CollatzResearch.WordTrace tailWord_1569334 prefixEnd_1569334 268607549814356069069257 := by
  unfold tailWord_1569334
  simp only [CollatzResearch.WordTrace]
  refine ⟨3577394581036150859629691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38158875531052275836050037 3577394581036150859629691)
  ·
    refine ⟨5366091871554226289444537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3577394581036150859629691 5366091871554226289444537)
    ·
      refine ⟨4024568903665669717083403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5366091871554226289444537 4024568903665669717083403)
      ·
        refine ⟨6036853355498504575625105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4024568903665669717083403 6036853355498504575625105)
        ·
          refine ⟨4527640016623878431718829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6036853355498504575625105 4527640016623878431718829)
          ·
            refine ⟨1697865006233954411894561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4527640016623878431718829 1697865006233954411894561)
            ·
              refine ⟨1273398754675465808920921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1697865006233954411894561 1273398754675465808920921)
              ·
                refine ⟨955049066006599356690691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273398754675465808920921 955049066006599356690691)
                ·
                  refine ⟨1432573599009899035036037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955049066006599356690691 1432573599009899035036037)
                  ·
                    refine ⟨268607549814356069069257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1432573599009899035036037 268607549814356069069257)
                    ·
                      rfl

theorem cell23_1569334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1569334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569334 prefixEnd_1569334 := by exact prefixLift 1569334
  have htrace : WordTrace (prefixWord ++ tailWord_1569334) baseStart_1569334 baseEnd_1569334 := by
    simpa [prefixWord, tailWord_1569334, baseEnd_1569334] using wordTrace_append hprefix tailTrace_1569334
  have hstable : (prefixWord ++ tailWord_1569334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569334).length < 2 ^ (prefixWord ++ tailWord_1569334).sum := by decide
  have hdescent : baseEnd_1569334 < baseStart_1569334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569356 : List Nat := [2, 2, 1, 3, 1, 2, 4, 1, 1, 6]
def baseStart_1569356 : Nat := 118140960795 + 1569356 * 2 ^ 59
def prefixEnd_1569356 : Nat := 4983230072969 + 3 ^ 40 * 1569356 * 2
def baseEnd_1569356 : Nat := 268611315339155707044223

theorem tailTrace_1569356 : CollatzResearch.WordTrace tailWord_1569356 prefixEnd_1569356 268611315339155707044223 := by
  unfold tailWord_1569356
  simp only [CollatzResearch.WordTrace]
  refine ⟨28619557851249355755687961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38159410468332474340917281 28619557851249355755687961)
  ·
    refine ⟨21464668388437016816765971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28619557851249355755687961 21464668388437016816765971)
    ·
      refine ⟨32197002582655525225148957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21464668388437016816765971 32197002582655525225148957)
      ·
        refine ⟨12073875968495821959430859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32197002582655525225148957 12073875968495821959430859)
        ·
          refine ⟨18110813952743732939146289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12073875968495821959430859 18110813952743732939146289)
          ·
            refine ⟨13583110464557799704359717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18110813952743732939146289 13583110464557799704359717)
            ·
              refine ⟨2546833212104587444567447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13583110464557799704359717 2546833212104587444567447)
              ·
                refine ⟨3820249818156881166851171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546833212104587444567447 3820249818156881166851171)
                ·
                  refine ⟨5730374727235321750276757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820249818156881166851171 5730374727235321750276757)
                  ·
                    refine ⟨268611315339155707044223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5730374727235321750276757 268611315339155707044223)
                    ·
                      rfl

theorem cell23_1569356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_1569356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569356 prefixEnd_1569356 := by exact prefixLift 1569356
  have htrace : WordTrace (prefixWord ++ tailWord_1569356) baseStart_1569356 baseEnd_1569356 := by
    simpa [prefixWord, tailWord_1569356, baseEnd_1569356] using wordTrace_append hprefix tailTrace_1569356
  have hstable : (prefixWord ++ tailWord_1569356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569356).length < 2 ^ (prefixWord ++ tailWord_1569356).sum := by decide
  have hdescent : baseEnd_1569356 < baseStart_1569356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569359 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 6]
def baseStart_1569359 : Nat := 118140960795 + 1569359 * 2 ^ 59
def prefixEnd_1569359 : Nat := 4983230072969 + 3 ^ 40 * 1569359 * 2
def baseEnd_1569359 : Nat := 805835486459430609395155

theorem tailTrace_1569359 : CollatzResearch.WordTrace tailWord_1569359 prefixEnd_1569359 805835486459430609395155 := by
  unfold tailWord_1569359
  simp only [CollatzResearch.WordTrace]
  refine ⟨57239225121487843023735131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38159483414325228682490087 57239225121487843023735131)
  ·
    refine ⟨85858837682231764535602697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57239225121487843023735131 85858837682231764535602697)
    ·
      refine ⟨64394128261673823401702023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85858837682231764535602697 64394128261673823401702023)
      ·
        refine ⟨96591192392510735102553035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64394128261673823401702023 96591192392510735102553035)
        ·
          refine ⟨144886788588766102653829553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96591192392510735102553035 144886788588766102653829553)
          ·
            refine ⟨108665091441574576990372165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144886788588766102653829553 108665091441574576990372165)
            ·
              refine ⟨20374704645295233185694781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108665091441574576990372165 20374704645295233185694781)
              ·
                refine ⟨7640514241985712444635543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20374704645295233185694781 7640514241985712444635543)
                ·
                  refine ⟨11460771362978568666953315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7640514241985712444635543 11460771362978568666953315)
                  ·
                    refine ⟨17191157044467853000429973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11460771362978568666953315 17191157044467853000429973)
                    ·
                      refine ⟨805835486459430609395155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17191157044467853000429973 805835486459430609395155)
                      ·
                        rfl

theorem cell23_1569359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 1, 6].length) (baseStart_1569359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569359 prefixEnd_1569359 := by exact prefixLift 1569359
  have htrace : WordTrace (prefixWord ++ tailWord_1569359) baseStart_1569359 baseEnd_1569359 := by
    simpa [prefixWord, tailWord_1569359, baseEnd_1569359] using wordTrace_append hprefix tailTrace_1569359
  have hstable : (prefixWord ++ tailWord_1569359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569359).length < 2 ^ (prefixWord ++ tailWord_1569359).sum := by decide
  have hdescent : baseEnd_1569359 < baseStart_1569359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569376 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 4]
def baseStart_1569376 : Nat := 118140960795 + 1569376 * 2 ^ 59
def prefixEnd_1569376 : Nat := 4983230072969 + 3 ^ 40 * 1569376 * 2
def baseEnd_1569376 : Nat := 805844215630557042882577

theorem tailTrace_1569376 : CollatzResearch.WordTrace tailWord_1569376 prefixEnd_1569376 805844215630557042882577 := by
  unfold tailWord_1569376
  simp only [CollatzResearch.WordTrace]
  refine ⟨28619922581213127463551991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38159896774950836618069321 28619922581213127463551991)
  ·
    refine ⟨42929883871819691195327987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28619922581213127463551991 42929883871819691195327987)
    ·
      refine ⟨64394825807729536792991981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42929883871819691195327987 64394825807729536792991981)
      ·
        refine ⟨24148059677898576297371993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64394825807729536792991981 24148059677898576297371993)
        ·
          refine ⟨18111044758423932223028995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24148059677898576297371993 18111044758423932223028995)
          ·
            refine ⟨27166567137635898334543493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18111044758423932223028995 27166567137635898334543493)
            ·
              refine ⟨5093731338306730937726905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27166567137635898334543493 5093731338306730937726905)
              ·
                refine ⟨3820298503730048203295179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5093731338306730937726905 3820298503730048203295179)
                ·
                  refine ⟨5730447755595072304942769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820298503730048203295179 5730447755595072304942769)
                  ·
                    refine ⟨4297835816696304228707077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5730447755595072304942769 4297835816696304228707077)
                    ·
                      refine ⟨805844215630557042882577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4297835816696304228707077 805844215630557042882577)
                      ·
                        rfl

theorem cell23_1569376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 2, 4].length) (baseStart_1569376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569376 prefixEnd_1569376 := by exact prefixLift 1569376
  have htrace : WordTrace (prefixWord ++ tailWord_1569376) baseStart_1569376 baseEnd_1569376 := by
    simpa [prefixWord, tailWord_1569376, baseEnd_1569376] using wordTrace_append hprefix tailTrace_1569376
  have hstable : (prefixWord ++ tailWord_1569376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569376).length < 2 ^ (prefixWord ++ tailWord_1569376).sum := by decide
  have hdescent : baseEnd_1569376 < baseStart_1569376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569390 : List Nat := [4, 1, 2, 2, 2, 1, 3, 2, 2, 4]
def baseStart_1569390 : Nat := 118140960795 + 1569390 * 2 ^ 59
def prefixEnd_1569390 : Nat := 4983230072969 + 3 ^ 40 * 1569390 * 2
def baseEnd_1569390 : Nat := 268617134786573329369171

theorem tailTrace_1569390 : CollatzResearch.WordTrace tailWord_1569390 prefixEnd_1569390 268617134786573329369171 := by
  unfold tailWord_1569390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7155044473046941914764203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38160237189583690212075749 7155044473046941914764203)
  ·
    refine ⟨10732566709570412872146305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7155044473046941914764203 10732566709570412872146305)
    ·
      refine ⟨8049425032177809654109729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10732566709570412872146305 8049425032177809654109729)
      ·
        refine ⟨6037068774133357240582297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8049425032177809654109729 6037068774133357240582297)
        ·
          refine ⟨4527801580600017930436723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6037068774133357240582297 4527801580600017930436723)
          ·
            refine ⟨6791702370900026895655085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4527801580600017930436723 6791702370900026895655085)
            ·
              refine ⟨2546888389087510085870657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6791702370900026895655085 2546888389087510085870657)
              ·
                refine ⟨1910166291815632564402993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2546888389087510085870657 1910166291815632564402993)
                ·
                  refine ⟨1432624718861724423302245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1910166291815632564402993 1432624718861724423302245)
                  ·
                    refine ⟨268617134786573329369171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1432624718861724423302245 268617134786573329369171)
                    ·
                      rfl

theorem cell23_1569390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 3, 2, 2, 4].length) (baseStart_1569390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569390 prefixEnd_1569390 := by exact prefixLift 1569390
  have htrace : WordTrace (prefixWord ++ tailWord_1569390) baseStart_1569390 baseEnd_1569390 := by
    simpa [prefixWord, tailWord_1569390, baseEnd_1569390] using wordTrace_append hprefix tailTrace_1569390
  have hstable : (prefixWord ++ tailWord_1569390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569390).length < 2 ^ (prefixWord ++ tailWord_1569390).sum := by decide
  have hdescent : baseEnd_1569390 < baseStart_1569390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569399 : List Nat := [1, 1, 3, 1, 1, 3, 2, 1, 1, 9]
def baseStart_1569399 : Nat := 118140960795 + 1569399 * 2 ^ 59
def prefixEnd_1569399 : Nat := 4983230072969 + 3 ^ 40 * 1569399 * 2
def baseEnd_1569399 : Nat := 268618675228536817631657

theorem tailTrace_1569399 : CollatzResearch.WordTrace tailWord_1569399 prefixEnd_1569399 268618675228536817631657 := by
  unfold tailWord_1569399
  simp only [CollatzResearch.WordTrace]
  refine ⟨57240684041342929855191251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38160456027561953236794167 57240684041342929855191251)
  ·
    refine ⟨85861026062014394782786877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57240684041342929855191251 85861026062014394782786877)
    ·
      refine ⟨32197884773255398043545079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85861026062014394782786877 32197884773255398043545079)
      ·
        refine ⟨48296827159883097065317619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32197884773255398043545079 48296827159883097065317619)
        ·
          refine ⟨72445240739824645597976429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48296827159883097065317619 72445240739824645597976429)
          ·
            refine ⟨27166965277434242099241161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72445240739824645597976429 27166965277434242099241161)
            ·
              refine ⟨20375223958075681574430871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27166965277434242099241161 20375223958075681574430871)
              ·
                refine ⟨30562835937113522361646307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20375223958075681574430871 30562835937113522361646307)
                ·
                  refine ⟨45844253905670283542469461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30562835937113522361646307 45844253905670283542469461)
                  ·
                    refine ⟨268618675228536817631657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 45844253905670283542469461 268618675228536817631657)
                    ·
                      rfl

theorem cell23_1569399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 9].length) (baseStart_1569399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569399 prefixEnd_1569399 := by exact prefixLift 1569399
  have htrace : WordTrace (prefixWord ++ tailWord_1569399) baseStart_1569399 baseEnd_1569399 := by
    simpa [prefixWord, tailWord_1569399, baseEnd_1569399] using wordTrace_append hprefix tailTrace_1569399
  have hstable : (prefixWord ++ tailWord_1569399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569399).length < 2 ^ (prefixWord ++ tailWord_1569399).sum := by decide
  have hdescent : baseEnd_1569399 < baseStart_1569399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569413 : List Nat := [1, 3, 1, 1, 4, 2, 3, 1, 1, 3, 3]
def baseStart_1569413 : Nat := 118140960795 + 1569413 * 2 ^ 59
def prefixEnd_1569413 : Nat := 4983230072969 + 3 ^ 40 * 1569413 * 2
def baseEnd_1569413 : Nat := 805863214414773398119907

theorem tailTrace_1569413 : CollatzResearch.WordTrace tailWord_1569413 prefixEnd_1569413 805863214414773398119907 := by
  unfold tailWord_1569413
  simp only [CollatzResearch.WordTrace]
  refine ⟨57241194663292210246200893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38160796442194806830800595 57241194663292210246200893)
  ·
    refine ⟨21465447998734578842325335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57241194663292210246200893 21465447998734578842325335)
    ·
      refine ⟨32198171998101868263488003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21465447998734578842325335 32198171998101868263488003)
      ·
        refine ⟨48297257997152802395232005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32198171998101868263488003 48297257997152802395232005)
        ·
          refine ⟨9055735874466150449106001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48297257997152802395232005 9055735874466150449106001)
          ·
            refine ⟨6791801905849612836829501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9055735874466150449106001 6791801905849612836829501)
            ·
              refine ⟨2546925714693604813811063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6791801905849612836829501 2546925714693604813811063)
              ·
                refine ⟨3820388572040407220716595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2546925714693604813811063 3820388572040407220716595)
                ·
                  refine ⟨5730582858060610831074893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820388572040407220716595 5730582858060610831074893)
                  ·
                    refine ⟨2148968571772729061653085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5730582858060610831074893 2148968571772729061653085)
                    ·
                      refine ⟨805863214414773398119907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2148968571772729061653085 805863214414773398119907)
                      ·
                        rfl

theorem cell23_1569413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_1569413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569413 prefixEnd_1569413 := by exact prefixLift 1569413
  have htrace : WordTrace (prefixWord ++ tailWord_1569413) baseStart_1569413 baseEnd_1569413 := by
    simpa [prefixWord, tailWord_1569413, baseEnd_1569413] using wordTrace_append hprefix tailTrace_1569413
  have hstable : (prefixWord ++ tailWord_1569413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569413).length < 2 ^ (prefixWord ++ tailWord_1569413).sum := by decide
  have hdescent : baseEnd_1569413 < baseStart_1569413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569419 : List Nat := [1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 8]
def baseStart_1569419 : Nat := 118140960795 + 1569419 * 2 ^ 59
def prefixEnd_1569419 : Nat := 4983230072969 + 3 ^ 40 * 1569419 * 2
def baseEnd_1569419 : Nat := 805866295298700374644879

theorem tailTrace_1569419 : CollatzResearch.WordTrace tailWord_1569419 prefixEnd_1569419 805866295298700374644879 := by
  unfold tailWord_1569419
  simp only [CollatzResearch.WordTrace]
  refine ⟨57241413501270473270919311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38160942334180315513946207 57241413501270473270919311)
  ·
    refine ⟨85862120251905709906378967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57241413501270473270919311 85862120251905709906378967)
    ·
      refine ⟨128793180377858564859568451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85862120251905709906378967 128793180377858564859568451)
      ·
        refine ⟨193189770566787847289352677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128793180377858564859568451 193189770566787847289352677)
        ·
          refine ⟨36223081981272721366753627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193189770566787847289352677 36223081981272721366753627)
          ·
            refine ⟨54334622971909082050130441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36223081981272721366753627 54334622971909082050130441)
            ·
              refine ⟨40750967228931811537597831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54334622971909082050130441 40750967228931811537597831)
              ·
                refine ⟨61126450843397717306396747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40750967228931811537597831 61126450843397717306396747)
                ·
                  refine ⟨91689676265096575959595121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61126450843397717306396747 91689676265096575959595121)
                  ·
                    refine ⟨68767257198822431969696341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 91689676265096575959595121 68767257198822431969696341)
                    ·
                      refine ⟨805866295298700374644879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 68767257198822431969696341 805866295298700374644879)
                      ·
                        rfl

theorem cell23_1569419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_1569419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569419 prefixEnd_1569419 := by exact prefixLift 1569419
  have htrace : WordTrace (prefixWord ++ tailWord_1569419) baseStart_1569419 baseEnd_1569419 := by
    simpa [prefixWord, tailWord_1569419, baseEnd_1569419] using wordTrace_append hprefix tailTrace_1569419
  have hstable : (prefixWord ++ tailWord_1569419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569419).length < 2 ^ (prefixWord ++ tailWord_1569419).sum := by decide
  have hdescent : baseEnd_1569419 < baseStart_1569419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569456 : List Nat := [2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 3]
def baseStart_1569456 : Nat := 118140960795 + 1569456 * 2 ^ 59
def prefixEnd_1569456 : Nat := 4983230072969 + 3 ^ 40 * 1569456 * 2
def baseEnd_1569456 : Nat := 805885294082916729882209

theorem tailTrace_1569456 : CollatzResearch.WordTrace tailWord_1569456 prefixEnd_1569456 805885294082916729882209 := by
  unfold tailWord_1569456
  simp only [CollatzResearch.WordTrace]
  refine ⟨28621381501068214295008111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38161842001424285726677481 28621381501068214295008111)
  ·
    refine ⟨42932072251602321442512167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28621381501068214295008111 42932072251602321442512167)
    ·
      refine ⟨64398108377403482163768251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42932072251602321442512167 64398108377403482163768251)
      ·
        refine ⟨96597162566105223245652377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64398108377403482163768251 96597162566105223245652377)
        ·
          refine ⟨72447871924578917434239283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96597162566105223245652377 72447871924578917434239283)
          ·
            refine ⟨108671807886868376151358925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72447871924578917434239283 108671807886868376151358925)
            ·
              refine ⟨40751927957575641056759597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108671807886868376151358925 40751927957575641056759597)
              ·
                refine ⟨15281972984090865396284849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40751927957575641056759597 15281972984090865396284849)
                ·
                  refine ⟨11461479738068149047213637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15281972984090865396284849 11461479738068149047213637)
                  ·
                    refine ⟨2149027450887777946352557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11461479738068149047213637 2149027450887777946352557)
                    ·
                      refine ⟨805885294082916729882209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2149027450887777946352557 805885294082916729882209)
                      ·
                        rfl

theorem cell23_1569456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 3, 3, 2, 4, 3].length) (baseStart_1569456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569456 prefixEnd_1569456 := by exact prefixLift 1569456
  have htrace : WordTrace (prefixWord ++ tailWord_1569456) baseStart_1569456 baseEnd_1569456 := by
    simpa [prefixWord, tailWord_1569456, baseEnd_1569456] using wordTrace_append hprefix tailTrace_1569456
  have hstable : (prefixWord ++ tailWord_1569456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569456).length < 2 ^ (prefixWord ++ tailWord_1569456).sum := by decide
  have hdescent : baseEnd_1569456 < baseStart_1569456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569466 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4]
def baseStart_1569466 : Nat := 118140960795 + 1569466 * 2 ^ 59
def prefixEnd_1569466 : Nat := 4983230072969 + 3 ^ 40 * 1569466 * 2
def baseEnd_1569466 : Nat := 805890428889461690757163

theorem tailTrace_1569466 : CollatzResearch.WordTrace tailWord_1569466 prefixEnd_1569466 805890428889461690757163 := by
  unfold tailWord_1569466
  simp only [CollatzResearch.WordTrace]
  refine ⟨14310781933025050074470063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38162085154733466865253501 14310781933025050074470063)
  ·
    refine ⟨21466172899537575111705095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14310781933025050074470063 21466172899537575111705095)
    ·
      refine ⟨32199259349306362667557643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21466172899537575111705095 32199259349306362667557643)
      ·
        refine ⟨48298889023959544001336465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32199259349306362667557643 48298889023959544001336465)
        ·
          refine ⟨36224166767969658001002349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48298889023959544001336465 36224166767969658001002349)
          ·
            refine ⟨13584062537988621750375881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36224166767969658001002349 13584062537988621750375881)
            ·
              refine ⟨10188046903491466312781911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13584062537988621750375881 10188046903491466312781911)
              ·
                refine ⟨15282070355237199469172867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10188046903491466312781911 15282070355237199469172867)
                ·
                  refine ⟨22923105532855799203759301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15282070355237199469172867 22923105532855799203759301)
                  ·
                    refine ⟨4298082287410462350704869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22923105532855799203759301 4298082287410462350704869)
                    ·
                      refine ⟨805890428889461690757163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4298082287410462350704869 805890428889461690757163)
                      ·
                        rfl

theorem cell23_1569466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 4, 4].length) (baseStart_1569466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569466 prefixEnd_1569466 := by exact prefixLift 1569466
  have htrace : WordTrace (prefixWord ++ tailWord_1569466) baseStart_1569466 baseEnd_1569466 := by
    simpa [prefixWord, tailWord_1569466, baseEnd_1569466] using wordTrace_append hprefix tailTrace_1569466
  have hstable : (prefixWord ++ tailWord_1569466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569466).length < 2 ^ (prefixWord ++ tailWord_1569466).sum := by decide
  have hdescent : baseEnd_1569466 < baseStart_1569466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569470 : List Nat := [4, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_1569470 : Nat := 118140960795 + 1569470 * 2 ^ 59
def prefixEnd_1569470 : Nat := 4983230072969 + 3 ^ 40 * 1569470 * 2
def baseEnd_1569470 : Nat := 805892482812079675107145

theorem tailTrace_1569470 : CollatzResearch.WordTrace tailWord_1569470 prefixEnd_1569470 805892482812079675107145 := by
  unfold tailWord_1569470
  simp only [CollatzResearch.WordTrace]
  refine ⟨7155409203010713622628233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38162182416057139320683909 7155409203010713622628233)
  ·
    refine ⟨5366556902258035216971175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7155409203010713622628233 5366556902258035216971175)
    ·
      refine ⟨8049835353387052825456763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5366556902258035216971175 8049835353387052825456763)
      ·
        refine ⟨12074753030080579238185145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8049835353387052825456763 12074753030080579238185145)
        ·
          refine ⟨9056064772560434428638859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12074753030080579238185145 9056064772560434428638859)
          ·
            refine ⟨13584097158840651642958289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9056064772560434428638859 13584097158840651642958289)
            ·
              refine ⟨10188072869130488732218717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13584097158840651642958289 10188072869130488732218717)
              ·
                refine ⟨3820527325923933274582019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10188072869130488732218717 3820527325923933274582019)
                ·
                  refine ⟨5730790988885899911873029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3820527325923933274582019 5730790988885899911873029)
                  ·
                    refine ⟨1074523310416106233476193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5730790988885899911873029 1074523310416106233476193)
                    ·
                      refine ⟨805892482812079675107145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074523310416106233476193 805892482812079675107145)
                      ·
                        rfl

theorem cell23_1569470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_1569470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569470 prefixEnd_1569470 := by exact prefixLift 1569470
  have htrace : WordTrace (prefixWord ++ tailWord_1569470) baseStart_1569470 baseEnd_1569470 := by
    simpa [prefixWord, tailWord_1569470, baseEnd_1569470] using wordTrace_append hprefix tailTrace_1569470
  have hstable : (prefixWord ++ tailWord_1569470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569470).length < 2 ^ (prefixWord ++ tailWord_1569470).sum := by decide
  have hdescent : baseEnd_1569470 < baseStart_1569470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569513 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 2, 5, 2]
def baseStart_1569513 : Nat := 118140960795 + 1569513 * 2 ^ 59
def prefixEnd_1569513 : Nat := 4983230072969 + 3 ^ 40 * 1569513 * 2
def baseEnd_1569513 : Nat := 805914562480223006869447

theorem tailTrace_1569513 : CollatzResearch.WordTrace tailWord_1569513 prefixEnd_1569513 805914562480223006869447 := by
  unfold tailWord_1569513
  simp only [CollatzResearch.WordTrace]
  refine ⟨57244841962929927324841193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38163227975286618216560795 57244841962929927324841193)
  ·
    refine ⟨42933631472197445493630895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57244841962929927324841193 42933631472197445493630895)
    ·
      refine ⟨64400447208296168240446343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42933631472197445493630895 64400447208296168240446343)
      ·
        refine ⟨96600670812444252360669515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64400447208296168240446343 96600670812444252360669515)
        ·
          refine ⟨144901006218666378541004273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96600670812444252360669515 144901006218666378541004273)
          ·
            refine ⟨108675754663999783905753205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 144901006218666378541004273 108675754663999783905753205)
            ·
              refine ⟨10188351999749979741164363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108675754663999783905753205 10188351999749979741164363)
              ·
                refine ⟨15282527999624969611746545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10188351999749979741164363 15282527999624969611746545)
                ·
                  refine ⟨11461895999718727208809909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15282527999624969611746545 11461895999718727208809909)
                  ·
                    refine ⟨1074552749973630675825929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11461895999718727208809909 1074552749973630675825929)
                    ·
                      refine ⟨805914562480223006869447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074552749973630675825929 805914562480223006869447)
                      ·
                        rfl

theorem cell23_1569513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 5, 2].length) (baseStart_1569513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569513 prefixEnd_1569513 := by exact prefixLift 1569513
  have htrace : WordTrace (prefixWord ++ tailWord_1569513) baseStart_1569513 baseEnd_1569513 := by
    simpa [prefixWord, tailWord_1569513, baseEnd_1569513] using wordTrace_append hprefix tailTrace_1569513
  have hstable : (prefixWord ++ tailWord_1569513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569513).length < 2 ^ (prefixWord ++ tailWord_1569513).sum := by decide
  have hdescent : baseEnd_1569513 < baseStart_1569513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569570 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 3, 4]
def baseStart_1569570 : Nat := 118140960795 + 1569570 * 2 ^ 59
def prefixEnd_1569570 : Nat := 4983230072969 + 3 ^ 40 * 1569570 * 2
def baseEnd_1569570 : Nat := 268647943625843094618895

theorem tailTrace_1569570 : CollatzResearch.WordTrace tailWord_1569570 prefixEnd_1569570 268647943625843094618895 := by
  unfold tailWord_1569570
  simp only [CollatzResearch.WordTrace]
  refine ⟨14311730230930856514916541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38164613949148950706444109 14311730230930856514916541)
  ·
    refine ⟨5366898836599071193093703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14311730230930856514916541 5366898836599071193093703)
    ·
      refine ⟨8050348254898606789640555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5366898836599071193093703 8050348254898606789640555)
      ·
        refine ⟨12075522382347910184460833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8050348254898606789640555 12075522382347910184460833)
        ·
          refine ⟨9056641786760932638345625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12075522382347910184460833 9056641786760932638345625)
          ·
            refine ⟨6792481340070699478759219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9056641786760932638345625 6792481340070699478759219)
            ·
              refine ⟨10188722010106049218138829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792481340070699478759219 10188722010106049218138829)
              ·
                refine ⟨3820770753789768456802061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10188722010106049218138829 3820770753789768456802061)
                ·
                  refine ⟨1432789032671163171300773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3820770753789768456802061 1432789032671163171300773)
                  ·
                    refine ⟨268647943625843094618895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1432789032671163171300773 268647943625843094618895)
                    ·
                      rfl

theorem cell23_1569570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_1569570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569570 prefixEnd_1569570 := by exact prefixLift 1569570
  have htrace : WordTrace (prefixWord ++ tailWord_1569570) baseStart_1569570 baseEnd_1569570 := by
    simpa [prefixWord, tailWord_1569570, baseEnd_1569570] using wordTrace_append hprefix tailTrace_1569570
  have hstable : (prefixWord ++ tailWord_1569570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569570).length < 2 ^ (prefixWord ++ tailWord_1569570).sum := by decide
  have hdescent : baseEnd_1569570 < baseStart_1569570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569634 : List Nat := [3, 3, 2, 1, 3, 2, 2, 1, 6]
def baseStart_1569634 : Nat := 118140960795 + 1569634 * 2 ^ 59
def prefixEnd_1569634 : Nat := 4983230072969 + 3 ^ 40 * 1569634 * 2
def baseEnd_1569634 : Nat := 89552965959935225939599

theorem tailTrace_1569634 : CollatzResearch.WordTrace tailWord_1569634 prefixEnd_1569634 89552965959935225939599 := by
  unfold tailWord_1569634
  simp only [CollatzResearch.WordTrace]
  refine ⟨14312313798872891247498989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38166170130327709993330637 14312313798872891247498989)
  ·
    refine ⟨5367117674577334217812121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14312313798872891247498989 5367117674577334217812121)
    ·
      refine ⟨4025338255933000663359091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5367117674577334217812121 4025338255933000663359091)
      ·
        refine ⟨6038007383899500995038637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025338255933000663359091 6038007383899500995038637)
        ·
          refine ⟨2264252768962312873139489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6038007383899500995038637 2264252768962312873139489)
          ·
            refine ⟨1698189576721734654854617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2264252768962312873139489 1698189576721734654854617)
            ·
              refine ⟨1273642182541300991140963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1698189576721734654854617 1273642182541300991140963)
              ·
                refine ⟨1910463273811951486711445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273642182541300991140963 1910463273811951486711445)
                ·
                  refine ⟨89552965959935225939599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1910463273811951486711445 89552965959935225939599)
                  ·
                    rfl

theorem cell23_1569634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 1, 6].length) (baseStart_1569634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569634 prefixEnd_1569634 := by exact prefixLift 1569634
  have htrace : WordTrace (prefixWord ++ tailWord_1569634) baseStart_1569634 baseEnd_1569634 := by
    simpa [prefixWord, tailWord_1569634, baseEnd_1569634] using wordTrace_append hprefix tailTrace_1569634
  have hstable : (prefixWord ++ tailWord_1569634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569634).length < 2 ^ (prefixWord ++ tailWord_1569634).sum := by decide
  have hdescent : baseEnd_1569634 < baseStart_1569634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569650 : List Nat := [3, 2, 1, 2, 1, 1, 2, 1, 2, 6, 2]
def baseStart_1569650 : Nat := 118140960795 + 1569650 * 2 ^ 59
def prefixEnd_1569650 : Nat := 4983230072969 + 3 ^ 40 * 1569650 * 2
def baseEnd_1569650 : Nat := 805984909329888970856317

theorem tailTrace_1569650 : CollatzResearch.WordTrace tailWord_1569650 prefixEnd_1569650 805984909329888970856317 := by
  unfold tailWord_1569650
  simp only [CollatzResearch.WordTrace]
  refine ⟨14312459690858399930644601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38166559175622399815052269 14312459690858399930644601)
  ·
    refine ⟨10734344768143799947983451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14312459690858399930644601 10734344768143799947983451)
    ·
      refine ⟨16101517152215699921975177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10734344768143799947983451 16101517152215699921975177)
      ·
        refine ⟨12076137864161774941481383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16101517152215699921975177 12076137864161774941481383)
        ·
          refine ⟨18114206796242662412222075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12076137864161774941481383 18114206796242662412222075)
          ·
            refine ⟨27171310194363993618333113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18114206796242662412222075 27171310194363993618333113)
            ·
              refine ⟨20378482645772995213749835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27171310194363993618333113 20378482645772995213749835)
              ·
                refine ⟨30567723968659492820624753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20378482645772995213749835 30567723968659492820624753)
                ·
                  refine ⟨22925792976494619615468565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30567723968659492820624753 22925792976494619615468565)
                  ·
                    refine ⟨1074646545773185294475089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22925792976494619615468565 1074646545773185294475089)
                    ·
                      refine ⟨805984909329888970856317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074646545773185294475089 805984909329888970856317)
                      ·
                        rfl

theorem cell23_1569650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_1569650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569650 prefixEnd_1569650 := by exact prefixLift 1569650
  have htrace : WordTrace (prefixWord ++ tailWord_1569650) baseStart_1569650 baseEnd_1569650 := by
    simpa [prefixWord, tailWord_1569650, baseEnd_1569650] using wordTrace_append hprefix tailTrace_1569650
  have hstable : (prefixWord ++ tailWord_1569650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569650).length < 2 ^ (prefixWord ++ tailWord_1569650).sum := by decide
  have hdescent : baseEnd_1569650 < baseStart_1569650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569654 : List Nat := [5, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2]
def baseStart_1569654 : Nat := 118140960795 + 1569654 * 2 ^ 59
def prefixEnd_1569654 : Nat := 4983230072969 + 3 ^ 40 * 1569654 * 2
def baseEnd_1569654 : Nat := 805986963252506955206299

theorem tailTrace_1569654 : CollatzResearch.WordTrace tailWord_1569654 prefixEnd_1569654 805986963252506955206299 := by
  unfold tailWord_1569654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578124040963694275357751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38166656436946072270482677 3578124040963694275357751)
  ·
    refine ⟨5367186061445541413036627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3578124040963694275357751 5367186061445541413036627)
    ·
      refine ⟨8050779092168312119554941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5367186061445541413036627 8050779092168312119554941)
      ·
        refine ⟨3019042159563117044833103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8050779092168312119554941 3019042159563117044833103)
        ·
          refine ⟨4528563239344675567249655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019042159563117044833103 4528563239344675567249655)
          ·
            refine ⟨6792844859017013350874483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4528563239344675567249655 6792844859017013350874483)
            ·
              refine ⟨10189267288525520026311725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6792844859017013350874483 10189267288525520026311725)
              ·
                refine ⟨3820975233197070009866897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10189267288525520026311725 3820975233197070009866897)
                ·
                  refine ⟨2865731424897802507400173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3820975233197070009866897 2865731424897802507400173)
                  ·
                    refine ⟨1074649284336675940275065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2865731424897802507400173 1074649284336675940275065)
                    ·
                      refine ⟨805986963252506955206299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074649284336675940275065 805986963252506955206299)
                      ·
                        rfl

theorem cell23_1569654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_1569654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569654 prefixEnd_1569654 := by exact prefixLift 1569654
  have htrace : WordTrace (prefixWord ++ tailWord_1569654) baseStart_1569654 baseEnd_1569654 := by
    simpa [prefixWord, tailWord_1569654, baseEnd_1569654] using wordTrace_append hprefix tailTrace_1569654
  have hstable : (prefixWord ++ tailWord_1569654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569654).length < 2 ^ (prefixWord ++ tailWord_1569654).sum := by decide
  have hdescent : baseEnd_1569654 < baseStart_1569654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569663 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 4]
def baseStart_1569663 : Nat := 118140960795 + 1569663 * 2 ^ 59
def prefixEnd_1569663 : Nat := 4983230072969 + 3 ^ 40 * 1569663 * 2
def baseEnd_1569663 : Nat := 805991584578397419993757

theorem tailTrace_1569663 : CollatzResearch.WordTrace tailWord_1569663 prefixEnd_1569663 805991584578397419993757 := by
  unfold tailWord_1569663
  simp only [CollatzResearch.WordTrace]
  refine ⟨57250312912386502942801643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38166875274924335295201095 57250312912386502942801643)
  ·
    refine ⟨85875469368579754414202465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57250312912386502942801643 85875469368579754414202465)
    ·
      refine ⟨64406602026434815810651849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85875469368579754414202465 64406602026434815810651849)
      ·
        refine ⟨48304951519826111857988887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64406602026434815810651849 48304951519826111857988887)
        ·
          refine ⟨72457427279739167786983331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48304951519826111857988887 72457427279739167786983331)
          ·
            refine ⟨108686140919608751680474997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72457427279739167786983331 108686140919608751680474997)
            ·
              refine ⟨10189325711213320470044531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 108686140919608751680474997 10189325711213320470044531)
              ·
                refine ⟨15283988566819980705066797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10189325711213320470044531 15283988566819980705066797)
                ·
                  refine ⟨5731495712557492764400049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15283988566819980705066797 5731495712557492764400049)
                  ·
                    refine ⟨4298621784418119573300037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5731495712557492764400049 4298621784418119573300037)
                    ·
                      refine ⟨805991584578397419993757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4298621784418119573300037 805991584578397419993757)
                      ·
                        rfl

theorem cell23_1569663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_1569663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569663 prefixEnd_1569663 := by exact prefixLift 1569663
  have htrace : WordTrace (prefixWord ++ tailWord_1569663) baseStart_1569663 baseEnd_1569663 := by
    simpa [prefixWord, tailWord_1569663, baseEnd_1569663] using wordTrace_append hprefix tailTrace_1569663
  have hstable : (prefixWord ++ tailWord_1569663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569663).length < 2 ^ (prefixWord ++ tailWord_1569663).sum := by decide
  have hdescent : baseEnd_1569663 < baseStart_1569663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569667 : List Nat := [1, 1, 1, 3, 4, 1, 5, 1, 1, 1, 4]
def baseStart_1569667 : Nat := 118140960795 + 1569667 * 2 ^ 59
def prefixEnd_1569667 : Nat := 4983230072969 + 3 ^ 40 * 1569667 * 2
def baseEnd_1569667 : Nat := 805993638501015404343739

theorem tailTrace_1569667 : CollatzResearch.WordTrace tailWord_1569667 prefixEnd_1569667 805993638501015404343739 := by
  unfold tailWord_1569667
  simp only [CollatzResearch.WordTrace]
  refine ⟨57250458804372011625947255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38166972536248007750631503 57250458804372011625947255)
  ·
    refine ⟨85875688206558017438920883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57250458804372011625947255 85875688206558017438920883)
    ·
      refine ⟨128813532309837026158381325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85875688206558017438920883 128813532309837026158381325)
      ·
        refine ⟨48305074616188884809392997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128813532309837026158381325 48305074616188884809392997)
        ·
          refine ⟨9057201490535415901761187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48305074616188884809392997 9057201490535415901761187)
          ·
            refine ⟨13585802235803123852641781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9057201490535415901761187 13585802235803123852641781)
            ·
              refine ⟨1273668959606542861185167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13585802235803123852641781 1273668959606542861185167)
              ·
                refine ⟨1910503439409814291777751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273668959606542861185167 1910503439409814291777751)
                ·
                  refine ⟨2865755159114721437666627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910503439409814291777751 2865755159114721437666627)
                  ·
                    refine ⟨4298632738672082156499941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2865755159114721437666627 4298632738672082156499941)
                    ·
                      refine ⟨805993638501015404343739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4298632738672082156499941 805993638501015404343739)
                      ·
                        rfl

theorem cell23_1569667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 1, 1, 4].length) (baseStart_1569667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569667 prefixEnd_1569667 := by exact prefixLift 1569667
  have htrace : WordTrace (prefixWord ++ tailWord_1569667) baseStart_1569667 baseEnd_1569667 := by
    simpa [prefixWord, tailWord_1569667, baseEnd_1569667] using wordTrace_append hprefix tailTrace_1569667
  have hstable : (prefixWord ++ tailWord_1569667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569667).length < 2 ^ (prefixWord ++ tailWord_1569667).sum := by decide
  have hdescent : baseEnd_1569667 < baseStart_1569667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569684 : List Nat := [2, 4, 2, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_1569684 : Nat := 118140960795 + 1569684 * 2 ^ 59
def prefixEnd_1569684 : Nat := 4983230072969 + 3 ^ 40 * 1569684 * 2
def baseEnd_1569684 : Nat := 806002367672141837831161

theorem tailTrace_1569684 : CollatzResearch.WordTrace tailWord_1569684 prefixEnd_1569684 806002367672141837831161 := by
  unfold tailWord_1569684
  simp only [CollatzResearch.WordTrace]
  refine ⟨28625539422655211764658053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38167385896873615686210737 28625539422655211764658053)
  ·
    refine ⟨5367288641747852205873385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28625539422655211764658053 5367288641747852205873385)
    ·
      refine ⟨4025466481310889154405039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5367288641747852205873385 4025466481310889154405039)
      ·
        refine ⟨6038199721966333731607559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025466481310889154405039 6038199721966333731607559)
        ·
          refine ⟨9057299582949500597411339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6038199721966333731607559 9057299582949500597411339)
          ·
            refine ⟨13585949374424250896117009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9057299582949500597411339 13585949374424250896117009)
            ·
              refine ⟨10189462030818188172087757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13585949374424250896117009 10189462030818188172087757)
              ·
                refine ⟨3821048261556820564532909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10189462030818188172087757 3821048261556820564532909)
                ·
                  refine ⟨1432893098083807711699841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3821048261556820564532909 1432893098083807711699841)
                  ·
                    refine ⟨1074669823562855783774881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1432893098083807711699841 1074669823562855783774881)
                    ·
                      refine ⟨806002367672141837831161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074669823562855783774881 806002367672141837831161)
                      ·
                        rfl

theorem cell23_1569684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_1569684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569684 prefixEnd_1569684 := by exact prefixLift 1569684
  have htrace : WordTrace (prefixWord ++ tailWord_1569684) baseStart_1569684 baseEnd_1569684 := by
    simpa [prefixWord, tailWord_1569684, baseEnd_1569684] using wordTrace_append hprefix tailTrace_1569684
  have hstable : (prefixWord ++ tailWord_1569684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569684).length < 2 ^ (prefixWord ++ tailWord_1569684).sum := by decide
  have hdescent : baseEnd_1569684 < baseStart_1569684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569697 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1569697 : Nat := 118140960795 + 1569697 * 2 ^ 59
def prefixEnd_1569697 : Nat := 4983230072969 + 3 ^ 40 * 1569697 * 2
def baseEnd_1569697 : Nat := 806009042920650286968601

theorem tailTrace_1569697 : CollatzResearch.WordTrace tailWord_1569697 prefixEnd_1569697 806009042920650286968601 := by
  unfold tailWord_1569697
  simp only [CollatzResearch.WordTrace]
  refine ⟨57251552994263326749539345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38167701996175551166359563 57251552994263326749539345)
  ·
    refine ⟨42938664745697495062154509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57251552994263326749539345 42938664745697495062154509)
    ·
      refine ⟨16101999279636560648307941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42938664745697495062154509 16101999279636560648307941)
      ·
        refine ⟨3019124864931855121557739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16101999279636560648307941 3019124864931855121557739)
        ·
          refine ⟨4528687297397782682336609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019124864931855121557739 4528687297397782682336609)
          ·
            refine ⟨3396515473048337011752457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4528687297397782682336609 3396515473048337011752457)
            ·
              refine ⟨2547386604786252758814343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3396515473048337011752457 2547386604786252758814343)
              ·
                refine ⟨3821079907179379138221515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547386604786252758814343 3821079907179379138221515)
                ·
                  refine ⟨5731619860769068707332273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3821079907179379138221515 5731619860769068707332273)
                  ·
                    refine ⟨4298714895576801530499205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5731619860769068707332273 4298714895576801530499205)
                    ·
                      refine ⟨806009042920650286968601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4298714895576801530499205 806009042920650286968601)
                      ·
                        rfl

theorem cell23_1569697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1569697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569697 prefixEnd_1569697 := by exact prefixLift 1569697
  have htrace : WordTrace (prefixWord ++ tailWord_1569697) baseStart_1569697 baseEnd_1569697 := by
    simpa [prefixWord, tailWord_1569697, baseEnd_1569697] using wordTrace_append hprefix tailTrace_1569697
  have hstable : (prefixWord ++ tailWord_1569697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569697).length < 2 ^ (prefixWord ++ tailWord_1569697).sum := by decide
  have hdescent : baseEnd_1569697 < baseStart_1569697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569717 : List Nat := [1, 3, 3, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_1569717 : Nat := 118140960795 + 1569717 * 2 ^ 59
def prefixEnd_1569717 : Nat := 4983230072969 + 3 ^ 40 * 1569717 * 2
def baseEnd_1569717 : Nat := 806019312533740208718509

theorem tailTrace_1569717 : CollatzResearch.WordTrace tailWord_1569717 prefixEnd_1569717 806019312533740208718509 := by
  unfold tailWord_1569717
  simp only [CollatzResearch.WordTrace]
  refine ⟨57252282454190870165267405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38168188302793913443511603 57252282454190870165267405)
  ·
    refine ⟨21469605920321576311975277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57252282454190870165267405 21469605920321576311975277)
    ·
      refine ⟨8051102220120591116990729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21469605920321576311975277 8051102220120591116990729)
      ·
        refine ⟨6038326665090443337743047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8051102220120591116990729 6038326665090443337743047)
        ·
          refine ⟨9057489997635665006614571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6038326665090443337743047 9057489997635665006614571)
          ·
            refine ⟨13586234996453497509921857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9057489997635665006614571 13586234996453497509921857)
            ·
              refine ⟨10189676247340123132441393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13586234996453497509921857 10189676247340123132441393)
              ·
                refine ⟨7642257185505092349331045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10189676247340123132441393 7642257185505092349331045)
                ·
                  refine ⟨1432923222282204815499571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7642257185505092349331045 1432923222282204815499571)
                  ·
                    refine ⟨2149384833423307223249357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1432923222282204815499571 2149384833423307223249357)
                    ·
                      refine ⟨806019312533740208718509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2149384833423307223249357 806019312533740208718509)
                      ·
                        rfl

theorem cell23_1569717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_1569717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569717 prefixEnd_1569717 := by exact prefixLift 1569717
  have htrace : WordTrace (prefixWord ++ tailWord_1569717) baseStart_1569717 baseEnd_1569717 := by
    simpa [prefixWord, tailWord_1569717, baseEnd_1569717] using wordTrace_append hprefix tailTrace_1569717
  have hstable : (prefixWord ++ tailWord_1569717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569717).length < 2 ^ (prefixWord ++ tailWord_1569717).sum := by decide
  have hdescent : baseEnd_1569717 < baseStart_1569717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569718 : List Nat := [5, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1569718 : Nat := 118140960795 + 1569718 * 2 ^ 59
def prefixEnd_1569718 : Nat := 4983230072969 + 3 ^ 40 * 1569718 * 2
def baseEnd_1569718 : Nat := 806019826014394704806005

theorem tailTrace_1569718 : CollatzResearch.WordTrace tailWord_1569718 prefixEnd_1569718 806019826014394704806005 := by
  unfold tailWord_1569718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578269932949202958503363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38168212618124831557369205 3578269932949202958503363)
  ·
    refine ⟨5367404899423804437755045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3578269932949202958503363 5367404899423804437755045)
    ·
      refine ⟨1006388418641963332079071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5367404899423804437755045 1006388418641963332079071)
      ·
        refine ⟨1509582627962944998118607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006388418641963332079071 1509582627962944998118607)
        ·
          refine ⟨2264373941944417497177911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509582627962944998118607 2264373941944417497177911)
          ·
            refine ⟨3396560912916626245766867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2264373941944417497177911 3396560912916626245766867)
            ·
              refine ⟨5094841369374939368650301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3396560912916626245766867 5094841369374939368650301)
              ·
                refine ⟨1910565513515602263243863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5094841369374939368650301 1910565513515602263243863)
                ·
                  refine ⟨2865848270273403394865795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910565513515602263243863 2865848270273403394865795)
                  ·
                    refine ⟨4298772405410105092298693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2865848270273403394865795 4298772405410105092298693)
                    ·
                      refine ⟨806019826014394704806005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4298772405410105092298693 806019826014394704806005)
                      ·
                        rfl

theorem cell23_1569718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1569718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569718 prefixEnd_1569718 := by exact prefixLift 1569718
  have htrace : WordTrace (prefixWord ++ tailWord_1569718) baseStart_1569718 baseEnd_1569718 := by
    simpa [prefixWord, tailWord_1569718, baseEnd_1569718] using wordTrace_append hprefix tailTrace_1569718
  have hstable : (prefixWord ++ tailWord_1569718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569718).length < 2 ^ (prefixWord ++ tailWord_1569718).sum := by decide
  have hdescent : baseEnd_1569718 < baseStart_1569718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569783 : List Nat := [1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 6]
def baseStart_1569783 : Nat := 118140960795 + 1569783 * 2 ^ 59
def prefixEnd_1569783 : Nat := 4983230072969 + 3 ^ 40 * 1569783 * 2
def baseEnd_1569783 : Nat := 806053202256936950493205

theorem tailTrace_1569783 : CollatzResearch.WordTrace tailWord_1569783 prefixEnd_1569783 806053202256936950493205 := by
  unfold tailWord_1569783
  simp only [CollatzResearch.WordTrace]
  refine ⟨57254689671951763437170003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38169793114634508958113335 57254689671951763437170003)
  ·
    refine ⟨85882034507927645155755005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57254689671951763437170003 85882034507927645155755005)
    ·
      refine ⟨32205762940472866933408127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85882034507927645155755005 32205762940472866933408127)
      ·
        refine ⟨48308644410709300400112191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32205762940472866933408127 48308644410709300400112191)
        ·
          refine ⟨72462966616063950600168287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48308644410709300400112191 72462966616063950600168287)
          ·
            refine ⟨108694449924095925900252431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72462966616063950600168287 108694449924095925900252431)
            ·
              refine ⟨163041674886143888850378647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108694449924095925900252431 163041674886143888850378647)
              ·
                refine ⟨244562512329215833275567971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163041674886143888850378647 244562512329215833275567971)
                ·
                  refine ⟨366843768493823749913351957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 244562512329215833275567971 366843768493823749913351957)
                  ·
                    refine ⟨17195801648147988277188373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 366843768493823749913351957 17195801648147988277188373)
                    ·
                      refine ⟨806053202256936950493205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17195801648147988277188373 806053202256936950493205)
                      ·
                        rfl

theorem cell23_1569783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_1569783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569783 prefixEnd_1569783 := by exact prefixLift 1569783
  have htrace : WordTrace (prefixWord ++ tailWord_1569783) baseStart_1569783 baseEnd_1569783 := by
    simpa [prefixWord, tailWord_1569783, baseEnd_1569783] using wordTrace_append hprefix tailTrace_1569783
  have hstable : (prefixWord ++ tailWord_1569783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569783).length < 2 ^ (prefixWord ++ tailWord_1569783).sum := by decide
  have hdescent : baseEnd_1569783 < baseStart_1569783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569827 : List Nat := [1, 1, 1, 4, 3, 3, 2, 1, 2, 5]
def baseStart_1569827 : Nat := 118140960795 + 1569827 * 2 ^ 59
def prefixEnd_1569827 : Nat := 4983230072969 + 3 ^ 40 * 1569827 * 2
def baseEnd_1569827 : Nat := 268691931801911592781001

theorem tailTrace_1569827 : CollatzResearch.WordTrace tailWord_1569827 prefixEnd_1569827 268691931801911592781001 := by
  unfold tailWord_1569827
  simp only [CollatzResearch.WordTrace]
  refine ⟨57256294483792358951771735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38170862989194905967847823 57256294483792358951771735)
  ·
    refine ⟨85884441725688538427657603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57256294483792358951771735 85884441725688538427657603)
    ·
      refine ⟨128826662588532807641486405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85884441725688538427657603 128826662588532807641486405)
      ·
        refine ⟨24154999235349901432778701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128826662588532807641486405 24154999235349901432778701)
        ·
          refine ⟨9058124713256213037292013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24154999235349901432778701 9058124713256213037292013)
          ·
            refine ⟨3396796767471079888984505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9058124713256213037292013 3396796767471079888984505)
            ·
              refine ⟨2547597575603309916738379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3396796767471079888984505 2547597575603309916738379)
              ·
                refine ⟨3821396363404964875107569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547597575603309916738379 3821396363404964875107569)
                ·
                  refine ⟨2866047272553723656330677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3821396363404964875107569 2866047272553723656330677)
                  ·
                    refine ⟨268691931801911592781001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2866047272553723656330677 268691931801911592781001)
                    ·
                      rfl

theorem cell23_1569827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 5].length) (baseStart_1569827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569827 prefixEnd_1569827 := by exact prefixLift 1569827
  have htrace : WordTrace (prefixWord ++ tailWord_1569827) baseStart_1569827 baseEnd_1569827 := by
    simpa [prefixWord, tailWord_1569827, baseEnd_1569827] using wordTrace_append hprefix tailTrace_1569827
  have hstable : (prefixWord ++ tailWord_1569827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569827).length < 2 ^ (prefixWord ++ tailWord_1569827).sum := by decide
  have hdescent : baseEnd_1569827 < baseStart_1569827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569844 : List Nat := [2, 5, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1569844 : Nat := 118140960795 + 1569844 * 2 ^ 59
def prefixEnd_1569844 : Nat := 4983230072969 + 3 ^ 40 * 1569844 * 2
def baseEnd_1569844 : Nat := 268694841525620403943475

theorem tailTrace_1569844 : CollatzResearch.WordTrace tailWord_1569844 prefixEnd_1569844 268694841525620403943475 := by
  unfold tailWord_1569844
  simp only [CollatzResearch.WordTrace]
  refine ⟨28628457262365385427570293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38171276349820513903427057 28628457262365385427570293)
  ·
    refine ⟨2683917868346754883834715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 28628457262365385427570293 2683917868346754883834715)
    ·
      refine ⟨4025876802520132325752073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2683917868346754883834715 4025876802520132325752073)
      ·
        refine ⟨3019407601890099244314055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4025876802520132325752073 3019407601890099244314055)
        ·
          refine ⟨4529111402835148866471083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019407601890099244314055 4529111402835148866471083)
          ·
            refine ⟨6793667104252723299706625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529111402835148866471083 6793667104252723299706625)
            ·
              refine ⟨5095250328189542474779969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6793667104252723299706625 5095250328189542474779969)
              ·
                refine ⟨3821437746142156856084977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5095250328189542474779969 3821437746142156856084977)
                ·
                  refine ⟨2866078309606617642063733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3821437746142156856084977 2866078309606617642063733)
                  ·
                    refine ⟨268694841525620403943475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2866078309606617642063733 268694841525620403943475)
                    ·
                      rfl

theorem cell23_1569844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1569844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569844 prefixEnd_1569844 := by exact prefixLift 1569844
  have htrace : WordTrace (prefixWord ++ tailWord_1569844) baseStart_1569844 baseEnd_1569844 := by
    simpa [prefixWord, tailWord_1569844, baseEnd_1569844] using wordTrace_append hprefix tailTrace_1569844
  have hstable : (prefixWord ++ tailWord_1569844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569844).length < 2 ^ (prefixWord ++ tailWord_1569844).sum := by decide
  have hdescent : baseEnd_1569844 < baseStart_1569844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569847 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 2, 4, 2]
def baseStart_1569847 : Nat := 118140960795 + 1569847 * 2 ^ 59
def prefixEnd_1569847 : Nat := 4983230072969 + 3 ^ 40 * 1569847 * 2
def baseEnd_1569847 : Nat := 806086065018824700092911

theorem tailTrace_1569847 : CollatzResearch.WordTrace tailWord_1569847 prefixEnd_1569847 806086065018824700092911 := by
  unfold tailWord_1569847
  simp only [CollatzResearch.WordTrace]
  refine ⟨57257023943719902367499795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38171349295813268244999863 57257023943719902367499795)
  ·
    refine ⟨85885535915579853551249693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57257023943719902367499795 85885535915579853551249693)
    ·
      refine ⟨32207075968342445081718635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 85885535915579853551249693 32207075968342445081718635)
      ·
        refine ⟨48310613952513667622577953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32207075968342445081718635 48310613952513667622577953)
        ·
          refine ⟨36232960464385250716933465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48310613952513667622577953 36232960464385250716933465)
          ·
            refine ⟨27174720348288938037700099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36232960464385250716933465 27174720348288938037700099)
            ·
              refine ⟨40762080522433407056550149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27174720348288938037700099 40762080522433407056550149)
              ·
                refine ⟨7642890097956263823103153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40762080522433407056550149 7642890097956263823103153)
                ·
                  refine ⟨5732167573467197867327365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7642890097956263823103153 5732167573467197867327365)
                  ·
                    refine ⟨1074781420025099600123881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5732167573467197867327365 1074781420025099600123881)
                    ·
                      refine ⟨806086065018824700092911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074781420025099600123881 806086065018824700092911)
                      ·
                        rfl

theorem cell23_1569847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 4, 2].length) (baseStart_1569847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569847 prefixEnd_1569847 := by exact prefixLift 1569847
  have htrace : WordTrace (prefixWord ++ tailWord_1569847) baseStart_1569847 baseEnd_1569847 := by
    simpa [prefixWord, tailWord_1569847, baseEnd_1569847] using wordTrace_append hprefix tailTrace_1569847
  have hstable : (prefixWord ++ tailWord_1569847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569847).length < 2 ^ (prefixWord ++ tailWord_1569847).sum := by decide
  have hdescent : baseEnd_1569847 < baseStart_1569847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569874 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 3, 4]
def baseStart_1569874 : Nat := 118140960795 + 1569874 * 2 ^ 59
def prefixEnd_1569874 : Nat := 4983230072969 + 3 ^ 40 * 1569874 * 2
def baseEnd_1569874 : Nat := 268699976332165364818429

theorem tailTrace_1569874 : CollatzResearch.WordTrace tailWord_1569874 prefixEnd_1569874 268699976332165364818429 := by
  unfold tailWord_1569874
  simp only [CollatzResearch.WordTrace]
  refine ⟨14314502178655521494683169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38172005809748057319155117 14314502178655521494683169)
  ·
    refine ⟨10735876633991641121012377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14314502178655521494683169 10735876633991641121012377)
    ·
      refine ⟨8051907475493730840759283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10735876633991641121012377 8051907475493730840759283)
      ·
        refine ⟨12077861213240596261138925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8051907475493730840759283 12077861213240596261138925)
        ·
          refine ⟨4529197954965223597927097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12077861213240596261138925 4529197954965223597927097)
          ·
            refine ⟨3396898466223917698445323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4529197954965223597927097 3396898466223917698445323)
            ·
              refine ⟨5095347699335876547667985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3396898466223917698445323 5095347699335876547667985)
              ·
                refine ⟨3821510774501907410750989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5095347699335876547667985 3821510774501907410750989)
                ·
                  refine ⟨1433066540438215279031621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3821510774501907410750989 1433066540438215279031621)
                  ·
                    refine ⟨268699976332165364818429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1433066540438215279031621 268699976332165364818429)
                    ·
                      rfl

theorem cell23_1569874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_1569874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569874 prefixEnd_1569874 := by exact prefixLift 1569874
  have htrace : WordTrace (prefixWord ++ tailWord_1569874) baseStart_1569874 baseEnd_1569874 := by
    simpa [prefixWord, tailWord_1569874, baseEnd_1569874] using wordTrace_append hprefix tailTrace_1569874
  have hstable : (prefixWord ++ tailWord_1569874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569874).length < 2 ^ (prefixWord ++ tailWord_1569874).sum := by decide
  have hdescent : baseEnd_1569874 < baseStart_1569874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569878 : List Nat := [5, 2, 2, 1, 2, 2, 1, 1, 2, 5]
def baseStart_1569878 : Nat := 118140960795 + 1569878 * 2 ^ 59
def prefixEnd_1569878 : Nat := 4983230072969 + 3 ^ 40 * 1569878 * 2
def baseEnd_1569878 : Nat := 268700660973038026268423

theorem tailTrace_1569878 : CollatzResearch.WordTrace tailWord_1569878 prefixEnd_1569878 268700660973038026268423 := by
  unfold tailWord_1569878
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578634662912974666367393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38172103071071729774585525 3578634662912974666367393)
  ·
    refine ⟨2683975997184730999775545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3578634662912974666367393 2683975997184730999775545)
    ·
      refine ⟨2012981997888548249831659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2683975997184730999775545 2012981997888548249831659)
      ·
        refine ⟨3019472996832822374747489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2012981997888548249831659 3019472996832822374747489)
        ·
          refine ⟨2264604747624616781060617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3019472996832822374747489 2264604747624616781060617)
          ·
            refine ⟨1698453560718462585795463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2264604747624616781060617 1698453560718462585795463)
            ·
              refine ⟨2547680341077693878693195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1698453560718462585795463 2547680341077693878693195)
              ·
                refine ⟨3821520511616540818039793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547680341077693878693195 3821520511616540818039793)
                ·
                  refine ⟨2866140383712405613529845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3821520511616540818039793 2866140383712405613529845)
                  ·
                    refine ⟨268700660973038026268423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2866140383712405613529845 268700660973038026268423)
                    ·
                      rfl

theorem cell23_1569878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_1569878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569878 prefixEnd_1569878 := by exact prefixLift 1569878
  have htrace : WordTrace (prefixWord ++ tailWord_1569878) baseStart_1569878 baseEnd_1569878 := by
    simpa [prefixWord, tailWord_1569878, baseEnd_1569878] using wordTrace_append hprefix tailTrace_1569878
  have hstable : (prefixWord ++ tailWord_1569878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569878).length < 2 ^ (prefixWord ++ tailWord_1569878).sum := by decide
  have hdescent : baseEnd_1569878 < baseStart_1569878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569924 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 1, 5, 2]
def baseStart_1569924 : Nat := 118140960795 + 1569924 * 2 ^ 59
def prefixEnd_1569924 : Nat := 4983230072969 + 3 ^ 40 * 1569924 * 2
def baseEnd_1569924 : Nat := 806125603029220898830057

theorem tailTrace_1569924 : CollatzResearch.WordTrace tailWord_1569924 prefixEnd_1569924 806125603029220898830057 := by
  unfold tailWord_1569924
  simp only [CollatzResearch.WordTrace]
  refine ⟨28629916182220472259026413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38173221576293963012035217 28629916182220472259026413)
  ·
    refine ⟨10736218568332677097134905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28629916182220472259026413 10736218568332677097134905)
    ·
      refine ⟨8052163926249507822851179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10736218568332677097134905 8052163926249507822851179)
      ·
        refine ⟨12078245889374261734276769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8052163926249507822851179 12078245889374261734276769)
        ·
          refine ⟨9058684417030696300707577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12078245889374261734276769 9058684417030696300707577)
          ·
            refine ⟨6794013312773022225530683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9058684417030696300707577 6794013312773022225530683)
            ·
              refine ⟨10191019969159533338296025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794013312773022225530683 10191019969159533338296025)
              ·
                refine ⟨7643264976869650003722019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10191019969159533338296025 7643264976869650003722019)
                ·
                  refine ⟨11464897465304475005583029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7643264976869650003722019 11464897465304475005583029)
                  ·
                    refine ⟨1074834137372294531773409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11464897465304475005583029 1074834137372294531773409)
                    ·
                      refine ⟨806125603029220898830057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074834137372294531773409 806125603029220898830057)
                      ·
                        rfl

theorem cell23_1569924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_1569924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569924 prefixEnd_1569924 := by exact prefixLift 1569924
  have htrace : WordTrace (prefixWord ++ tailWord_1569924) baseStart_1569924 baseEnd_1569924 := by
    simpa [prefixWord, tailWord_1569924, baseEnd_1569924] using wordTrace_append hprefix tailTrace_1569924
  have hstable : (prefixWord ++ tailWord_1569924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569924).length < 2 ^ (prefixWord ++ tailWord_1569924).sum := by decide
  have hdescent : baseEnd_1569924 < baseStart_1569924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569934 : List Nat := [4, 1, 1, 3, 2, 1, 1, 4, 1, 5]
def baseStart_1569934 : Nat := 118140960795 + 1569934 * 2 ^ 59
def prefixEnd_1569934 : Nat := 4983230072969 + 3 ^ 40 * 1569934 * 2
def baseEnd_1569934 : Nat := 268710245945255286568337

theorem tailTrace_1569934 : CollatzResearch.WordTrace tailWord_1569934 prefixEnd_1569934 268710245945255286568337 := by
  unfold tailWord_1569934
  simp only [CollatzResearch.WordTrace]
  refine ⟨7157524636800589528239607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38173464729603144150611237 7157524636800589528239607)
  ·
    refine ⟨10736286955200884292359411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7157524636800589528239607 10736286955200884292359411)
    ·
      refine ⟨16104430432801326438539117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10736286955200884292359411 16104430432801326438539117)
      ·
        refine ⟨6039161412300497414452169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16104430432801326438539117 6039161412300497414452169)
        ·
          refine ⟨4529371059225373060839127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6039161412300497414452169 4529371059225373060839127)
          ·
            refine ⟨6794056588838059591258691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529371059225373060839127 6794056588838059591258691)
            ·
              refine ⟨10191084883257089386888037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794056588838059591258691 10191084883257089386888037)
              ·
                refine ⟨1910828415610704260041507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10191084883257089386888037 1910828415610704260041507)
                ·
                  refine ⟨2866242623416056390062261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910828415610704260041507 2866242623416056390062261)
                  ·
                    refine ⟨268710245945255286568337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2866242623416056390062261 268710245945255286568337)
                    ·
                      rfl

theorem cell23_1569934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 4, 1, 5].length) (baseStart_1569934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569934 prefixEnd_1569934 := by exact prefixLift 1569934
  have htrace : WordTrace (prefixWord ++ tailWord_1569934) baseStart_1569934 baseEnd_1569934 := by
    simpa [prefixWord, tailWord_1569934, baseEnd_1569934] using wordTrace_append hprefix tailTrace_1569934
  have hstable : (prefixWord ++ tailWord_1569934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569934).length < 2 ^ (prefixWord ++ tailWord_1569934).sum := by decide
  have hdescent : baseEnd_1569934 < baseStart_1569934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569948 : List Nat := [2, 2, 3, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_1569948 : Nat := 118140960795 + 1569948 * 2 ^ 59
def prefixEnd_1569948 : Nat := 4983230072969 + 3 ^ 40 * 1569948 * 2
def baseEnd_1569948 : Nat := 806137926564928804929947

theorem tailTrace_1569948 : CollatzResearch.WordTrace tailWord_1569948 prefixEnd_1569948 806137926564928804929947 := by
  unfold tailWord_1569948
  simp only [CollatzResearch.WordTrace]
  refine ⟨28630353858176998308463249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38173805144235997744617665 28630353858176998308463249)
  ·
    refine ⟨21472765393632748731347437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28630353858176998308463249 21472765393632748731347437)
    ·
      refine ⟨8052287022612280774255289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21472765393632748731347437 8052287022612280774255289)
      ·
        refine ⟨6039215266959210580691467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8052287022612280774255289 6039215266959210580691467)
        ·
          refine ⟨9058822900438815871037201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6039215266959210580691467 9058822900438815871037201)
          ·
            refine ⟨6794117175329111903277901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9058822900438815871037201 6794117175329111903277901)
            ·
              refine ⟨2547793940748416963729213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6794117175329111903277901 2547793940748416963729213)
              ·
                refine ⟨955422727780656361398455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2547793940748416963729213 955422727780656361398455)
                ·
                  refine ⟨1433134091670984542097683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955422727780656361398455 1433134091670984542097683)
                  ·
                    refine ⟨2149701137506476813146525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1433134091670984542097683 2149701137506476813146525)
                    ·
                      refine ⟨806137926564928804929947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2149701137506476813146525 806137926564928804929947)
                      ·
                        rfl

theorem cell23_1569948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_1569948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569948 prefixEnd_1569948 := by exact prefixLift 1569948
  have htrace : WordTrace (prefixWord ++ tailWord_1569948) baseStart_1569948 baseEnd_1569948 := by
    simpa [prefixWord, tailWord_1569948, baseEnd_1569948] using wordTrace_append hprefix tailTrace_1569948
  have hstable : (prefixWord ++ tailWord_1569948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569948).length < 2 ^ (prefixWord ++ tailWord_1569948).sum := by decide
  have hdescent : baseEnd_1569948 < baseStart_1569948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569957 : List Nat := [1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_1569957 : Nat := 118140960795 + 1569957 * 2 ^ 59
def prefixEnd_1569957 : Nat := 4983230072969 + 3 ^ 40 * 1569957 * 2
def baseEnd_1569957 : Nat := 806142547890819269717405

theorem tailTrace_1569957 : CollatzResearch.WordTrace tailWord_1569957 prefixEnd_1569957 806142547890819269717405 := by
  unfold tailWord_1569957
  simp only [CollatzResearch.WordTrace]
  refine ⟨57261035973321391154004125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38174023982214260769336083 57261035973321391154004125)
  ·
    refine ⟨21472888489995521682751547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57261035973321391154004125 21472888489995521682751547)
    ·
      refine ⟨32209332734993282524127321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21472888489995521682751547 32209332734993282524127321)
      ·
        refine ⟨24156999551244961893095491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32209332734993282524127321 24156999551244961893095491)
        ·
          refine ⟨36235499326867442839643237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24156999551244961893095491 36235499326867442839643237)
          ·
            refine ⟨6794156123787645532433107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36235499326867442839643237 6794156123787645532433107)
            ·
              refine ⟨10191234185681468298649661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794156123787645532433107 10191234185681468298649661)
              ·
                refine ⟨3821712819630550611993623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10191234185681468298649661 3821712819630550611993623)
                ·
                  refine ⟨5732569229445825917990435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3821712819630550611993623 5732569229445825917990435)
                  ·
                    refine ⟨8598853844168738876985653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5732569229445825917990435 8598853844168738876985653)
                    ·
                      refine ⟨806142547890819269717405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8598853844168738876985653 806142547890819269717405)
                      ·
                        rfl

theorem cell23_1569957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_1569957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569957 prefixEnd_1569957 := by exact prefixLift 1569957
  have htrace : WordTrace (prefixWord ++ tailWord_1569957) baseStart_1569957 baseEnd_1569957 := by
    simpa [prefixWord, tailWord_1569957, baseEnd_1569957] using wordTrace_append hprefix tailTrace_1569957
  have hstable : (prefixWord ++ tailWord_1569957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569957).length < 2 ^ (prefixWord ++ tailWord_1569957).sum := by decide
  have hdescent : baseEnd_1569957 < baseStart_1569957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569965 : List Nat := [1, 5, 2, 1, 4, 1, 1, 1, 3, 1, 3]
def baseStart_1569965 : Nat := 118140960795 + 1569965 * 2 ^ 59
def prefixEnd_1569965 : Nat := 4983230072969 + 3 ^ 40 * 1569965 * 2
def baseEnd_1569965 : Nat := 806146655736055238417369

theorem tailTrace_1569965 : CollatzResearch.WordTrace tailWord_1569965 prefixEnd_1569965 806146655736055238417369 := by
  unfold tailWord_1569965
  simp only [CollatzResearch.WordTrace]
  refine ⟨57261327757292408520295349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38174218504861605680196899 57261327757292408520295349)
  ·
    refine ⟨5368249477246163298777689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57261327757292408520295349 5368249477246163298777689)
    ·
      refine ⟨4026187107934622474083267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5368249477246163298777689 4026187107934622474083267)
      ·
        refine ⟨6039280661901933711124901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4026187107934622474083267 6039280661901933711124901)
        ·
          refine ⟨1132365124106612570835919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6039280661901933711124901 1132365124106612570835919)
          ·
            refine ⟨1698547686159918856253879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132365124106612570835919 1698547686159918856253879)
            ·
              refine ⟨2547821529239878284380819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1698547686159918856253879 2547821529239878284380819)
              ·
                refine ⟨3821732293859817426571229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547821529239878284380819 3821732293859817426571229)
                ·
                  refine ⟨1433149610197431534964211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3821732293859817426571229 1433149610197431534964211)
                  ·
                    refine ⟨2149724415296147302446317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1433149610197431534964211 2149724415296147302446317)
                    ·
                      refine ⟨806146655736055238417369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2149724415296147302446317 806146655736055238417369)
                      ·
                        rfl

theorem cell23_1569965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 1, 1, 3, 1, 3].length) (baseStart_1569965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569965 prefixEnd_1569965 := by exact prefixLift 1569965
  have htrace : WordTrace (prefixWord ++ tailWord_1569965) baseStart_1569965 baseEnd_1569965 := by
    simpa [prefixWord, tailWord_1569965, baseEnd_1569965] using wordTrace_append hprefix tailTrace_1569965
  have hstable : (prefixWord ++ tailWord_1569965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569965).length < 2 ^ (prefixWord ++ tailWord_1569965).sum := by decide
  have hdescent : baseEnd_1569965 < baseStart_1569965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569971 : List Nat := [1, 1, 1, 2, 3, 2, 5, 1, 3, 2, 2]
def baseStart_1569971 : Nat := 118140960795 + 1569971 * 2 ^ 59
def prefixEnd_1569971 : Nat := 4983230072969 + 3 ^ 40 * 1569971 * 2
def baseEnd_1569971 : Nat := 806149736619982214942341

theorem tailTrace_1569971 : CollatzResearch.WordTrace tailWord_1569971 prefixEnd_1569971 806149736619982214942341 := by
  unfold tailWord_1569971
  simp only [CollatzResearch.WordTrace]
  refine ⟨57261546595270671545013767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38174364396847114363342511 57261546595270671545013767)
  ·
    refine ⟨85892319892906007317520651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57261546595270671545013767 85892319892906007317520651)
    ·
      refine ⟨128838479839359010976280977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85892319892906007317520651 128838479839359010976280977)
      ·
        refine ⟨96628859879519258232210733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128838479839359010976280977 96628859879519258232210733)
        ·
          refine ⟨36235822454819721837079025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96628859879519258232210733 36235822454819721837079025)
          ·
            refine ⟨27176866841114791377809269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36235822454819721837079025 27176866841114791377809269)
            ·
              refine ⟨2547831266354511691669619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27176866841114791377809269 2547831266354511691669619)
              ·
                refine ⟨3821746899531767537504429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2547831266354511691669619 3821746899531767537504429)
                ·
                  refine ⟨1433155087324412826564161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3821746899531767537504429 1433155087324412826564161)
                  ·
                    refine ⟨1074866315493309619923121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1433155087324412826564161 1074866315493309619923121)
                    ·
                      refine ⟨806149736619982214942341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1074866315493309619923121 806149736619982214942341)
                      ·
                        rfl

theorem cell23_1569971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 2, 2].length) (baseStart_1569971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569971 prefixEnd_1569971 := by exact prefixLift 1569971
  have htrace : WordTrace (prefixWord ++ tailWord_1569971) baseStart_1569971 baseEnd_1569971 := by
    simpa [prefixWord, tailWord_1569971, baseEnd_1569971] using wordTrace_append hprefix tailTrace_1569971
  have hstable : (prefixWord ++ tailWord_1569971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569971).length < 2 ^ (prefixWord ++ tailWord_1569971).sum := by decide
  have hdescent : baseEnd_1569971 < baseStart_1569971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569977 : List Nat := [1, 2, 1, 4, 1, 4, 2, 8]
def baseStart_1569977 : Nat := 118140960795 + 1569977 * 2 ^ 59
def prefixEnd_1569977 : Nat := 4983230072969 + 3 ^ 40 * 1569977 * 2
def baseEnd_1569977 : Nat := 29857511759404044128419

theorem tailTrace_1569977 : CollatzResearch.WordTrace tailWord_1569977 prefixEnd_1569977 29857511759404044128419 := by
  unfold tailWord_1569977
  simp only [CollatzResearch.WordTrace]
  refine ⟨57261765433248934569732185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38174510288832623046488123 57261765433248934569732185)
  ·
    refine ⟨42946324074936700927299139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57261765433248934569732185 42946324074936700927299139)
    ·
      refine ⟨64419486112405051390948709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42946324074936700927299139 64419486112405051390948709)
      ·
        refine ⟨12078653646075947135802883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64419486112405051390948709 12078653646075947135802883)
        ·
          refine ⟨18117980469113920703704325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12078653646075947135802883 18117980469113920703704325)
          ·
            refine ⟨3397121337958860131944561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18117980469113920703704325 3397121337958860131944561)
            ·
              refine ⟨2547841003469145098958421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3397121337958860131944561 2547841003469145098958421)
              ·
                refine ⟨29857511759404044128419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2547841003469145098958421 29857511759404044128419)
                ·
                  rfl

theorem cell23_1569977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 8].length) (baseStart_1569977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569977 prefixEnd_1569977 := by exact prefixLift 1569977
  have htrace : WordTrace (prefixWord ++ tailWord_1569977) baseStart_1569977 baseEnd_1569977 := by
    simpa [prefixWord, tailWord_1569977, baseEnd_1569977] using wordTrace_append hprefix tailTrace_1569977
  have hstable : (prefixWord ++ tailWord_1569977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569977).length < 2 ^ (prefixWord ++ tailWord_1569977).sum := by decide
  have hdescent : baseEnd_1569977 < baseStart_1569977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569981 : List Nat := [1, 4, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_1569981 : Nat := 118140960795 + 1569981 * 2 ^ 59
def prefixEnd_1569981 : Nat := 4983230072969 + 3 ^ 40 * 1569981 * 2
def baseEnd_1569981 : Nat := 268718290475509058605765

theorem tailTrace_1569981 : CollatzResearch.WordTrace tailWord_1569981 prefixEnd_1569981 268718290475509058605765 := by
  unfold tailWord_1569981
  simp only [CollatzResearch.WordTrace]
  refine ⟨57261911325234443252877797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38174607550156295501918531 57261911325234443252877797)
  ·
    refine ⟨10736608373481458109914587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57261911325234443252877797 10736608373481458109914587)
    ·
      refine ⟨16104912560222187164871881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10736608373481458109914587 16104912560222187164871881)
      ·
        refine ⟨12078684420166640373653911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16104912560222187164871881 12078684420166640373653911)
        ·
          refine ⟨18118026630249960560480867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12078684420166640373653911 18118026630249960560480867)
          ·
            refine ⟨27177039945374940840721301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18118026630249960560480867 27177039945374940840721301)
            ·
              refine ⟨1273923747439450351908811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27177039945374940840721301 1273923747439450351908811)
              ·
                refine ⟨1910885621159175527863217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273923747439450351908811 1910885621159175527863217)
                ·
                  refine ⟨1433164215869381645897413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1910885621159175527863217 1433164215869381645897413)
                  ·
                    refine ⟨268718290475509058605765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1433164215869381645897413 268718290475509058605765)
                    ·
                      rfl

theorem cell23_1569981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_1569981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569981 prefixEnd_1569981 := by exact prefixLift 1569981
  have htrace : WordTrace (prefixWord ++ tailWord_1569981) baseStart_1569981 baseEnd_1569981 := by
    simpa [prefixWord, tailWord_1569981, baseEnd_1569981] using wordTrace_append hprefix tailTrace_1569981
  have hstable : (prefixWord ++ tailWord_1569981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569981).length < 2 ^ (prefixWord ++ tailWord_1569981).sum := by decide
  have hdescent : baseEnd_1569981 < baseStart_1569981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1569988 : List Nat := [2, 3, 3, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_1569988 : Nat := 118140960795 + 1569988 * 2 ^ 59
def prefixEnd_1569988 : Nat := 4983230072969 + 3 ^ 40 * 1569988 * 2
def baseEnd_1569988 : Nat := 806158465791108648429763

theorem tailTrace_1569988 : CollatzResearch.WordTrace tailWord_1569988 prefixEnd_1569988 806158465791108648429763 := by
  unfold tailWord_1569988
  simp only [CollatzResearch.WordTrace]
  refine ⟨28631083318104541724191309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38174777757472722298921745 28631083318104541724191309)
  ·
    refine ⟨10736656244289203146571741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28631083318104541724191309 10736656244289203146571741)
    ·
      refine ⟨4026246091608451179964403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10736656244289203146571741 4026246091608451179964403)
      ·
        refine ⟨6039369137412676769946605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4026246091608451179964403 6039369137412676769946605)
        ·
          refine ⟨2264763426529753788729977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6039369137412676769946605 2264763426529753788729977)
          ·
            refine ⟨1698572569897315341547483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2264763426529753788729977 1698572569897315341547483)
            ·
              refine ⟨2547858854845973012321225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1698572569897315341547483 2547858854845973012321225)
              ·
                refine ⟨1910894141134479759240919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2547858854845973012321225 1910894141134479759240919)
                ·
                  refine ⟨2866341211701719638861379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910894141134479759240919 2866341211701719638861379)
                  ·
                    refine ⟨4299511817552579458292069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2866341211701719638861379 4299511817552579458292069)
                    ·
                      refine ⟨806158465791108648429763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4299511817552579458292069 806158465791108648429763)
                      ·
                        rfl

theorem cell23_1569988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_1569988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1569988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1569988 prefixEnd_1569988 := by exact prefixLift 1569988
  have htrace : WordTrace (prefixWord ++ tailWord_1569988) baseStart_1569988 baseEnd_1569988 := by
    simpa [prefixWord, tailWord_1569988, baseEnd_1569988] using wordTrace_append hprefix tailTrace_1569988
  have hstable : (prefixWord ++ tailWord_1569988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1569988).length < 2 ^ (prefixWord ++ tailWord_1569988).sum := by decide
  have hdescent : baseEnd_1569988 < baseStart_1569988 := by decide
  rcases family_descends (prefixWord ++ tailWord_1569988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570008 : List Nat := [2, 1, 2, 2, 5, 1, 3, 1, 1, 2, 3]
def baseStart_1570008 : Nat := 118140960795 + 1570008 * 2 ^ 59
def prefixEnd_1570008 : Nat := 4983230072969 + 3 ^ 40 * 1570008 * 2
def baseEnd_1570008 : Nat := 806168735404198570179671

theorem tailTrace_1570008 : CollatzResearch.WordTrace tailWord_1570008 prefixEnd_1570008 806168735404198570179671 := by
  unfold tailWord_1570008
  simp only [CollatzResearch.WordTrace]
  refine ⟨28631448048068313432055339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38175264064091084576073785 28631448048068313432055339)
  ·
    refine ⟨42947172072102470148083009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28631448048068313432055339 42947172072102470148083009)
    ·
      refine ⟨32210379054076852611062257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42947172072102470148083009 32210379054076852611062257)
      ·
        refine ⟨24157784290557639458296693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32210379054076852611062257 24157784290557639458296693)
        ·
          refine ⟨2264792277239778699215315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24157784290557639458296693 2264792277239778699215315)
          ·
            refine ⟨3397188415859668048822973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2264792277239778699215315 3397188415859668048822973)
            ·
              refine ⟨1273945655947375518308615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3397188415859668048822973 1273945655947375518308615)
              ·
                refine ⟨1910918483921063277462923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273945655947375518308615 1910918483921063277462923)
                ·
                  refine ⟨2866377725881594916194385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1910918483921063277462923 2866377725881594916194385)
                  ·
                    refine ⟨2149783294411196187145789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2866377725881594916194385 2149783294411196187145789)
                    ·
                      refine ⟨806168735404198570179671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2149783294411196187145789 806168735404198570179671)
                      ·
                        rfl

theorem cell23_1570008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 3, 1, 1, 2, 3].length) (baseStart_1570008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570008 prefixEnd_1570008 := by exact prefixLift 1570008
  have htrace : WordTrace (prefixWord ++ tailWord_1570008) baseStart_1570008 baseEnd_1570008 := by
    simpa [prefixWord, tailWord_1570008, baseEnd_1570008] using wordTrace_append hprefix tailTrace_1570008
  have hstable : (prefixWord ++ tailWord_1570008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570008).length < 2 ^ (prefixWord ++ tailWord_1570008).sum := by decide
  have hdescent : baseEnd_1570008 < baseStart_1570008 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570027 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 4]
def baseStart_1570027 : Nat := 118140960795 + 1570027 * 2 ^ 59
def prefixEnd_1570027 : Nat := 4983230072969 + 3 ^ 40 * 1570027 * 2
def baseEnd_1570027 : Nat := 806178491536633995842083

theorem tailTrace_1570027 : CollatzResearch.WordTrace tailWord_1570027 prefixEnd_1570027 806178491536633995842083 := by
  unfold tailWord_1570027
  simp only [CollatzResearch.WordTrace]
  refine ⟨57263589083067793109052335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38175726055378528739368223 57263589083067793109052335)
  ·
    refine ⟨85895383624601689663578503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57263589083067793109052335 85895383624601689663578503)
    ·
      refine ⟨128843075436902534495367755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85895383624601689663578503 128843075436902534495367755)
      ·
        refine ⟨193264613155353801743051633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128843075436902534495367755 193264613155353801743051633)
        ·
          refine ⟨144948459866515351307288725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193264613155353801743051633 144948459866515351307288725)
          ·
            refine ⟨6794459056242907092529159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 144948459866515351307288725 6794459056242907092529159)
            ·
              refine ⟨10191688584364360638793739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794459056242907092529159 10191688584364360638793739)
              ·
                refine ⟨15287532876546540958190609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10191688584364360638793739 15287532876546540958190609)
                ·
                  refine ⟨11465649657409905718642957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15287532876546540958190609 11465649657409905718642957)
                  ·
                    refine ⟨4299618621528714644491109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11465649657409905718642957 4299618621528714644491109)
                    ·
                      refine ⟨806178491536633995842083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4299618621528714644491109 806178491536633995842083)
                      ·
                        rfl

theorem cell23_1570027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3, 4].length) (baseStart_1570027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570027 prefixEnd_1570027 := by exact prefixLift 1570027
  have htrace : WordTrace (prefixWord ++ tailWord_1570027) baseStart_1570027 baseEnd_1570027 := by
    simpa [prefixWord, tailWord_1570027, baseEnd_1570027] using wordTrace_append hprefix tailTrace_1570027
  have hstable : (prefixWord ++ tailWord_1570027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570027).length < 2 ^ (prefixWord ++ tailWord_1570027).sum := by decide
  have hdescent : baseEnd_1570027 < baseStart_1570027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570057 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 1, 4, 4]
def baseStart_1570057 : Nat := 118140960795 + 1570057 * 2 ^ 59
def prefixEnd_1570057 : Nat := 4983230072969 + 3 ^ 40 * 1570057 * 2
def baseEnd_1570057 : Nat := 806193895956268878466945

theorem tailTrace_1570057 : CollatzResearch.WordTrace tailWord_1570057 prefixEnd_1570057 806193895956268878466945 := by
  unfold tailWord_1570057
  simp only [CollatzResearch.WordTrace]
  refine ⟨57264683272959108232644425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38176455515306072155096283 57264683272959108232644425)
  ·
    refine ⟨42948512454719331174483319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57264683272959108232644425 42948512454719331174483319)
    ·
      refine ⟨64422768682078996761724979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42948512454719331174483319 64422768682078996761724979)
      ·
        refine ⟨96634153023118495142587469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64422768682078996761724979 96634153023118495142587469)
        ·
          refine ⟨36237807383669435678470301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96634153023118495142587469 36237807383669435678470301)
          ·
            refine ⟨13589177768876038379426363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36237807383669435678470301 13589177768876038379426363)
            ·
              refine ⟨20383766653314057569139545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13589177768876038379426363 20383766653314057569139545)
              ·
                refine ⟨15287824989985543176854659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20383766653314057569139545 15287824989985543176854659)
                ·
                  refine ⟨22931737484978314765281989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15287824989985543176854659 22931737484978314765281989)
                  ·
                    refine ⟨4299700778433434018490373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 22931737484978314765281989 4299700778433434018490373)
                    ·
                      refine ⟨806193895956268878466945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4299700778433434018490373 806193895956268878466945)
                      ·
                        rfl

theorem cell23_1570057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_1570057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570057 prefixEnd_1570057 := by exact prefixLift 1570057
  have htrace : WordTrace (prefixWord ++ tailWord_1570057) baseStart_1570057 baseEnd_1570057 := by
    simpa [prefixWord, tailWord_1570057, baseEnd_1570057] using wordTrace_append hprefix tailTrace_1570057
  have hstable : (prefixWord ++ tailWord_1570057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570057).length < 2 ^ (prefixWord ++ tailWord_1570057).sum := by decide
  have hdescent : baseEnd_1570057 < baseStart_1570057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570074 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4]
def baseStart_1570074 : Nat := 118140960795 + 1570074 * 2 ^ 59
def prefixEnd_1570074 : Nat := 4983230072969 + 3 ^ 40 * 1570074 * 2
def baseEnd_1570074 : Nat := 806202625127395311954367

theorem tailTrace_1570074 : CollatzResearch.WordTrace tailWord_1570074 prefixEnd_1570074 806202625127395311954367 := by
  unfold tailWord_1570074
  simp only [CollatzResearch.WordTrace]
  refine ⟨14316325828474380034003319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38176868875931680090675517 14316325828474380034003319)
  ·
    refine ⟨21474488742711570051004979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14316325828474380034003319 21474488742711570051004979)
    ·
      refine ⟨32211733114067355076507469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21474488742711570051004979 32211733114067355076507469)
      ·
        refine ⟨12079399917775258153690301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32211733114067355076507469 12079399917775258153690301)
        ·
          refine ⟨4529774969165721807633863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12079399917775258153690301 4529774969165721807633863)
          ·
            refine ⟨6794662453748582711450795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529774969165721807633863 6794662453748582711450795)
            ·
              refine ⟨10191993680622874067176193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6794662453748582711450795 10191993680622874067176193)
              ·
                refine ⟨7643995260467155550382145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10191993680622874067176193 7643995260467155550382145)
                ·
                  refine ⟨5732996445350366662786609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7643995260467155550382145 5732996445350366662786609)
                  ·
                    refine ⟨4299747334012774997089957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5732996445350366662786609 4299747334012774997089957)
                    ·
                      refine ⟨806202625127395311954367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4299747334012774997089957 806202625127395311954367)
                      ·
                        rfl

theorem cell23_1570074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_1570074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570074 prefixEnd_1570074 := by exact prefixLift 1570074
  have htrace : WordTrace (prefixWord ++ tailWord_1570074) baseStart_1570074 baseEnd_1570074 := by
    simpa [prefixWord, tailWord_1570074, baseEnd_1570074] using wordTrace_append hprefix tailTrace_1570074
  have hstable : (prefixWord ++ tailWord_1570074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570074).length < 2 ^ (prefixWord ++ tailWord_1570074).sum := by decide
  have hdescent : baseEnd_1570074 < baseStart_1570074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570084 : List Nat := [2, 3, 1, 3, 1, 1, 4, 1, 7]
def baseStart_1570084 : Nat := 118140960795 + 1570084 * 2 ^ 59
def prefixEnd_1570084 : Nat := 4983230072969 + 3 ^ 40 * 1570084 * 2
def baseEnd_1570084 : Nat := 89578639992660030314369

theorem tailTrace_1570084 : CollatzResearch.WordTrace tailWord_1570084 prefixEnd_1570084 89578639992660030314369 := by
  unfold tailWord_1570084
  simp only [CollatzResearch.WordTrace]
  refine ⟨28632834021930645921938653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38177112029240861229251537 28632834021930645921938653)
  ·
    refine ⟨10737312758223992220726995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28632834021930645921938653 10737312758223992220726995)
    ·
      refine ⟨16105969137335988331090493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10737312758223992220726995 16105969137335988331090493)
      ·
        refine ⟨6039738426500995624158935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16105969137335988331090493 6039738426500995624158935)
        ·
          refine ⟨9059607639751493436238403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6039738426500995624158935 9059607639751493436238403)
          ·
            refine ⟨13589411459627240154357605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9059607639751493436238403 13589411459627240154357605)
            ·
              refine ⟨2548014648680107528942051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13589411459627240154357605 2548014648680107528942051)
              ·
                refine ⟨3822021973020161293413077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2548014648680107528942051 3822021973020161293413077)
                ·
                  refine ⟨89578639992660030314369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3822021973020161293413077 89578639992660030314369)
                  ·
                    rfl

theorem cell23_1570084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 1, 7].length) (baseStart_1570084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570084 prefixEnd_1570084 := by exact prefixLift 1570084
  have htrace : WordTrace (prefixWord ++ tailWord_1570084) baseStart_1570084 baseEnd_1570084 := by
    simpa [prefixWord, tailWord_1570084, baseEnd_1570084] using wordTrace_append hprefix tailTrace_1570084
  have hstable : (prefixWord ++ tailWord_1570084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570084).length < 2 ^ (prefixWord ++ tailWord_1570084).sum := by decide
  have hdescent : baseEnd_1570084 < baseStart_1570084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570171 : List Nat := [1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 3]
def baseStart_1570171 : Nat := 118140960795 + 1570171 * 2 ^ 59
def prefixEnd_1570171 : Nat := 4983230072969 + 3 ^ 40 * 1570171 * 2
def baseEnd_1570171 : Nat := 806252432750881432441421

theorem tailTrace_1570171 : CollatzResearch.WordTrace tailWord_1570171 prefixEnd_1570171 806252432750881432441421 := by
  unfold tailWord_1570171
  simp only [CollatzResearch.WordTrace]
  refine ⟨57268841194546105702294367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38179227463030737134862911 57268841194546105702294367)
  ·
    refine ⟨85903261791819158553441551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57268841194546105702294367 85903261791819158553441551)
    ·
      refine ⟨128854892687728737830162327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85903261791819158553441551 128854892687728737830162327)
      ·
        refine ⟨193282339031593106745243491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128854892687728737830162327 193282339031593106745243491)
        ·
          refine ⟨289923508547389660117865237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193282339031593106745243491 289923508547389660117865237)
          ·
            refine ⟨13590164463158890318024933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 289923508547389660117865237 13590164463158890318024933)
            ·
              refine ⟨2548155836842291934629675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13590164463158890318024933 2548155836842291934629675)
              ·
                refine ⟨3822233755263437901944513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2548155836842291934629675 3822233755263437901944513)
                ·
                  refine ⟨2866675316447578426458385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3822233755263437901944513 2866675316447578426458385)
                  ·
                    refine ⟨2150006487335683819843789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2866675316447578426458385 2150006487335683819843789)
                    ·
                      refine ⟨806252432750881432441421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2150006487335683819843789 806252432750881432441421)
                      ·
                        rfl

theorem cell23_1570171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 2, 2, 3].length) (baseStart_1570171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570171 prefixEnd_1570171 := by exact prefixLift 1570171
  have htrace : WordTrace (prefixWord ++ tailWord_1570171) baseStart_1570171 baseEnd_1570171 := by
    simpa [prefixWord, tailWord_1570171, baseEnd_1570171] using wordTrace_append hprefix tailTrace_1570171
  have hstable : (prefixWord ++ tailWord_1570171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570171).length < 2 ^ (prefixWord ++ tailWord_1570171).sum := by decide
  have hdescent : baseEnd_1570171 < baseStart_1570171 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570211 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 1, 5, 2]
def baseStart_1570211 : Nat := 118140960795 + 1570211 * 2 ^ 59
def prefixEnd_1570211 : Nat := 4983230072969 + 3 ^ 40 * 1570211 * 2
def baseEnd_1570211 : Nat := 806272971977061275941237

theorem tailTrace_1570211 : CollatzResearch.WordTrace tailWord_1570211 prefixEnd_1570211 806272971977061275941237 := by
  unfold tailWord_1570211
  simp only [CollatzResearch.WordTrace]
  refine ⟨57270300114401192533750487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38180200076267461689166991 57270300114401192533750487)
  ·
    refine ⟨85905450171601788800625731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57270300114401192533750487 85905450171601788800625731)
    ·
      refine ⟨128858175257402683200938597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85905450171601788800625731 128858175257402683200938597)
      ·
        refine ⟨24160907860763003100175987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128858175257402683200938597 24160907860763003100175987)
        ·
          refine ⟨36241361791144504650263981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24160907860763003100175987 36241361791144504650263981)
          ·
            refine ⟨13590510671679189243848993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36241361791144504650263981 13590510671679189243848993)
            ·
              refine ⟨10192883003759391932886745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13590510671679189243848993 10192883003759391932886745)
              ·
                refine ⟨7644662252819543949665059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10192883003759391932886745 7644662252819543949665059)
                ·
                  refine ⟨11466993379229315924497589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7644662252819543949665059 11466993379229315924497589)
                  ·
                    refine ⟨1075030629302748367921649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11466993379229315924497589 1075030629302748367921649)
                    ·
                      refine ⟨806272971977061275941237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1075030629302748367921649 806272971977061275941237)
                      ·
                        rfl

theorem cell23_1570211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 5, 2].length) (baseStart_1570211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570211 prefixEnd_1570211 := by exact prefixLift 1570211
  have htrace : WordTrace (prefixWord ++ tailWord_1570211) baseStart_1570211 baseEnd_1570211 := by
    simpa [prefixWord, tailWord_1570211, baseEnd_1570211] using wordTrace_append hprefix tailTrace_1570211
  have hstable : (prefixWord ++ tailWord_1570211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570211).length < 2 ^ (prefixWord ++ tailWord_1570211).sum := by decide
  have hdescent : baseEnd_1570211 < baseStart_1570211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570242 : List Nat := [3, 5, 2, 1, 1, 1, 1, 1, 8]
def baseStart_1570242 : Nat := 118140960795 + 1570242 * 2 ^ 59
def prefixEnd_1570242 : Nat := 4983230072969 + 3 ^ 40 * 1570242 * 2
def baseEnd_1570242 : Nat := 89587654430816739405955

theorem tailTrace_1570242 : CollatzResearch.WordTrace tailWord_1570242 prefixEnd_1570242 89587654430816739405955 := by
  unfold tailWord_1570242
  simp only [CollatzResearch.WordTrace]
  refine ⟨14317857694322221207032245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38180953851525923218752653 14317857694322221207032245)
  ·
    refine ⟨1342299158842708238159273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14317857694322221207032245 1342299158842708238159273)
    ·
      refine ⟨1006724369132031178619455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1342299158842708238159273 1006724369132031178619455)
      ·
        refine ⟨1510086553698046767929183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006724369132031178619455 1510086553698046767929183)
        ·
          refine ⟨2265129830547070151893775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510086553698046767929183 2265129830547070151893775)
          ·
            refine ⟨3397694745820605227840663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265129830547070151893775 3397694745820605227840663)
            ·
              refine ⟨5096542118730907841760995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397694745820605227840663 5096542118730907841760995)
              ·
                refine ⟨7644813178096361762641493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5096542118730907841760995 7644813178096361762641493)
                ·
                  refine ⟨89587654430816739405955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7644813178096361762641493 89587654430816739405955)
                  ·
                    rfl

theorem cell23_1570242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_1570242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570242 prefixEnd_1570242 := by exact prefixLift 1570242
  have htrace : WordTrace (prefixWord ++ tailWord_1570242) baseStart_1570242 baseEnd_1570242 := by
    simpa [prefixWord, tailWord_1570242, baseEnd_1570242] using wordTrace_append hprefix tailTrace_1570242
  have hstable : (prefixWord ++ tailWord_1570242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570242).length < 2 ^ (prefixWord ++ tailWord_1570242).sum := by decide
  have hdescent : baseEnd_1570242 < baseStart_1570242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570261 : List Nat := [1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1570261 : Nat := 118140960795 + 1570261 * 2 ^ 59
def prefixEnd_1570261 : Nat := 4983230072969 + 3 ^ 40 * 1570261 * 2
def baseEnd_1570261 : Nat := 806298646009786080316007

theorem tailTrace_1570261 : CollatzResearch.WordTrace tailWord_1570261 prefixEnd_1570261 806298646009786080316007 := by
  unfold tailWord_1570261
  simp only [CollatzResearch.WordTrace]
  refine ⟨57272123764220051073070637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38181415842813367382047091 57272123764220051073070637)
  ·
    refine ⟨21477046411582519152401489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57272123764220051073070637 21477046411582519152401489)
    ·
      refine ⟨16107784808686889364301117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21477046411582519152401489 16107784808686889364301117)
      ·
        refine ⟨6040419303257583511612919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16107784808686889364301117 6040419303257583511612919)
        ·
          refine ⟨9060628954886375267419379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6040419303257583511612919 9060628954886375267419379)
          ·
            refine ⟨13590943432329562901129069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9060628954886375267419379 13590943432329562901129069)
            ·
              refine ⟨5096603787123586087923401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13590943432329562901129069 5096603787123586087923401)
              ·
                refine ⟨3822452840342689565942551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5096603787123586087923401 3822452840342689565942551)
                ·
                  refine ⟨5733679260514034348913827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3822452840342689565942551 5733679260514034348913827)
                  ·
                    refine ⟨8600518890771051523370741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5733679260514034348913827 8600518890771051523370741)
                    ·
                      refine ⟨806298646009786080316007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8600518890771051523370741 806298646009786080316007)
                      ·
                        rfl

theorem cell23_1570261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1570261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570261 prefixEnd_1570261 := by exact prefixLift 1570261
  have htrace : WordTrace (prefixWord ++ tailWord_1570261) baseStart_1570261 baseEnd_1570261 := by
    simpa [prefixWord, tailWord_1570261, baseEnd_1570261] using wordTrace_append hprefix tailTrace_1570261
  have hstable : (prefixWord ++ tailWord_1570261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570261).length < 2 ^ (prefixWord ++ tailWord_1570261).sum := by decide
  have hdescent : baseEnd_1570261 < baseStart_1570261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570275 : List Nat := [1, 1, 1, 6, 2, 1, 2, 2, 3, 2, 2]
def baseStart_1570275 : Nat := 118140960795 + 1570275 * 2 ^ 59
def prefixEnd_1570275 : Nat := 4983230072969 + 3 ^ 40 * 1570275 * 2
def baseEnd_1570275 : Nat := 806305834738949025540943

theorem tailTrace_1570275 : CollatzResearch.WordTrace tailWord_1570275 prefixEnd_1570275 806305834738949025540943 := by
  unfold tailWord_1570275
  simp only [CollatzResearch.WordTrace]
  refine ⟨57272634386169331464080279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38181756257446220976053519 57272634386169331464080279)
  ·
    refine ⟨85908951579253997196120419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57272634386169331464080279 85908951579253997196120419)
    ·
      refine ⟨128863427368880995794180629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85908951579253997196120419 128863427368880995794180629)
      ·
        refine ⟨6040473157916296677852217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 128863427368880995794180629 6040473157916296677852217)
        ·
          refine ⟨4530354868437222508389163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6040473157916296677852217 4530354868437222508389163)
          ·
            refine ⟨6795532302655833762583745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4530354868437222508389163 6795532302655833762583745)
            ·
              refine ⟨5096649226991875321937809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6795532302655833762583745 5096649226991875321937809)
              ·
                refine ⟨3822486920243906491453357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5096649226991875321937809 3822486920243906491453357)
                ·
                  refine ⟨1433432595091464934295009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3822486920243906491453357 1433432595091464934295009)
                  ·
                    refine ⟨1075074446318598700721257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1433432595091464934295009 1075074446318598700721257)
                    ·
                      refine ⟨806305834738949025540943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1075074446318598700721257 806305834738949025540943)
                      ·
                        rfl

theorem cell23_1570275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_1570275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570275 prefixEnd_1570275 := by exact prefixLift 1570275
  have htrace : WordTrace (prefixWord ++ tailWord_1570275) baseStart_1570275 baseEnd_1570275 := by
    simpa [prefixWord, tailWord_1570275, baseEnd_1570275] using wordTrace_append hprefix tailTrace_1570275
  have hstable : (prefixWord ++ tailWord_1570275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570275).length < 2 ^ (prefixWord ++ tailWord_1570275).sum := by decide
  have hdescent : baseEnd_1570275 < baseStart_1570275 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570325 : List Nat := [1, 3, 2, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_1570325 : Nat := 118140960795 + 1570325 * 2 ^ 59
def prefixEnd_1570325 : Nat := 4983230072969 + 3 ^ 40 * 1570325 * 2
def baseEnd_1570325 : Nat := 806331508771673829915713

theorem tailTrace_1570325 : CollatzResearch.WordTrace tailWord_1570325 prefixEnd_1570325 806331508771673829915713 := by
  unfold tailWord_1570325
  simp only [CollatzResearch.WordTrace]
  refine ⟨57274458035988190003400429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38182972023992126668933619 57274458035988190003400429)
  ·
    refine ⟨21477921763495571251275161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57274458035988190003400429 21477921763495571251275161)
    ·
      refine ⟨16108441322621678438456371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21477921763495571251275161 16108441322621678438456371)
      ·
        refine ⟨24162661983932517657684557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16108441322621678438456371 24162661983932517657684557)
        ·
          refine ⟨9060998243974694121631709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24162661983932517657684557 9060998243974694121631709)
          ·
            refine ⟨3397874341490510295611891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9060998243974694121631709 3397874341490510295611891)
            ·
              refine ⟨5096811512235765443417837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3397874341490510295611891 5096811512235765443417837)
              ·
                refine ⟨1911304317088412041281689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5096811512235765443417837 1911304317088412041281689)
                ·
                  refine ⟨1433478237816309030961267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1911304317088412041281689 1433478237816309030961267)
                  ·
                    refine ⟨2150217356724463546441901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1433478237816309030961267 2150217356724463546441901)
                    ·
                      refine ⟨806331508771673829915713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2150217356724463546441901 806331508771673829915713)
                      ·
                        rfl

theorem cell23_1570325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_1570325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570325 prefixEnd_1570325 := by exact prefixLift 1570325
  have htrace : WordTrace (prefixWord ++ tailWord_1570325) baseStart_1570325 baseEnd_1570325 := by
    simpa [prefixWord, tailWord_1570325, baseEnd_1570325] using wordTrace_append hprefix tailTrace_1570325
  have hstable : (prefixWord ++ tailWord_1570325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570325).length < 2 ^ (prefixWord ++ tailWord_1570325).sum := by decide
  have hdescent : baseEnd_1570325 < baseStart_1570325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570335 : List Nat := [1, 1, 2, 4, 1, 1, 5, 2, 1, 3, 2]
def baseStart_1570335 : Nat := 118140960795 + 1570335 * 2 ^ 59
def prefixEnd_1570335 : Nat := 4983230072969 + 3 ^ 40 * 1570335 * 2
def baseEnd_1570335 : Nat := 806336643578218790790667

theorem tailTrace_1570335 : CollatzResearch.WordTrace tailWord_1570335 prefixEnd_1570335 806336643578218790790667 := by
  unfold tailWord_1570335
  simp only [CollatzResearch.WordTrace]
  refine ⟨57274822765951961711264459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38183215177301307807509639 57274822765951961711264459)
  ·
    refine ⟨85912234148927942566896689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57274822765951961711264459 85912234148927942566896689)
    ·
      refine ⟨64434175611695956925172517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85912234148927942566896689 64434175611695956925172517)
      ·
        refine ⟨12081407927192991923469847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64434175611695956925172517 12081407927192991923469847)
        ·
          refine ⟨18122111890789487885204771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12081407927192991923469847 18122111890789487885204771)
          ·
            refine ⟨27183167836184231827807157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18122111890789487885204771 27183167836184231827807157)
            ·
              refine ⟨2548421984642271733856921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27183167836184231827807157 2548421984642271733856921)
              ·
                refine ⟨1911316488481703800392691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2548421984642271733856921 1911316488481703800392691)
                ·
                  refine ⟨2866974732722555700589037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911316488481703800392691 2866974732722555700589037)
                  ·
                    refine ⟨1075115524770958387720889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2866974732722555700589037 1075115524770958387720889)
                    ·
                      refine ⟨806336643578218790790667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1075115524770958387720889 806336643578218790790667)
                      ·
                        rfl

theorem cell23_1570335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 3, 2].length) (baseStart_1570335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570335 prefixEnd_1570335 := by exact prefixLift 1570335
  have htrace : WordTrace (prefixWord ++ tailWord_1570335) baseStart_1570335 baseEnd_1570335 := by
    simpa [prefixWord, tailWord_1570335, baseEnd_1570335] using wordTrace_append hprefix tailTrace_1570335
  have hstable : (prefixWord ++ tailWord_1570335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570335).length < 2 ^ (prefixWord ++ tailWord_1570335).sum := by decide
  have hdescent : baseEnd_1570335 < baseStart_1570335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570401 : List Nat := [1, 2, 3, 1, 1, 3, 3, 1, 1, 7]
def baseStart_1570401 : Nat := 118140960795 + 1570401 * 2 ^ 59
def prefixEnd_1570401 : Nat := 4983230072969 + 3 ^ 40 * 1570401 * 2
def baseEnd_1570401 : Nat := 268790177767138510855121

theorem tailTrace_1570401 : CollatzResearch.WordTrace tailWord_1570401 prefixEnd_1570401 268790177767138510855121 := by
  unfold tailWord_1570401
  simp only [CollatzResearch.WordTrace]
  refine ⟨57277229983712854983167057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38184819989141903322111371 57277229983712854983167057)
  ·
    refine ⟨42957922487784641237375293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57277229983712854983167057 42957922487784641237375293)
    ·
      refine ⟨16109220932919240464015735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42957922487784641237375293 16109220932919240464015735)
      ·
        refine ⟨24163831399378860696023603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16109220932919240464015735 24163831399378860696023603)
        ·
          refine ⟨36245747099068291044035405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24163831399378860696023603 36245747099068291044035405)
          ·
            refine ⟨13592155162150609141513277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36245747099068291044035405 13592155162150609141513277)
            ·
              refine ⟨5097058185806478428067479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13592155162150609141513277 5097058185806478428067479)
              ·
                refine ⟨7645587278709717642101219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5097058185806478428067479 7645587278709717642101219)
                ·
                  refine ⟨11468380918064576463151829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7645587278709717642101219 11468380918064576463151829)
                  ·
                    refine ⟨268790177767138510855121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11468380918064576463151829 268790177767138510855121)
                    ·
                      rfl

theorem cell23_1570401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_1570401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570401 prefixEnd_1570401 := by exact prefixLift 1570401
  have htrace : WordTrace (prefixWord ++ tailWord_1570401) baseStart_1570401 baseEnd_1570401 := by
    simpa [prefixWord, tailWord_1570401, baseEnd_1570401] using wordTrace_append hprefix tailTrace_1570401
  have hstable : (prefixWord ++ tailWord_1570401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570401).length < 2 ^ (prefixWord ++ tailWord_1570401).sum := by decide
  have hdescent : baseEnd_1570401 < baseStart_1570401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570405 : List Nat := [1, 3, 1, 3, 3, 2, 2, 3, 5]
def baseStart_1570405 : Nat := 118140960795 + 1570405 * 2 ^ 59
def prefixEnd_1570405 : Nat := 4983230072969 + 3 ^ 40 * 1570405 * 2
def baseEnd_1570405 : Nat := 89596954136003724101705

theorem tailTrace_1570405 : CollatzResearch.WordTrace tailWord_1570405 prefixEnd_1570405 89596954136003724101705 := by
  unfold tailWord_1570405
  simp only [CollatzResearch.WordTrace]
  refine ⟨57277375875698363666312669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38184917250465575777541779 57277375875698363666312669)
  ·
    refine ⟨21479015953386886374867251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57277375875698363666312669 21479015953386886374867251)
    ·
      refine ⟨32218523930080329562300877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21479015953386886374867251 32218523930080329562300877)
      ·
        refine ⟨12081946473780123585862829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32218523930080329562300877 12081946473780123585862829)
        ·
          refine ⟨4530729927667546344698561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12081946473780123585862829 4530729927667546344698561)
          ·
            refine ⟨3398047445750659758523921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4530729927667546344698561 3398047445750659758523921)
            ·
              refine ⟨2548535584312994818892941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3398047445750659758523921 2548535584312994818892941)
              ·
                refine ⟨955700844117373057084853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2548535584312994818892941 955700844117373057084853)
                ·
                  refine ⟨89596954136003724101705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 955700844117373057084853 89596954136003724101705)
                  ·
                    rfl

theorem cell23_1570405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_1570405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570405 prefixEnd_1570405 := by exact prefixLift 1570405
  have htrace : WordTrace (prefixWord ++ tailWord_1570405) baseStart_1570405 baseEnd_1570405 := by
    simpa [prefixWord, tailWord_1570405, baseEnd_1570405] using wordTrace_append hprefix tailTrace_1570405
  have hstable : (prefixWord ++ tailWord_1570405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570405).length < 2 ^ (prefixWord ++ tailWord_1570405).sum := by decide
  have hdescent : baseEnd_1570405 < baseStart_1570405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570501 : List Nat := [1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_1570501 : Nat := 118140960795 + 1570501 * 2 ^ 59
def prefixEnd_1570501 : Nat := 4983230072969 + 3 ^ 40 * 1570501 * 2
def baseEnd_1570501 : Nat := 806421881366865141314903

theorem tailTrace_1570501 : CollatzResearch.WordTrace tailWord_1570501 prefixEnd_1570501 806421881366865141314903 := by
  unfold tailWord_1570501
  simp only [CollatzResearch.WordTrace]
  refine ⟨57280877283350572061807357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38187251522233714707871571 57280877283350572061807357)
  ·
    refine ⟨21480328981256464523177759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57280877283350572061807357 21480328981256464523177759)
    ·
      refine ⟨32220493471884696784766639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21480328981256464523177759 32220493471884696784766639)
      ·
        refine ⟨48330740207827045177149959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32220493471884696784766639 48330740207827045177149959)
        ·
          refine ⟨72496110311740567765724939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48330740207827045177149959 72496110311740567765724939)
          ·
            refine ⟨108744165467610851648587409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72496110311740567765724939 108744165467610851648587409)
            ·
              refine ⟨81558124100708138736440557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 108744165467610851648587409 81558124100708138736440557)
              ·
                refine ⟨30584296537765552026165209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81558124100708138736440557 30584296537765552026165209)
                ·
                  refine ⟨22938222403324164019623907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30584296537765552026165209 22938222403324164019623907)
                  ·
                    refine ⟨34407333604986246029435861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22938222403324164019623907 34407333604986246029435861)
                    ·
                      refine ⟨806421881366865141314903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34407333604986246029435861 806421881366865141314903)
                      ·
                        rfl

theorem cell23_1570501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_1570501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570501 prefixEnd_1570501 := by exact prefixLift 1570501
  have htrace : WordTrace (prefixWord ++ tailWord_1570501) baseStart_1570501 baseEnd_1570501 := by
    simpa [prefixWord, tailWord_1570501, baseEnd_1570501] using wordTrace_append hprefix tailTrace_1570501
  have hstable : (prefixWord ++ tailWord_1570501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570501).length < 2 ^ (prefixWord ++ tailWord_1570501).sum := by decide
  have hdescent : baseEnd_1570501 < baseStart_1570501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570509 : List Nat := [1, 6, 2, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_1570509 : Nat := 118140960795 + 1570509 * 2 ^ 59
def prefixEnd_1570509 : Nat := 4983230072969 + 3 ^ 40 * 1570509 * 2
def baseEnd_1570509 : Nat := 806425989212101110014867

theorem tailTrace_1570509 : CollatzResearch.WordTrace tailWord_1570509 prefixEnd_1570509 806425989212101110014867 := by
  unfold tailWord_1570509
  simp only [CollatzResearch.WordTrace]
  refine ⟨57281169067321589428098581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38187446044881059618732387 57281169067321589428098581)
  ·
    refine ⟨2685054800030699504442121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57281169067321589428098581 2685054800030699504442121)
    ·
      refine ⟨2013791100023024628331591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2685054800030699504442121 2013791100023024628331591)
      ·
        refine ⟨3020686650034536942497387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013791100023024628331591 3020686650034536942497387)
        ·
          refine ⟨4531029975051805413746081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3020686650034536942497387 4531029975051805413746081)
          ·
            refine ⟨3398272481288854060309561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4531029975051805413746081 3398272481288854060309561)
            ·
              refine ⟨2548704360966640545232171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3398272481288854060309561 2548704360966640545232171)
              ·
                refine ⟨3823056541449960817848257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2548704360966640545232171 3823056541449960817848257)
                ·
                  refine ⟨2867292406087470613386193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3823056541449960817848257 2867292406087470613386193)
                  ·
                    refine ⟨2150469304565602960039645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2867292406087470613386193 2150469304565602960039645)
                    ·
                      refine ⟨806425989212101110014867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2150469304565602960039645 806425989212101110014867)
                      ·
                        rfl

theorem cell23_1570509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_1570509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570509 prefixEnd_1570509 := by exact prefixLift 1570509
  have htrace : WordTrace (prefixWord ++ tailWord_1570509) baseStart_1570509 baseEnd_1570509 := by
    simpa [prefixWord, tailWord_1570509, baseEnd_1570509] using wordTrace_append hprefix tailTrace_1570509
  have hstable : (prefixWord ++ tailWord_1570509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570509).length < 2 ^ (prefixWord ++ tailWord_1570509).sum := by decide
  have hdescent : baseEnd_1570509 < baseStart_1570509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570539 : List Nat := [1, 1, 1, 1, 2, 4, 6, 2, 1, 1, 3]
def baseStart_1570539 : Nat := 118140960795 + 1570539 * 2 ^ 59
def prefixEnd_1570539 : Nat := 4983230072969 + 3 ^ 40 * 1570539 * 2
def baseEnd_1570539 : Nat := 806441393631735992639729

theorem tailTrace_1570539 : CollatzResearch.WordTrace tailWord_1570539 prefixEnd_1570539 806441393631735992639729 := by
  unfold tailWord_1570539
  simp only [CollatzResearch.WordTrace]
  refine ⟨57282263257212904551690671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38188175504808603034460447 57282263257212904551690671)
  ·
    refine ⟨85923394885819356827536007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57282263257212904551690671 85923394885819356827536007)
    ·
      refine ⟨128885092328729035241304011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85923394885819356827536007 128885092328729035241304011)
      ·
        refine ⟨193327638493093552861956017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128885092328729035241304011 193327638493093552861956017)
        ·
          refine ⟨144995728869820164646467013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193327638493093552861956017 144995728869820164646467013)
          ·
            refine ⟨27186699163091280871212565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 144995728869820164646467013 27186699163091280871212565)
            ·
              refine ⟨1274376523269903790838089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 27186699163091280871212565 1274376523269903790838089)
              ·
                refine ⟨955782392452427843128567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274376523269903790838089 955782392452427843128567)
                ·
                  refine ⟨1433673588678641764692851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955782392452427843128567 1433673588678641764692851)
                  ·
                    refine ⟨2150510383017962647039277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1433673588678641764692851 2150510383017962647039277)
                    ·
                      refine ⟨806441393631735992639729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2150510383017962647039277 806441393631735992639729)
                      ·
                        rfl

theorem cell23_1570539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 6, 2, 1, 1, 3].length) (baseStart_1570539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570539 prefixEnd_1570539 := by exact prefixLift 1570539
  have htrace : WordTrace (prefixWord ++ tailWord_1570539) baseStart_1570539 baseEnd_1570539 := by
    simpa [prefixWord, tailWord_1570539, baseEnd_1570539] using wordTrace_append hprefix tailTrace_1570539
  have hstable : (prefixWord ++ tailWord_1570539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570539).length < 2 ^ (prefixWord ++ tailWord_1570539).sum := by decide
  have hdescent : baseEnd_1570539 < baseStart_1570539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570562 : List Nat := [3, 4, 1, 1, 1, 1, 2, 4, 1, 1, 4]
def baseStart_1570562 : Nat := 118140960795 + 1570562 * 2 ^ 59
def prefixEnd_1570562 : Nat := 4983230072969 + 3 ^ 40 * 1570562 * 2
def baseEnd_1570562 : Nat := 806453203686789402652123

theorem tailTrace_1570562 : CollatzResearch.WordTrace tailWord_1570562 prefixEnd_1570562 806453203686789402652123 := by
  unfold tailWord_1570562
  simp only [CollatzResearch.WordTrace]
  refine ⟨14320775534032394869944485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38188734757419719653185293 14320775534032394869944485)
  ·
    refine ⟨2685145412631074038114591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14320775534032394869944485 2685145412631074038114591)
    ·
      refine ⟨4027718118946611057171887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2685145412631074038114591 4027718118946611057171887)
      ·
        refine ⟨6041577178419916585757831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4027718118946611057171887 6041577178419916585757831)
        ·
          refine ⟨9062365767629874878636747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6041577178419916585757831 9062365767629874878636747)
          ·
            refine ⟨13593548651444812317955121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9062365767629874878636747 13593548651444812317955121)
            ·
              refine ⟨10195161488583609238466341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13593548651444812317955121 10195161488583609238466341)
              ·
                refine ⟨1911592779109426732212439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10195161488583609238466341 1911592779109426732212439)
                ·
                  refine ⟨2867389168664140098318659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911592779109426732212439 2867389168664140098318659)
                  ·
                    refine ⟨4301083752996210147477989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2867389168664140098318659 4301083752996210147477989)
                    ·
                      refine ⟨806453203686789402652123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4301083752996210147477989 806453203686789402652123)
                      ·
                        rfl

theorem cell23_1570562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_1570562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570562 prefixEnd_1570562 := by exact prefixLift 1570562
  have htrace : WordTrace (prefixWord ++ tailWord_1570562) baseStart_1570562 baseEnd_1570562 := by
    simpa [prefixWord, tailWord_1570562, baseEnd_1570562] using wordTrace_append hprefix tailTrace_1570562
  have hstable : (prefixWord ++ tailWord_1570562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570562).length < 2 ^ (prefixWord ++ tailWord_1570562).sum := by decide
  have hdescent : baseEnd_1570562 < baseStart_1570562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570596 : List Nat := [2, 3, 1, 3, 2, 1, 2, 4, 1, 2, 2]
def baseStart_1570596 : Nat := 118140960795 + 1570596 * 2 ^ 59
def prefixEnd_1570596 : Nat := 4983230072969 + 3 ^ 40 * 1570596 * 2
def baseEnd_1570596 : Nat := 806470662029042269626967

theorem tailTrace_1570596 : CollatzResearch.WordTrace tailWord_1570596 prefixEnd_1570596 806470662029042269626967 := by
  unfold tailWord_1570596
  simp only [CollatzResearch.WordTrace]
  refine ⟨28642171109003201643257821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38189561478670935524343761 28642171109003201643257821)
  ·
    refine ⟨10740814165876200616221683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28642171109003201643257821 10740814165876200616221683)
    ·
      refine ⟨16111221248814300924332525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10740814165876200616221683 16111221248814300924332525)
      ·
        refine ⟨6041707968305362846624697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16111221248814300924332525 6041707968305362846624697)
        ·
          refine ⟨4531280976229022134968523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6041707968305362846624697 4531280976229022134968523)
          ·
            refine ⟨6796921464343533202452785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4531280976229022134968523 6796921464343533202452785)
            ·
              refine ⟨5097691098257649901839589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6796921464343533202452785 5097691098257649901839589)
              ·
                refine ⟨955817080923309356594923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5097691098257649901839589 955817080923309356594923)
                ·
                  refine ⟨1433725621384964034892385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955817080923309356594923 1433725621384964034892385)
                  ·
                    refine ⟨1075294216038723026169289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1433725621384964034892385 1075294216038723026169289)
                    ·
                      refine ⟨806470662029042269626967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1075294216038723026169289 806470662029042269626967)
                      ·
                        rfl

theorem cell23_1570596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_1570596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570596 prefixEnd_1570596 := by exact prefixLift 1570596
  have htrace : WordTrace (prefixWord ++ tailWord_1570596) baseStart_1570596 baseEnd_1570596 := by
    simpa [prefixWord, tailWord_1570596, baseEnd_1570596] using wordTrace_append hprefix tailTrace_1570596
  have hstable : (prefixWord ++ tailWord_1570596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570596).length < 2 ^ (prefixWord ++ tailWord_1570596).sum := by decide
  have hdescent : baseEnd_1570596 < baseStart_1570596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570606 : List Nat := [4, 1, 3, 2, 2, 1, 3, 1, 2, 4]
def baseStart_1570606 : Nat := 118140960795 + 1570606 * 2 ^ 59
def prefixEnd_1570606 : Nat := 4983230072969 + 3 ^ 40 * 1570606 * 2
def baseEnd_1570606 : Nat := 268825265611862410167307

theorem tailTrace_1570606 : CollatzResearch.WordTrace tailWord_1570606 prefixEnd_1570606 268825265611862410167307 := by
  unfold tailWord_1570606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160588368496271874297459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38189804631980116662919781 7160588368496271874297459)
  ·
    refine ⟨10740882552744407811446189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7160588368496271874297459 10740882552744407811446189)
    ·
      refine ⟨4027830957279152929292321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10740882552744407811446189 4027830957279152929292321)
      ·
        refine ⟨3020873217959364696969241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4027830957279152929292321 3020873217959364696969241)
        ·
          refine ⟨2265654913469523522726931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3020873217959364696969241 2265654913469523522726931)
          ·
            refine ⟨3398482370204285284090397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265654913469523522726931 3398482370204285284090397)
            ·
              refine ⟨1274430888826606981533899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3398482370204285284090397 1274430888826606981533899)
              ·
                refine ⟨1911646333239910472300849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274430888826606981533899 1911646333239910472300849)
                ·
                  refine ⟨1433734749929932854225637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1911646333239910472300849 1433734749929932854225637)
                  ·
                    refine ⟨268825265611862410167307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1433734749929932854225637 268825265611862410167307)
                    ·
                      rfl

theorem cell23_1570606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 3, 1, 2, 4].length) (baseStart_1570606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570606 prefixEnd_1570606 := by exact prefixLift 1570606
  have htrace : WordTrace (prefixWord ++ tailWord_1570606) baseStart_1570606 baseEnd_1570606 := by
    simpa [prefixWord, tailWord_1570606, baseEnd_1570606] using wordTrace_append hprefix tailTrace_1570606
  have hstable : (prefixWord ++ tailWord_1570606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570606).length < 2 ^ (prefixWord ++ tailWord_1570606).sum := by decide
  have hdescent : baseEnd_1570606 < baseStart_1570606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570630 : List Nat := [6, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2]
def baseStart_1570630 : Nat := 118140960795 + 1570630 * 2 ^ 59
def prefixEnd_1570630 : Nat := 4983230072969 + 3 ^ 40 * 1570630 * 2
def baseEnd_1570630 : Nat := 806488120371295136601811

theorem tailTrace_1570630 : CollatzResearch.WordTrace tailWord_1570630 prefixEnd_1570630 806488120371295136601811 := by
  unfold tailWord_1570630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1790174446871350846664167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38190388199922151395502229 1790174446871350846664167)
  ·
    refine ⟨2685261670307026269996251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1790174446871350846664167 2685261670307026269996251)
    ·
      refine ⟨4027892505460539404994377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2685261670307026269996251 4027892505460539404994377)
      ·
        refine ⟨3020919379095404553745783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4027892505460539404994377 3020919379095404553745783)
        ·
          refine ⟨4531379068643106830618675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3020919379095404553745783 4531379068643106830618675)
          ·
            refine ⟨6797068602964660245928013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4531379068643106830618675 6797068602964660245928013)
            ·
              refine ⟨2548900726111747592223005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6797068602964660245928013 2548900726111747592223005)
              ·
                refine ⟨955837772291905347083627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2548900726111747592223005 955837772291905347083627)
                ·
                  refine ⟨1433756658437858020625441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955837772291905347083627 1433756658437858020625441)
                  ·
                    refine ⟨1075317493828393515469081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1433756658437858020625441 1075317493828393515469081)
                    ·
                      refine ⟨806488120371295136601811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1075317493828393515469081 806488120371295136601811)
                      ·
                        rfl

theorem cell23_1570630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 3, 3, 1, 2, 2].length) (baseStart_1570630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570630 prefixEnd_1570630 := by exact prefixLift 1570630
  have htrace : WordTrace (prefixWord ++ tailWord_1570630) baseStart_1570630 baseEnd_1570630 := by
    simpa [prefixWord, tailWord_1570630, baseEnd_1570630] using wordTrace_append hprefix tailTrace_1570630
  have hstable : (prefixWord ++ tailWord_1570630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570630).length < 2 ^ (prefixWord ++ tailWord_1570630).sum := by decide
  have hdescent : baseEnd_1570630 < baseStart_1570630 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570685 : List Nat := [1, 4, 1, 1, 2, 1, 1, 2, 4, 3, 3]
def baseStart_1570685 : Nat := 118140960795 + 1570685 * 2 ^ 59
def prefixEnd_1570685 : Nat := 4983230072969 + 3 ^ 40 * 1570685 * 2
def baseEnd_1570685 : Nat := 806516361807292421414057

theorem tailTrace_1570685 : CollatzResearch.WordTrace tailWord_1570685 prefixEnd_1570685 806516361807292421414057 := by
  unfold tailWord_1570685
  simp only [CollatzResearch.WordTrace]
  refine ⟨57287588314683971486505509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38191725543122647657670339 57287588314683971486505509)
  ·
    refine ⟨10741422809003244653719783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57287588314683971486505509 10741422809003244653719783)
    ·
      refine ⟨16112134213504866980579675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10741422809003244653719783 16112134213504866980579675)
      ·
        refine ⟨24168201320257300470869513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16112134213504866980579675 24168201320257300470869513)
        ·
          refine ⟨18126150990192975353152135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24168201320257300470869513 18126150990192975353152135)
          ·
            refine ⟨27189226485289463029728203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18126150990192975353152135 27189226485289463029728203)
            ·
              refine ⟨40783839727934194544592305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27189226485289463029728203 40783839727934194544592305)
              ·
                refine ⟨30587879795950645908444229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40783839727934194544592305 30587879795950645908444229)
                ·
                  refine ⟨5735227461740746107833293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30587879795950645908444229 5735227461740746107833293)
                  ·
                    refine ⟨2150710298152779790437485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5735227461740746107833293 2150710298152779790437485)
                    ·
                      refine ⟨806516361807292421414057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2150710298152779790437485 806516361807292421414057)
                      ·
                        rfl

theorem cell23_1570685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 4, 3, 3].length) (baseStart_1570685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570685 prefixEnd_1570685 := by exact prefixLift 1570685
  have htrace : WordTrace (prefixWord ++ tailWord_1570685) baseStart_1570685 baseEnd_1570685 := by
    simpa [prefixWord, tailWord_1570685, baseEnd_1570685] using wordTrace_append hprefix tailTrace_1570685
  have hstable : (prefixWord ++ tailWord_1570685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570685).length < 2 ^ (prefixWord ++ tailWord_1570685).sum := by decide
  have hdescent : baseEnd_1570685 < baseStart_1570685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570686 : List Nat := [4, 2, 3, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_1570686 : Nat := 118140960795 + 1570686 * 2 ^ 59
def prefixEnd_1570686 : Nat := 4983230072969 + 3 ^ 40 * 1570686 * 2
def baseEnd_1570686 : Nat := 806516875287946917501553

theorem tailTrace_1570686 : CollatzResearch.WordTrace tailWord_1570686 prefixEnd_1570686 806516875287946917501553 := by
  unfold tailWord_1570686
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160953098460043582161489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38191749858453565771527941 7160953098460043582161489)
  ·
    refine ⟨5370714823845032686621117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7160953098460043582161489 5370714823845032686621117)
    ·
      refine ⟨2014018058941887257482919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5370714823845032686621117 2014018058941887257482919)
      ·
        refine ⟨3021027088412830886224379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2014018058941887257482919 3021027088412830886224379)
        ·
          refine ⟨4531540632619246329336569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3021027088412830886224379 4531540632619246329336569)
          ·
            refine ⟨3398655474464434747002427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4531540632619246329336569 3398655474464434747002427)
            ·
              refine ⟨5097983211696652120503641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3398655474464434747002427 5097983211696652120503641)
              ·
                refine ⟨3823487408772489090377731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5097983211696652120503641 3823487408772489090377731)
                ·
                  refine ⟨5735231113158733635566597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3823487408772489090377731 5735231113158733635566597)
                  ·
                    refine ⟨1075355833717262556668737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5735231113158733635566597 1075355833717262556668737)
                    ·
                      refine ⟨806516875287946917501553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1075355833717262556668737 806516875287946917501553)
                      ·
                        rfl

theorem cell23_1570686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_1570686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570686 prefixEnd_1570686 := by exact prefixLift 1570686
  have htrace : WordTrace (prefixWord ++ tailWord_1570686) baseStart_1570686 baseEnd_1570686 := by
    simpa [prefixWord, tailWord_1570686, baseEnd_1570686] using wordTrace_append hprefix tailTrace_1570686
  have hstable : (prefixWord ++ tailWord_1570686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570686).length < 2 ^ (prefixWord ++ tailWord_1570686).sum := by decide
  have hdescent : baseEnd_1570686 < baseStart_1570686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570705 : List Nat := [1, 2, 2, 1, 1, 1, 6, 2, 2, 5]
def baseStart_1570705 : Nat := 118140960795 + 1570705 * 2 ^ 59
def prefixEnd_1570705 : Nat := 4983230072969 + 3 ^ 40 * 1570705 * 2
def baseEnd_1570705 : Nat := 268842210473460781054655

theorem tailTrace_1570705 : CollatzResearch.WordTrace tailWord_1570705 prefixEnd_1570705 268842210473460781054655 := by
  unfold tailWord_1570705
  simp only [CollatzResearch.WordTrace]
  refine ⟨57288317774611514902233569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38192211849741009934822379 57288317774611514902233569)
  ·
    refine ⟨42966238330958636176675177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57288317774611514902233569 42966238330958636176675177)
    ·
      refine ⟨32224678748218977132506383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42966238330958636176675177 32224678748218977132506383)
      ·
        refine ⟨48337018122328465698759575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32224678748218977132506383 48337018122328465698759575)
        ·
          refine ⟨72505527183492698548139363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48337018122328465698759575 72505527183492698548139363)
          ·
            refine ⟨108758290775239047822209045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72505527183492698548139363 108758290775239047822209045)
            ·
              refine ⟨5098044880089330366666049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 108758290775239047822209045 5098044880089330366666049)
              ·
                refine ⟨3823533660066997774999537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5098044880089330366666049 3823533660066997774999537)
                ·
                  refine ⟨2867650245050248331249653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3823533660066997774999537 2867650245050248331249653)
                  ·
                    refine ⟨268842210473460781054655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2867650245050248331249653 268842210473460781054655)
                    ·
                      rfl

theorem cell23_1570705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_1570705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570705 prefixEnd_1570705 := by exact prefixLift 1570705
  have htrace : WordTrace (prefixWord ++ tailWord_1570705) baseStart_1570705 baseEnd_1570705 := by
    simpa [prefixWord, tailWord_1570705, baseEnd_1570705] using wordTrace_append hprefix tailTrace_1570705
  have hstable : (prefixWord ++ tailWord_1570705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570705).length < 2 ^ (prefixWord ++ tailWord_1570705).sum := by decide
  have hdescent : baseEnd_1570705 < baseStart_1570705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570725 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_1570725 : Nat := 118140960795 + 1570725 * 2 ^ 59
def prefixEnd_1570725 : Nat := 4983230072969 + 3 ^ 40 * 1570725 * 2
def baseEnd_1570725 : Nat := 806536901033472264913873

theorem tailTrace_1570725 : CollatzResearch.WordTrace tailWord_1570725 prefixEnd_1570725 806536901033472264913873 := by
  unfold tailWord_1570725
  simp only [CollatzResearch.WordTrace]
  refine ⟨57289047234539058317961629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38192698156359372211974419 57289047234539058317961629)
  ·
    refine ⟨21483392712952146869235611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57289047234539058317961629 21483392712952146869235611)
    ·
      refine ⟨32225089069428220303853417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21483392712952146869235611 32225089069428220303853417)
      ·
        refine ⟨24168816802071165227890063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32225089069428220303853417 24168816802071165227890063)
        ·
          refine ⟨36253225203106747841835095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24168816802071165227890063 36253225203106747841835095)
          ·
            refine ⟨54379837804660121762752643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36253225203106747841835095 54379837804660121762752643)
            ·
              refine ⟨81569756706990182644128965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54379837804660121762752643 81569756706990182644128965)
              ·
                refine ⟨15294329382560659245774181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81569756706990182644128965 15294329382560659245774181)
                ·
                  refine ⟨2867686759230123608582659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15294329382560659245774181 2867686759230123608582659)
                  ·
                    refine ⟨4301530138845185412873989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2867686759230123608582659 4301530138845185412873989)
                    ·
                      refine ⟨806536901033472264913873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4301530138845185412873989 806536901033472264913873)
                      ·
                        rfl

theorem cell23_1570725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_1570725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570725 prefixEnd_1570725 := by exact prefixLift 1570725
  have htrace : WordTrace (prefixWord ++ tailWord_1570725) baseStart_1570725 baseEnd_1570725 := by
    simpa [prefixWord, tailWord_1570725, baseEnd_1570725] using wordTrace_append hprefix tailTrace_1570725
  have hstable : (prefixWord ++ tailWord_1570725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570725).length < 2 ^ (prefixWord ++ tailWord_1570725).sum := by decide
  have hdescent : baseEnd_1570725 < baseStart_1570725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570762 : List Nat := [3, 1, 2, 1, 2, 1, 2, 4, 2, 2, 3]
def baseStart_1570762 : Nat := 118140960795 + 1570762 * 2 ^ 59
def prefixEnd_1570762 : Nat := 4983230072969 + 3 ^ 40 * 1570762 * 2
def baseEnd_1570762 : Nat := 806555899817688620151203

theorem tailTrace_1570762 : CollatzResearch.WordTrace tailWord_1570762 prefixEnd_1570762 806555899817688620151203 := by
  unfold tailWord_1570762
  simp only [CollatzResearch.WordTrace]
  refine ⟨14322599183851253409264635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38193597823603342424705693 14322599183851253409264635)
  ·
    refine ⟨21483898775776880113896953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14322599183851253409264635 21483898775776880113896953)
    ·
      refine ⟨16112924081832660085422715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21483898775776880113896953 16112924081832660085422715)
      ·
        refine ⟨24169386122748990128134073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16112924081832660085422715 24169386122748990128134073)
        ·
          refine ⟨18127039592061742596100555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24169386122748990128134073 18127039592061742596100555)
          ·
            refine ⟨27190559388092613894150833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18127039592061742596100555 27190559388092613894150833)
            ·
              refine ⟨20392919541069460420613125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27190559388092613894150833 20392919541069460420613125)
              ·
                refine ⟨3823672413950523828864961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20392919541069460420613125 3823672413950523828864961)
                ·
                  refine ⟨2867754310462892871648721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3823672413950523828864961 2867754310462892871648721)
                  ·
                    refine ⟨2150815732847169653736541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2867754310462892871648721 2150815732847169653736541)
                    ·
                      refine ⟨806555899817688620151203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2150815732847169653736541 806555899817688620151203)
                      ·
                        rfl

theorem cell23_1570762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 2, 2, 3].length) (baseStart_1570762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570762 prefixEnd_1570762 := by exact prefixLift 1570762
  have htrace : WordTrace (prefixWord ++ tailWord_1570762) baseStart_1570762 baseEnd_1570762 := by
    simpa [prefixWord, tailWord_1570762, baseEnd_1570762] using wordTrace_append hprefix tailTrace_1570762
  have hstable : (prefixWord ++ tailWord_1570762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570762).length < 2 ^ (prefixWord ++ tailWord_1570762).sum := by decide
  have hdescent : baseEnd_1570762 < baseStart_1570762 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570795 : List Nat := [1, 1, 1, 1, 2, 3, 1, 5, 3, 5]
def baseStart_1570795 : Nat := 118140960795 + 1570795 * 2 ^ 59
def prefixEnd_1570795 : Nat := 4983230072969 + 3 ^ 40 * 1570795 * 2
def baseEnd_1570795 : Nat := 268857614893095663679517

theorem tailTrace_1570795 : CollatzResearch.WordTrace tailWord_1570795 prefixEnd_1570795 268857614893095663679517 := by
  unfold tailWord_1570795
  simp only [CollatzResearch.WordTrace]
  refine ⟨57291600344285460273009839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38194400229523640182006559 57291600344285460273009839)
  ·
    refine ⟨85937400516428190409514759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57291600344285460273009839 85937400516428190409514759)
    ·
      refine ⟨128906100774642285614272139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85937400516428190409514759 128906100774642285614272139)
      ·
        refine ⟨193359151161963428421408209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128906100774642285614272139 193359151161963428421408209)
        ·
          refine ⟨145019363371472571316056157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193359151161963428421408209 145019363371472571316056157)
          ·
            refine ⟨54382261264302214243521059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145019363371472571316056157 54382261264302214243521059)
            ·
              refine ⟨81573391896453321365281589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54382261264302214243521059 81573391896453321365281589)
              ·
                refine ⟨7647505490292498877995149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81573391896453321365281589 7647505490292498877995149)
                ·
                  refine ⟨2867814558859687079248181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7647505490292498877995149 2867814558859687079248181)
                  ·
                    refine ⟨268857614893095663679517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2867814558859687079248181 268857614893095663679517)
                    ·
                      rfl

theorem cell23_1570795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 5].length) (baseStart_1570795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570795 prefixEnd_1570795 := by exact prefixLift 1570795
  have htrace : WordTrace (prefixWord ++ tailWord_1570795) baseStart_1570795 baseEnd_1570795 := by
    simpa [prefixWord, tailWord_1570795, baseEnd_1570795] using wordTrace_append hprefix tailTrace_1570795
  have hstable : (prefixWord ++ tailWord_1570795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570795).length < 2 ^ (prefixWord ++ tailWord_1570795).sum := by decide
  have hdescent : baseEnd_1570795 < baseStart_1570795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570812 : List Nat := [2, 2, 2, 1, 2, 2, 1, 5, 1, 5]
def baseStart_1570812 : Nat := 118140960795 + 1570812 * 2 ^ 59
def prefixEnd_1570812 : Nat := 4983230072969 + 3 ^ 40 * 1570812 * 2
def baseEnd_1570812 : Nat := 268860524616804474841991

theorem tailTrace_1570812 : CollatzResearch.WordTrace tailWord_1570812 prefixEnd_1570812 268860524616804474841991 := by
  unfold tailWord_1570812
  simp only [CollatzResearch.WordTrace]
  refine ⟨28646110192611936088189345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38194813590149248117585793 28646110192611936088189345)
  ·
    refine ⟨21484582644458952066142009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28646110192611936088189345 21484582644458952066142009)
    ·
      refine ⟨16113436983344214049606507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21484582644458952066142009 16113436983344214049606507)
      ·
        refine ⟨24170155475016321074409761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16113436983344214049606507 24170155475016321074409761)
        ·
          refine ⟨18127616606262240805807321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24170155475016321074409761 18127616606262240805807321)
          ·
            refine ⟨13595712454696680604355491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18127616606262240805807321 13595712454696680604355491)
            ·
              refine ⟨20393568682045020906533237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13595712454696680604355491 20393568682045020906533237)
              ·
                refine ⟨1911897063941720709987491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20393568682045020906533237 1911897063941720709987491)
                ·
                  refine ⟨2867845595912581064981237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911897063941720709987491 2867845595912581064981237)
                  ·
                    refine ⟨268860524616804474841991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2867845595912581064981237 268860524616804474841991)
                    ·
                      rfl

theorem cell23_1570812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_1570812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570812 prefixEnd_1570812 := by exact prefixLift 1570812
  have htrace : WordTrace (prefixWord ++ tailWord_1570812) baseStart_1570812 baseEnd_1570812 := by
    simpa [prefixWord, tailWord_1570812, baseEnd_1570812] using wordTrace_append hprefix tailTrace_1570812
  have hstable : (prefixWord ++ tailWord_1570812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570812).length < 2 ^ (prefixWord ++ tailWord_1570812).sum := by decide
  have hdescent : baseEnd_1570812 < baseStart_1570812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570820 : List Nat := [2, 3, 2, 4, 1, 1, 3, 2, 1, 4]
def baseStart_1570820 : Nat := 118140960795 + 1570820 * 2 ^ 59
def prefixEnd_1570820 : Nat := 4983230072969 + 3 ^ 40 * 1570820 * 2
def baseEnd_1570820 : Nat := 268861893898549797741979

theorem tailTrace_1570820 : CollatzResearch.WordTrace tailWord_1570820 prefixEnd_1570820 268861893898549797741979 := by
  unfold tailWord_1570820
  simp only [CollatzResearch.WordTrace]
  refine ⟨28646256084597444771334957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38195008112796593028446609 28646256084597444771334957)
  ·
    refine ⟨10742346031724041789250609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28646256084597444771334957 10742346031724041789250609)
    ·
      refine ⟨8056759523793031341937957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10742346031724041789250609 8056759523793031341937957)
      ·
        refine ⟨1510642410711193376613367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8056759523793031341937957 1510642410711193376613367)
        ·
          refine ⟨2265963616066790064920051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510642410711193376613367 2265963616066790064920051)
          ·
            refine ⟨3398945424100185097380077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2265963616066790064920051 3398945424100185097380077)
            ·
              refine ⟨1274604534037569411517529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3398945424100185097380077 1274604534037569411517529)
              ·
                refine ⟨955953400528177058638147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1274604534037569411517529 955953400528177058638147)
                ·
                  refine ⟨1433930100792265587957221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 955953400528177058638147 1433930100792265587957221)
                  ·
                    refine ⟨268861893898549797741979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1433930100792265587957221 268861893898549797741979)
                    ·
                      rfl

theorem cell23_1570820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 3, 2, 1, 4].length) (baseStart_1570820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570820 prefixEnd_1570820 := by exact prefixLift 1570820
  have htrace : WordTrace (prefixWord ++ tailWord_1570820) baseStart_1570820 baseEnd_1570820 := by
    simpa [prefixWord, tailWord_1570820, baseEnd_1570820] using wordTrace_append hprefix tailTrace_1570820
  have hstable : (prefixWord ++ tailWord_1570820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570820).length < 2 ^ (prefixWord ++ tailWord_1570820).sum := by decide
  have hdescent : baseEnd_1570820 < baseStart_1570820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570849 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_1570849 : Nat := 118140960795 + 1570849 * 2 ^ 59
def prefixEnd_1570849 : Nat := 4983230072969 + 3 ^ 40 * 1570849 * 2
def baseEnd_1570849 : Nat := 806600572634629779763303

theorem tailTrace_1570849 : CollatzResearch.WordTrace tailWord_1570849 prefixEnd_1570849 806600572634629779763303 := by
  unfold tailWord_1570849
  simp only [CollatzResearch.WordTrace]
  refine ⟨57293569886089827495475601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38195713257393218330317067 57293569886089827495475601)
  ·
    refine ⟨42970177414567370621606701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57293569886089827495475601 42970177414567370621606701)
    ·
      refine ⟨16113816530462763983102513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 42970177414567370621606701 16113816530462763983102513)
      ·
        refine ⟨12085362397847072987326885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16113816530462763983102513 12085362397847072987326885)
        ·
          refine ⟨2266005449596326185123791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12085362397847072987326885 2266005449596326185123791)
          ·
            refine ⟨3399008174394489277685687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266005449596326185123791 3399008174394489277685687)
            ·
              refine ⟨5098512261591733916528531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399008174394489277685687 5098512261591733916528531)
              ·
                refine ⟨7647768392387600874792797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5098512261591733916528531 7647768392387600874792797)
                ·
                  refine ⟨2867913147145350328047299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7647768392387600874792797 2867913147145350328047299)
                  ·
                    refine ⟨4301869720718025492070949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2867913147145350328047299 4301869720718025492070949)
                    ·
                      refine ⟨806600572634629779763303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4301869720718025492070949 806600572634629779763303)
                      ·
                        rfl

theorem cell23_1570849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_1570849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570849 prefixEnd_1570849 := by exact prefixLift 1570849
  have htrace : WordTrace (prefixWord ++ tailWord_1570849) baseStart_1570849 baseEnd_1570849 := by
    simpa [prefixWord, tailWord_1570849, baseEnd_1570849] using wordTrace_append hprefix tailTrace_1570849
  have hstable : (prefixWord ++ tailWord_1570849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570849).length < 2 ^ (prefixWord ++ tailWord_1570849).sum := by decide
  have hdescent : baseEnd_1570849 < baseStart_1570849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570866 : List Nat := [3, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4]
def baseStart_1570866 : Nat := 118140960795 + 1570866 * 2 ^ 59
def prefixEnd_1570866 : Nat := 4983230072969 + 3 ^ 40 * 1570866 * 2
def baseEnd_1570866 : Nat := 806609301805756213250725

theorem tailTrace_1570866 : CollatzResearch.WordTrace tailWord_1570866 prefixEnd_1570866 806609301805756213250725 := by
  unfold tailWord_1570866
  simp only [CollatzResearch.WordTrace]
  refine ⟨14323547481757059849711113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38196126618018826265896301 14323547481757059849711113)
  ·
    refine ⟨10742660611317794887283335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14323547481757059849711113 10742660611317794887283335)
    ·
      refine ⟨16113990916976692330925003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10742660611317794887283335 16113990916976692330925003)
      ·
        refine ⟨24170986375465038496387505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16113990916976692330925003 24170986375465038496387505)
        ·
          refine ⟨18128239781598778872290629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24170986375465038496387505 18128239781598778872290629)
          ·
            refine ⟨3399044959049771038554493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18128239781598778872290629 3399044959049771038554493)
            ·
              refine ⟨1274641859643664139457935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3399044959049771038554493 1274641859643664139457935)
              ·
                refine ⟨1911962789465496209186903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274641859643664139457935 1911962789465496209186903)
                ·
                  refine ⟨2867944184198244313780355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911962789465496209186903 2867944184198244313780355)
                  ·
                    refine ⟨4301916276297366470670533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2867944184198244313780355 4301916276297366470670533)
                    ·
                      refine ⟨806609301805756213250725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4301916276297366470670533 806609301805756213250725)
                      ·
                        rfl

theorem cell23_1570866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_1570866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570866 prefixEnd_1570866 := by exact prefixLift 1570866
  have htrace : WordTrace (prefixWord ++ tailWord_1570866) baseStart_1570866 baseEnd_1570866 := by
    simpa [prefixWord, tailWord_1570866, baseEnd_1570866] using wordTrace_append hprefix tailTrace_1570866
  have hstable : (prefixWord ++ tailWord_1570866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570866).length < 2 ^ (prefixWord ++ tailWord_1570866).sum := by decide
  have hdescent : baseEnd_1570866 < baseStart_1570866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570869 : List Nat := [1, 3, 3, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_1570869 : Nat := 118140960795 + 1570869 * 2 ^ 59
def prefixEnd_1570869 : Nat := 4983230072969 + 3 ^ 40 * 1570869 * 2
def baseEnd_1570869 : Nat := 806610842247719701513211

theorem tailTrace_1570869 : CollatzResearch.WordTrace tailWord_1570869 prefixEnd_1570869 806610842247719701513211 := by
  unfold tailWord_1570869
  simp only [CollatzResearch.WordTrace]
  refine ⟨57294299346017370911203661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38196199564011580607469107 57294299346017370911203661)
  ·
    refine ⟨21485362254756514091701373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57294299346017370911203661 21485362254756514091701373)
    ·
      refine ⟨8057010845533692784388015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21485362254756514091701373 8057010845533692784388015)
      ·
        refine ⟨12085516268300539176582023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8057010845533692784388015 12085516268300539176582023)
        ·
          refine ⟨18128274402450808764873035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12085516268300539176582023 18128274402450808764873035)
          ·
            refine ⟨27192411603676213147309553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18128274402450808764873035 27192411603676213147309553)
            ·
              refine ⟨20394308702757159860482165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27192411603676213147309553 20394308702757159860482165)
              ·
                refine ⟨1911966440883483736920203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 20394308702757159860482165 1911966440883483736920203)
                ·
                  refine ⟨2867949661325225605380305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1911966440883483736920203 2867949661325225605380305)
                  ·
                    refine ⟨2150962245993919204035229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2867949661325225605380305 2150962245993919204035229)
                    ·
                      refine ⟨806610842247719701513211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2150962245993919204035229 806610842247719701513211)
                      ·
                        rfl

theorem cell23_1570869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_1570869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570869 prefixEnd_1570869 := by exact prefixLift 1570869
  have htrace : WordTrace (prefixWord ++ tailWord_1570869) baseStart_1570869 baseEnd_1570869 := by
    simpa [prefixWord, tailWord_1570869, baseEnd_1570869] using wordTrace_append hprefix tailTrace_1570869
  have hstable : (prefixWord ++ tailWord_1570869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570869).length < 2 ^ (prefixWord ++ tailWord_1570869).sum := by decide
  have hdescent : baseEnd_1570869 < baseStart_1570869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570872 : List Nat := [2, 1, 2, 1, 7, 10]
def baseStart_1570872 : Nat := 118140960795 + 1570872 * 2 ^ 59
def prefixEnd_1570872 : Nat := 4983230072969 + 3 ^ 40 * 1570872 * 2
def baseEnd_1570872 : Nat := 3319392521356720945579

theorem tailTrace_1570872 : CollatzResearch.WordTrace tailWord_1570872 prefixEnd_1570872 3319392521356720945579 := by
  unfold tailWord_1570872
  simp only [CollatzResearch.WordTrace]
  refine ⟨28647204382503251211781435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38196272510004334949041913 28647204382503251211781435)
  ·
    refine ⟨42970806573754876817672153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28647204382503251211781435 42970806573754876817672153)
    ·
      refine ⟨32228104930316157613254115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42970806573754876817672153 32228104930316157613254115)
      ·
        refine ⟨48342157395474236419881173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32228104930316157613254115 48342157395474236419881173)
        ·
          refine ⟨1133019313956427416090965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 48342157395474236419881173 1133019313956427416090965)
          ·
            refine ⟨3319392521356720945579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1133019313956427416090965 3319392521356720945579)
            ·
              rfl

theorem cell23_1570872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 10].length) (baseStart_1570872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570872 prefixEnd_1570872 := by exact prefixLift 1570872
  have htrace : WordTrace (prefixWord ++ tailWord_1570872) baseStart_1570872 baseEnd_1570872 := by
    simpa [prefixWord, tailWord_1570872, baseEnd_1570872] using wordTrace_append hprefix tailTrace_1570872
  have hstable : (prefixWord ++ tailWord_1570872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570872).length < 2 ^ (prefixWord ++ tailWord_1570872).sum := by decide
  have hdescent : baseEnd_1570872 < baseStart_1570872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1570886 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1570886 : Nat := 118140960795 + 1570886 * 2 ^ 59
def prefixEnd_1570886 : Nat := 4983230072969 + 3 ^ 40 * 1570886 * 2
def baseEnd_1570886 : Nat := 806619571418846135000633

theorem tailTrace_1570886 : CollatzResearch.WordTrace tailWord_1570886 prefixEnd_1570886 806619571418846135000633 := by
  unfold tailWord_1570886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1790466230842368212955391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38196612924637188543048341 1790466230842368212955391)
  ·
    refine ⟨2685699346263552319433087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1790466230842368212955391 2685699346263552319433087)
    ·
      refine ⟨4028549019395328479149631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2685699346263552319433087 4028549019395328479149631)
      ·
        refine ⟨6042823529092992718724447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4028549019395328479149631 6042823529092992718724447)
        ·
          refine ⟨9064235293639489078086671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6042823529092992718724447 9064235293639489078086671)
          ·
            refine ⟨13596352940459233617130007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9064235293639489078086671 13596352940459233617130007)
            ·
              refine ⟨20394529410688850425695011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13596352940459233617130007 20394529410688850425695011)
              ·
                refine ⟨30591794116033275638542517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20394529410688850425695011 30591794116033275638542517)
                ·
                  refine ⟨2867980698378119591113361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30591794116033275638542517 2867980698378119591113361)
                  ·
                    refine ⟨2150985523783589693335021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2867980698378119591113361 2150985523783589693335021)
                    ·
                      refine ⟨806619571418846135000633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2150985523783589693335021 806619571418846135000633)
                      ·
                        rfl

theorem cell23_1570886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1570886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1570886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1570886 prefixEnd_1570886 := by exact prefixLift 1570886
  have htrace : WordTrace (prefixWord ++ tailWord_1570886) baseStart_1570886 baseEnd_1570886 := by
    simpa [prefixWord, tailWord_1570886, baseEnd_1570886] using wordTrace_append hprefix tailTrace_1570886
  have hstable : (prefixWord ++ tailWord_1570886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1570886).length < 2 ^ (prefixWord ++ tailWord_1570886).sum := by decide
  have hdescent : baseEnd_1570886 < baseStart_1570886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1570886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571002 : List Nat := [3, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_1571002 : Nat := 118140960795 + 1571002 * 2 ^ 59
def prefixEnd_1571002 : Nat := 4983230072969 + 3 ^ 40 * 1571002 * 2
def baseEnd_1571002 : Nat := 806679135174767681150099

theorem tailTrace_1571002 : CollatzResearch.WordTrace tailWord_1571002 prefixEnd_1571002 806679135174767681150099 := by
  unfold tailWord_1571002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14324787563633883656448815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38199433503023689750530173 14324787563633883656448815)
  ·
    refine ⟨21487181345450825484673223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14324787563633883656448815 21487181345450825484673223)
    ·
      refine ⟨32230772018176238227009835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21487181345450825484673223 32230772018176238227009835)
      ·
        refine ⟨48346158027264357340514753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32230772018176238227009835 48346158027264357340514753)
        ·
          refine ⟨36259618520448268005386065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48346158027264357340514753 36259618520448268005386065)
          ·
            refine ⟨27194713890336201004039549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36259618520448268005386065 27194713890336201004039549)
            ·
              refine ⟨10198017708876075376514831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27194713890336201004039549 10198017708876075376514831)
              ·
                refine ⟨15297026563314113064772247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10198017708876075376514831 15297026563314113064772247)
                ·
                  refine ⟨22945539844971169597158371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15297026563314113064772247 22945539844971169597158371)
                  ·
                    refine ⟨34418309767456754395737557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22945539844971169597158371 34418309767456754395737557)
                    ·
                      refine ⟨806679135174767681150099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34418309767456754395737557 806679135174767681150099)
                      ·
                        rfl

theorem cell23_1571002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_1571002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571002 prefixEnd_1571002 := by exact prefixLift 1571002
  have htrace : WordTrace (prefixWord ++ tailWord_1571002) baseStart_1571002 baseEnd_1571002 := by
    simpa [prefixWord, tailWord_1571002, baseEnd_1571002] using wordTrace_append hprefix tailTrace_1571002
  have hstable : (prefixWord ++ tailWord_1571002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571002).length < 2 ^ (prefixWord ++ tailWord_1571002).sum := by decide
  have hdescent : baseEnd_1571002 < baseStart_1571002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571026 : List Nat := [3, 2, 2, 2, 1, 3, 2, 1, 2, 5]
def baseStart_1571026 : Nat := 118140960795 + 1571026 * 2 ^ 59
def prefixEnd_1571026 : Nat := 4983230072969 + 3 ^ 40 * 1571026 * 2
def baseEnd_1571026 : Nat := 268897152903491862416663

theorem tailTrace_1571026 : CollatzResearch.WordTrace tailWord_1571026 prefixEnd_1571026 268897152903491862416663 := by
  unfold tailWord_1571026
  simp only [CollatzResearch.WordTrace]
  refine ⟨14325006401612146681167233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38200017070965724483112621 14325006401612146681167233)
  ·
    refine ⟨10743754801209110010875425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14325006401612146681167233 10743754801209110010875425)
    ·
      refine ⟨8057816100906832508156569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10743754801209110010875425 8057816100906832508156569)
      ·
        refine ⟨6043362075680124381117427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8057816100906832508156569 6043362075680124381117427)
        ·
          refine ⟨9065043113520186571676141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6043362075680124381117427 9065043113520186571676141)
          ·
            refine ⟨3399391167570069964378553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9065043113520186571676141 3399391167570069964378553)
            ·
              refine ⟨2549543375677552473283915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3399391167570069964378553 2549543375677552473283915)
              ·
                refine ⟨3824315063516328709925873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549543375677552473283915 3824315063516328709925873)
                ·
                  refine ⟨2868236297637246532444405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3824315063516328709925873 2868236297637246532444405)
                  ·
                    refine ⟨268897152903491862416663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2868236297637246532444405 268897152903491862416663)
                    ·
                      rfl

theorem cell23_1571026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_1571026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571026 prefixEnd_1571026 := by exact prefixLift 1571026
  have htrace : WordTrace (prefixWord ++ tailWord_1571026) baseStart_1571026 baseEnd_1571026 := by
    simpa [prefixWord, tailWord_1571026, baseEnd_1571026] using wordTrace_append hprefix tailTrace_1571026
  have hstable : (prefixWord ++ tailWord_1571026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571026).length < 2 ^ (prefixWord ++ tailWord_1571026).sum := by decide
  have hdescent : baseEnd_1571026 < baseStart_1571026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571096 : List Nat := [2, 1, 2, 3, 1, 2, 1, 2, 5, 1, 3]
def baseStart_1571096 : Nat := 118140960795 + 1571096 * 2 ^ 59
def prefixEnd_1571096 : Nat := 4983230072969 + 3 ^ 40 * 1571096 * 2
def baseEnd_1571096 : Nat := 806727402356290313374667

theorem tailTrace_1571096 : CollatzResearch.WordTrace tailWord_1571096 prefixEnd_1571096 806727402356290313374667 := by
  unfold tailWord_1571096
  simp only [CollatzResearch.WordTrace]
  refine ⟨28651289358097494339858571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38201719144129992453144761 28651289358097494339858571)
  ·
    refine ⟨42976934037146241509787857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28651289358097494339858571 42976934037146241509787857)
    ·
      refine ⟨32232700527859681132340893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42976934037146241509787857 32232700527859681132340893)
      ·
        refine ⟨12087262697947380424627835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32232700527859681132340893 12087262697947380424627835)
        ·
          refine ⟨18130894046921070636941753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12087262697947380424627835 18130894046921070636941753)
          ·
            refine ⟨13598170535190802977706315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18130894046921070636941753 13598170535190802977706315)
            ·
              refine ⟨20397255802786204466559473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13598170535190802977706315 20397255802786204466559473)
              ·
                refine ⟨15297941852089653349919605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20397255802786204466559473 15297941852089653349919605)
                ·
                  refine ⟨1434182048633405001554963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15297941852089653349919605 1434182048633405001554963)
                  ·
                    refine ⟨2151273072950107502332445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1434182048633405001554963 2151273072950107502332445)
                    ·
                      refine ⟨806727402356290313374667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2151273072950107502332445 806727402356290313374667)
                      ·
                        rfl

theorem cell23_1571096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 2, 5, 1, 3].length) (baseStart_1571096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571096 prefixEnd_1571096 := by exact prefixLift 1571096
  have htrace : WordTrace (prefixWord ++ tailWord_1571096) baseStart_1571096 baseEnd_1571096 := by
    simpa [prefixWord, tailWord_1571096, baseEnd_1571096] using wordTrace_append hprefix tailTrace_1571096
  have hstable : (prefixWord ++ tailWord_1571096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571096).length < 2 ^ (prefixWord ++ tailWord_1571096).sum := by decide
  have hdescent : baseEnd_1571096 < baseStart_1571096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571119 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 4]
def baseStart_1571119 : Nat := 118140960795 + 1571119 * 2 ^ 59
def prefixEnd_1571119 : Nat := 4983230072969 + 3 ^ 40 * 1571119 * 2
def baseEnd_1571119 : Nat := 806739212411343723387061

theorem tailTrace_1571119 : CollatzResearch.WordTrace tailWord_1571119 prefixEnd_1571119 806739212411343723387061 := by
  unfold tailWord_1571119
  simp only [CollatzResearch.WordTrace]
  refine ⟨57303417595111663607804411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38202278396741109071869607 57303417595111663607804411)
  ·
    refine ⟨85955126392667495411706617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57303417595111663607804411 85955126392667495411706617)
    ·
      refine ⟨64466344794500621558779963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85955126392667495411706617 64466344794500621558779963)
      ·
        refine ⟨96699517191750932338169945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64466344794500621558779963 96699517191750932338169945)
        ·
          refine ⟨72524637893813199253627459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96699517191750932338169945 72524637893813199253627459)
          ·
            refine ⟨108786956840719798880441189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72524637893813199253627459 108786956840719798880441189)
            ·
              refine ⟨20397554407634962290082723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108786956840719798880441189 20397554407634962290082723)
              ·
                refine ⟨30596331611452443435124085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20397554407634962290082723 30596331611452443435124085)
                ·
                  refine ⟨2868406088573666572042883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30596331611452443435124085 2868406088573666572042883)
                  ·
                    refine ⟨4302609132860499858064325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2868406088573666572042883 4302609132860499858064325)
                    ·
                      refine ⟨806739212411343723387061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4302609132860499858064325 806739212411343723387061)
                      ·
                        rfl

theorem cell23_1571119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 4].length) (baseStart_1571119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571119 prefixEnd_1571119 := by exact prefixLift 1571119
  have htrace : WordTrace (prefixWord ++ tailWord_1571119) baseStart_1571119 baseEnd_1571119 := by
    simpa [prefixWord, tailWord_1571119, baseEnd_1571119] using wordTrace_append hprefix tailTrace_1571119
  have hstable : (prefixWord ++ tailWord_1571119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571119).length < 2 ^ (prefixWord ++ tailWord_1571119).sum := by decide
  have hdescent : baseEnd_1571119 < baseStart_1571119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571156 : List Nat := [2, 4, 1, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_1571156 : Nat := 118140960795 + 1571156 * 2 ^ 59
def prefixEnd_1571156 : Nat := 4983230072969 + 3 ^ 40 * 1571156 * 2
def baseEnd_1571156 : Nat := 806758211195560078624391

theorem tailTrace_1571156 : CollatzResearch.WordTrace tailWord_1571156 prefixEnd_1571156 806758211195560078624391 := by
  unfold tailWord_1571156
  simp only [CollatzResearch.WordTrace]
  refine ⟨28652383547988809463450661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38203178063985079284600881 28652383547988809463450661)
  ·
    refine ⟨5372321915247901774396999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28652383547988809463450661 5372321915247901774396999)
    ·
      refine ⟨8058482872871852661595499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5372321915247901774396999 8058482872871852661595499)
      ·
        refine ⟨12087724309307778992393249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8058482872871852661595499 12087724309307778992393249)
        ·
          refine ⟨9065793231980834244294937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12087724309307778992393249 9065793231980834244294937)
          ·
            refine ⟨6799344923985625683221203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9065793231980834244294937 6799344923985625683221203)
            ·
              refine ⟨10199017385978438524831805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6799344923985625683221203 10199017385978438524831805)
              ·
                refine ⟨3824631519741914446811927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10199017385978438524831805 3824631519741914446811927)
                ·
                  refine ⟨5736947279612871670217891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824631519741914446811927 5736947279612871670217891)
                  ·
                    refine ⟨8605420919419307505326837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5736947279612871670217891 8605420919419307505326837)
                    ·
                      refine ⟨806758211195560078624391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8605420919419307505326837 806758211195560078624391)
                      ·
                        rfl

theorem cell23_1571156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_1571156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571156 prefixEnd_1571156 := by exact prefixLift 1571156
  have htrace : WordTrace (prefixWord ++ tailWord_1571156) baseStart_1571156 baseEnd_1571156 := by
    simpa [prefixWord, tailWord_1571156, baseEnd_1571156] using wordTrace_append hprefix tailTrace_1571156
  have hstable : (prefixWord ++ tailWord_1571156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571156).length < 2 ^ (prefixWord ++ tailWord_1571156).sum := by decide
  have hdescent : baseEnd_1571156 < baseStart_1571156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571164 : List Nat := [2, 2, 4, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_1571164 : Nat := 118140960795 + 1571164 * 2 ^ 59
def prefixEnd_1571164 : Nat := 4983230072969 + 3 ^ 40 * 1571164 * 2
def baseEnd_1571164 : Nat := 806762319040796047324355

theorem tailTrace_1571164 : CollatzResearch.WordTrace tailWord_1571164 prefixEnd_1571164 806762319040796047324355 := by
  unfold tailWord_1571164
  simp only [CollatzResearch.WordTrace]
  refine ⟨28652529439974318146596273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38203372586632424195461697 28652529439974318146596273)
  ·
    refine ⟨21489397079980738609947205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28652529439974318146596273 21489397079980738609947205)
    ·
      refine ⟨4029261952496388489365101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21489397079980738609947205 4029261952496388489365101)
      ·
        refine ⟨1510973232186145683511913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4029261952496388489365101 1510973232186145683511913)
        ·
          refine ⟨1133229924139609262633935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1510973232186145683511913 1133229924139609262633935)
          ·
            refine ⟨1699844886209413893950903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133229924139609262633935 1699844886209413893950903)
            ·
              refine ⟨2549767329314120840926355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1699844886209413893950903 2549767329314120840926355)
              ·
                refine ⟨3824650993971181261389533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2549767329314120840926355 3824650993971181261389533)
                ·
                  refine ⟨1434244122739192973021075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3824650993971181261389533 1434244122739192973021075)
                  ·
                    refine ⟨2151366184108789459531613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1434244122739192973021075 2151366184108789459531613)
                    ·
                      refine ⟨806762319040796047324355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2151366184108789459531613 806762319040796047324355)
                      ·
                        rfl

theorem cell23_1571164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_1571164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571164 prefixEnd_1571164 := by exact prefixLift 1571164
  have htrace : WordTrace (prefixWord ++ tailWord_1571164) baseStart_1571164 baseEnd_1571164 := by
    simpa [prefixWord, tailWord_1571164, baseEnd_1571164] using wordTrace_append hprefix tailTrace_1571164
  have hstable : (prefixWord ++ tailWord_1571164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571164).length < 2 ^ (prefixWord ++ tailWord_1571164).sum := by decide
  have hdescent : baseEnd_1571164 < baseStart_1571164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571176 : List Nat := [2, 1, 4, 2, 2, 2, 2, 8]
def baseStart_1571176 : Nat := 118140960795 + 1571176 * 2 ^ 59
def prefixEnd_1571176 : Nat := 4983230072969 + 3 ^ 40 * 1571176 * 2
def baseEnd_1571176 : Nat := 29880314104024074087937

theorem tailTrace_1571176 : CollatzResearch.WordTrace tailWord_1571176 prefixEnd_1571176 29880314104024074087937 := by
  unfold tailWord_1571176
  simp only [CollatzResearch.WordTrace]
  refine ⟨28652748277952581171314691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38203664370603441561752921 28652748277952581171314691)
  ·
    refine ⟨42979122416928871756972037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28652748277952581171314691 42979122416928871756972037)
    ·
      refine ⟨8058585453174163454432257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 42979122416928871756972037 8058585453174163454432257)
      ·
        refine ⟨6043939089880622590824193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8058585453174163454432257 6043939089880622590824193)
        ·
          refine ⟨4532954317410466943118145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6043939089880622590824193 4532954317410466943118145)
          ·
            refine ⟨3399715738057850207338609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4532954317410466943118145 3399715738057850207338609)
            ·
              refine ⟨2549786803543387655503957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3399715738057850207338609 2549786803543387655503957)
              ·
                refine ⟨29880314104024074087937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2549786803543387655503957 29880314104024074087937)
                ·
                  rfl

theorem cell23_1571176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 8].length) (baseStart_1571176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571176 prefixEnd_1571176 := by exact prefixLift 1571176
  have htrace : WordTrace (prefixWord ++ tailWord_1571176) baseStart_1571176 baseEnd_1571176 := by
    simpa [prefixWord, tailWord_1571176, baseEnd_1571176] using wordTrace_append hprefix tailTrace_1571176
  have hstable : (prefixWord ++ tailWord_1571176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571176).length < 2 ^ (prefixWord ++ tailWord_1571176).sum := by decide
  have hdescent : baseEnd_1571176 < baseStart_1571176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571203 : List Nat := [1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 3]
def baseStart_1571203 : Nat := 118140960795 + 1571203 * 2 ^ 59
def prefixEnd_1571203 : Nat := 4983230072969 + 3 ^ 40 * 1571203 * 2
def baseEnd_1571203 : Nat := 806782344786321394736675

theorem tailTrace_1571203 : CollatzResearch.WordTrace tailWord_1571203 prefixEnd_1571203 806782344786321394736675 := by
  unfold tailWord_1571203
  simp only [CollatzResearch.WordTrace]
  refine ⟨57306481326807345953862263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38204320884538230635908175 57306481326807345953862263)
  ·
    refine ⟨85959721990211018930793395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57306481326807345953862263 85959721990211018930793395)
    ·
      refine ⟨128939582985316528396190093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85959721990211018930793395 128939582985316528396190093)
      ·
        refine ⟨48352343619493698148571285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 128939582985316528396190093 48352343619493698148571285)
        ·
          refine ⟨2266516107163767100714279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 48352343619493698148571285 2266516107163767100714279)
          ·
            refine ⟨3399774160745650651071419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2266516107163767100714279 3399774160745650651071419)
            ·
              refine ⟨5099661241118475976607129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3399774160745650651071419 5099661241118475976607129)
              ·
                refine ⟨3824745930838856982455347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5099661241118475976607129 3824745930838856982455347)
                ·
                  refine ⟨5737118896258285473683021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824745930838856982455347 5737118896258285473683021)
                  ·
                    refine ⟨2151419586096857052631133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5737118896258285473683021 2151419586096857052631133)
                    ·
                      refine ⟨806782344786321394736675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2151419586096857052631133 806782344786321394736675)
                      ·
                        rfl

theorem cell23_1571203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 1, 3, 3].length) (baseStart_1571203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571203 prefixEnd_1571203 := by exact prefixLift 1571203
  have htrace : WordTrace (prefixWord ++ tailWord_1571203) baseStart_1571203 baseEnd_1571203 := by
    simpa [prefixWord, tailWord_1571203, baseEnd_1571203] using wordTrace_append hprefix tailTrace_1571203
  have hstable : (prefixWord ++ tailWord_1571203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571203).length < 2 ^ (prefixWord ++ tailWord_1571203).sum := by decide
  have hdescent : baseEnd_1571203 < baseStart_1571203 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571226 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1571226 : Nat := 118140960795 + 1571226 * 2 ^ 59
def prefixEnd_1571226 : Nat := 4983230072969 + 3 ^ 40 * 1571226 * 2
def baseEnd_1571226 : Nat := 806794154841374804749069

theorem tailTrace_1571226 : CollatzResearch.WordTrace tailWord_1571226 prefixEnd_1571226 806794154841374804749069 := by
  unfold tailWord_1571226
  simp only [CollatzResearch.WordTrace]
  refine ⟨14326830051431005220487383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38204880137149347254633021 14326830051431005220487383)
  ·
    refine ⟨21490245077146507830731075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14326830051431005220487383 21490245077146507830731075)
    ·
      refine ⟨32235367615719761746096613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21490245077146507830731075 32235367615719761746096613)
      ·
        refine ⟨6044131427947455327393115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32235367615719761746096613 6044131427947455327393115)
        ·
          refine ⟨9066197141921182991089673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044131427947455327393115 9066197141921182991089673)
          ·
            refine ⟨6799647856440887243317255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9066197141921182991089673 6799647856440887243317255)
            ·
              refine ⟨10199471784661330864975883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6799647856440887243317255 10199471784661330864975883)
              ·
                refine ⟨15299207676991996297463825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10199471784661330864975883 15299207676991996297463825)
                ·
                  refine ⟨11474405757743997223097869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15299207676991996297463825 11474405757743997223097869)
                  ·
                    refine ⟨4302902159153998958661701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11474405757743997223097869 4302902159153998958661701)
                    ·
                      refine ⟨806794154841374804749069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4302902159153998958661701 806794154841374804749069)
                      ·
                        rfl

theorem cell23_1571226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1571226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571226 prefixEnd_1571226 := by exact prefixLift 1571226
  have htrace : WordTrace (prefixWord ++ tailWord_1571226) baseStart_1571226 baseEnd_1571226 := by
    simpa [prefixWord, tailWord_1571226, baseEnd_1571226] using wordTrace_append hprefix tailTrace_1571226
  have hstable : (prefixWord ++ tailWord_1571226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571226).length < 2 ^ (prefixWord ++ tailWord_1571226).sum := by decide
  have hdescent : baseEnd_1571226 < baseStart_1571226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571260 : List Nat := [2, 2, 2, 4, 1, 1, 2, 2, 1, 4, 2]
def baseStart_1571260 : Nat := 118140960795 + 1571260 * 2 ^ 59
def prefixEnd_1571260 : Nat := 4983230072969 + 3 ^ 40 * 1571260 * 2
def baseEnd_1571260 : Nat := 806811613183627671723913

theorem tailTrace_1571260 : CollatzResearch.WordTrace tailWord_1571260 prefixEnd_1571260 806811613183627671723913 := by
  unfold tailWord_1571260
  simp only [CollatzResearch.WordTrace]
  refine ⟨28654280143800422344343617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38205706858400563125791489 28654280143800422344343617)
  ·
    refine ⟨21490710107850316758257713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28654280143800422344343617 21490710107850316758257713)
    ·
      refine ⟨16118032580887737568693285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21490710107850316758257713 16118032580887737568693285)
      ·
        refine ⟨3022131108916450794129991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16118032580887737568693285 3022131108916450794129991)
        ·
          refine ⟨4533196663374676191194987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3022131108916450794129991 4533196663374676191194987)
          ·
            refine ⟨6799794995062014286792481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533196663374676191194987 6799794995062014286792481)
            ·
              refine ⟨5099846246296510715094361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6799794995062014286792481 5099846246296510715094361)
              ·
                refine ⟨3824884684722383036320771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5099846246296510715094361 3824884684722383036320771)
                ·
                  refine ⟨5737327027083574554481157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3824884684722383036320771 5737327027083574554481157)
                  ·
                    refine ⟨1075748817578170228965217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5737327027083574554481157 1075748817578170228965217)
                    ·
                      refine ⟨806811613183627671723913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1075748817578170228965217 806811613183627671723913)
                      ·
                        rfl

theorem cell23_1571260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_1571260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571260 prefixEnd_1571260 := by exact prefixLift 1571260
  have htrace : WordTrace (prefixWord ++ tailWord_1571260) baseStart_1571260 baseEnd_1571260 := by
    simpa [prefixWord, tailWord_1571260, baseEnd_1571260] using wordTrace_append hprefix tailTrace_1571260
  have hstable : (prefixWord ++ tailWord_1571260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571260).length < 2 ^ (prefixWord ++ tailWord_1571260).sum := by decide
  have hdescent : baseEnd_1571260 < baseStart_1571260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571293 : List Nat := [1, 4, 3, 1, 1, 1, 1, 3, 2, 3, 3]
def baseStart_1571293 : Nat := 118140960795 + 1571293 * 2 ^ 59
def prefixEnd_1571293 : Nat := 4983230072969 + 3 ^ 40 * 1571293 * 2
def baseEnd_1571293 : Nat := 806828558045226042611261

theorem tailTrace_1571293 : CollatzResearch.WordTrace tailWord_1571293 prefixEnd_1571293 806828558045226042611261 := by
  unfold tailWord_1571293
  simp only [CollatzResearch.WordTrace]
  refine ⟨57309763896481291324638533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38206509264320860883092355 57309763896481291324638533)
  ·
    refine ⟨10745580730590242123369725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57309763896481291324638533 10745580730590242123369725)
    ·
      refine ⟨4029592773971340796263647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10745580730590242123369725 4029592773971340796263647)
      ·
        refine ⟨6044389160957011194395471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029592773971340796263647 6044389160957011194395471)
        ·
          refine ⟨9066583741435516791593207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044389160957011194395471 9066583741435516791593207)
          ·
            refine ⟨13599875612153275187389811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9066583741435516791593207 13599875612153275187389811)
            ·
              refine ⟨20399813418229912781084717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13599875612153275187389811 20399813418229912781084717)
              ·
                refine ⟨7649930031836217292906769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20399813418229912781084717 7649930031836217292906769)
                ·
                  refine ⟨5737447523877162969680077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7649930031836217292906769 5737447523877162969680077)
                  ·
                    refine ⟨2151542821453936113630029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5737447523877162969680077 2151542821453936113630029)
                    ·
                      refine ⟨806828558045226042611261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2151542821453936113630029 806828558045226042611261)
                      ·
                        rfl

theorem cell23_1571293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_1571293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571293 prefixEnd_1571293 := by exact prefixLift 1571293
  have htrace : WordTrace (prefixWord ++ tailWord_1571293) baseStart_1571293 baseEnd_1571293 := by
    simpa [prefixWord, tailWord_1571293, baseEnd_1571293] using wordTrace_append hprefix tailTrace_1571293
  have hstable : (prefixWord ++ tailWord_1571293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571293).length < 2 ^ (prefixWord ++ tailWord_1571293).sum := by decide
  have hdescent : baseEnd_1571293 < baseStart_1571293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571333 : List Nat := [1, 3, 1, 1, 2, 2, 2, 1, 4, 4, 2]
def baseStart_1571333 : Nat := 118140960795 + 1571333 * 2 ^ 59
def prefixEnd_1571333 : Nat := 4983230072969 + 3 ^ 40 * 1571333 * 2
def baseEnd_1571333 : Nat := 806849097271405886111077

theorem tailTrace_1571333 : CollatzResearch.WordTrace tailWord_1571333 prefixEnd_1571333 806849097271405886111077 := by
  unfold tailWord_1571333
  simp only [CollatzResearch.WordTrace]
  refine ⟨57311222816336378156094653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38207481877557585437396435 57311222816336378156094653)
  ·
    refine ⟨21491708556126141808535495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57311222816336378156094653 21491708556126141808535495)
    ·
      refine ⟨32237562834189212712803243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21491708556126141808535495 32237562834189212712803243)
      ·
        refine ⟨48356344251283819069204865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32237562834189212712803243 48356344251283819069204865)
        ·
          refine ⟨36267258188462864301903649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48356344251283819069204865 36267258188462864301903649)
          ·
            refine ⟨27200443641347148226427737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36267258188462864301903649 27200443641347148226427737)
            ·
              refine ⟨20400332731010361169820803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27200443641347148226427737 20400332731010361169820803)
              ·
                refine ⟨30600499096515541754731205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20400332731010361169820803 30600499096515541754731205)
                ·
                  refine ⟨5737593580596664079012101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30600499096515541754731205 5737593580596664079012101)
                  ·
                    refine ⟨1075798796361874514814769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5737593580596664079012101 1075798796361874514814769)
                    ·
                      refine ⟨806849097271405886111077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1075798796361874514814769 806849097271405886111077)
                      ·
                        rfl

theorem cell23_1571333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 4, 2].length) (baseStart_1571333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571333 prefixEnd_1571333 := by exact prefixLift 1571333
  have htrace : WordTrace (prefixWord ++ tailWord_1571333) baseStart_1571333 baseEnd_1571333 := by
    simpa [prefixWord, tailWord_1571333, baseEnd_1571333] using wordTrace_append hprefix tailTrace_1571333
  have hstable : (prefixWord ++ tailWord_1571333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571333).length < 2 ^ (prefixWord ++ tailWord_1571333).sum := by decide
  have hdescent : baseEnd_1571333 < baseStart_1571333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571334 : List Nat := [6, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_1571334 : Nat := 118140960795 + 1571334 * 2 ^ 59
def prefixEnd_1571334 : Nat := 4983230072969 + 3 ^ 40 * 1571334 * 2
def baseEnd_1571334 : Nat := 89649956750228931355397

theorem tailTrace_1571334 : CollatzResearch.WordTrace tailWord_1571334 prefixEnd_1571334 89649956750228931355397 := by
  unfold tailWord_1571334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1790976852791648603965033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 38207506192888503551254037 1790976852791648603965033)
  ·
    refine ⟨1343232639593736452973775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1790976852791648603965033 1343232639593736452973775)
    ·
      refine ⟨2014848959390604679460663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1343232639593736452973775 2014848959390604679460663)
      ·
        refine ⟨3022273439085907019190995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2014848959390604679460663 3022273439085907019190995)
        ·
          refine ⟨4533410158628860528786493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3022273439085907019190995 4533410158628860528786493)
          ·
            refine ⟨1700028809485822698294935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4533410158628860528786493 1700028809485822698294935)
            ·
              refine ⟨2550043214228734047442403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700028809485822698294935 2550043214228734047442403)
              ·
                refine ⟨3825064821343101071163605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2550043214228734047442403 3825064821343101071163605)
                ·
                  refine ⟨89649956750228931355397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3825064821343101071163605 89649956750228931355397)
                  ·
                    rfl

theorem cell23_1571334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_1571334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571334 prefixEnd_1571334 := by exact prefixLift 1571334
  have htrace : WordTrace (prefixWord ++ tailWord_1571334) baseStart_1571334 baseEnd_1571334 := by
    simpa [prefixWord, tailWord_1571334, baseEnd_1571334] using wordTrace_append hprefix tailTrace_1571334
  have hstable : (prefixWord ++ tailWord_1571334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571334).length < 2 ^ (prefixWord ++ tailWord_1571334).sum := by decide
  have hdescent : baseEnd_1571334 < baseStart_1571334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571370 : List Nat := [3, 1, 4, 1, 1, 2, 1, 3, 2, 2, 3]
def baseStart_1571370 : Nat := 118140960795 + 1571370 * 2 ^ 59
def prefixEnd_1571370 : Nat := 4983230072969 + 3 ^ 40 * 1571370 * 2
def baseEnd_1571370 : Nat := 806868096055622241348407

theorem tailTrace_1571370 : CollatzResearch.WordTrace tailWord_1571370 prefixEnd_1571370 806868096055622241348407 := by
  unfold tailWord_1571370
  simp only [CollatzResearch.WordTrace]
  refine ⟨14328143079300583368797891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38208381544801555650127709 14328143079300583368797891)
  ·
    refine ⟨21492214618950875053196837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14328143079300583368797891 21492214618950875053196837)
    ·
      refine ⟨4029790241053289072474407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21492214618950875053196837 4029790241053289072474407)
      ·
        refine ⟨6044685361579933608711611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4029790241053289072474407 6044685361579933608711611)
        ·
          refine ⟨9067028042369900413067417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044685361579933608711611 9067028042369900413067417)
          ·
            refine ⟨6800271031777425309800563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9067028042369900413067417 6800271031777425309800563)
            ·
              refine ⟨10200406547666137964700845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6800271031777425309800563 10200406547666137964700845)
              ·
                refine ⟨3825152455374801736762817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10200406547666137964700845 3825152455374801736762817)
                ·
                  refine ⟨2868864341531101302572113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3825152455374801736762817 2868864341531101302572113)
                  ·
                    refine ⟨2151648256148325976929085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2868864341531101302572113 2151648256148325976929085)
                    ·
                      refine ⟨806868096055622241348407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2151648256148325976929085 806868096055622241348407)
                      ·
                        rfl

theorem cell23_1571370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_1571370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571370 prefixEnd_1571370 := by exact prefixLift 1571370
  have htrace : WordTrace (prefixWord ++ tailWord_1571370) baseStart_1571370 baseEnd_1571370 := by
    simpa [prefixWord, tailWord_1571370, baseEnd_1571370] using wordTrace_append hprefix tailTrace_1571370
  have hstable : (prefixWord ++ tailWord_1571370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571370).length < 2 ^ (prefixWord ++ tailWord_1571370).sum := by decide
  have hdescent : baseEnd_1571370 < baseStart_1571370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571410 : List Nat := [3, 2, 2, 1, 2, 1, 2, 2, 1, 5, 2]
def baseStart_1571410 : Nat := 118140960795 + 1571410 * 2 ^ 59
def prefixEnd_1571410 : Nat := 4983230072969 + 3 ^ 40 * 1571410 * 2
def baseEnd_1571410 : Nat := 806888635281802084848223

theorem tailTrace_1571410 : CollatzResearch.WordTrace tailWord_1571410 prefixEnd_1571410 806888635281802084848223 := by
  unfold tailWord_1571410
  simp only [CollatzResearch.WordTrace]
  refine ⟨14328507809264355076661921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38209354158038280204431789 14328507809264355076661921)
  ·
    refine ⟨10746380856948266307496441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14328507809264355076661921 10746380856948266307496441)
    ·
      refine ⟨8059785642711199730622331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10746380856948266307496441 8059785642711199730622331)
      ·
        refine ⟨12089678464066799595933497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8059785642711199730622331 12089678464066799595933497)
        ·
          refine ⟨9067258848050099696950123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12089678464066799595933497 9067258848050099696950123)
          ·
            refine ⟨13600888272075149545425185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9067258848050099696950123 13600888272075149545425185)
            ·
              refine ⟨10200666204056362159068889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13600888272075149545425185 10200666204056362159068889)
              ·
                refine ⟨7650499653042271619301667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10200666204056362159068889 7650499653042271619301667)
                ·
                  refine ⟨11475749479563407428952501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7650499653042271619301667 11475749479563407428952501)
                  ·
                    refine ⟨1075851513709069446464297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11475749479563407428952501 1075851513709069446464297)
                    ·
                      refine ⟨806888635281802084848223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1075851513709069446464297 806888635281802084848223)
                      ·
                        rfl

theorem cell23_1571410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_1571410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571410 prefixEnd_1571410 := by exact prefixLift 1571410
  have htrace : WordTrace (prefixWord ++ tailWord_1571410) baseStart_1571410 baseEnd_1571410 := by
    simpa [prefixWord, tailWord_1571410, baseEnd_1571410] using wordTrace_append hprefix tailTrace_1571410
  have hstable : (prefixWord ++ tailWord_1571410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571410).length < 2 ^ (prefixWord ++ tailWord_1571410).sum := by decide
  have hdescent : baseEnd_1571410 < baseStart_1571410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571433 : List Nat := [1, 2, 1, 1, 1, 4, 1, 4, 4, 4]
def baseStart_1571433 : Nat := 118140960795 + 1571433 * 2 ^ 59
def prefixEnd_1571433 : Nat := 4983230072969 + 3 ^ 40 * 1571433 * 2
def baseEnd_1571433 : Nat := 268966815112285164953539

theorem tailTrace_1571433 : CollatzResearch.WordTrace tailWord_1571433 prefixEnd_1571433 268966815112285164953539 := by
  unfold tailWord_1571433
  simp only [CollatzResearch.WordTrace]
  refine ⟨57314870115974095234734953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38209913410649396823156635 57314870115974095234734953)
  ·
    refine ⟨42986152586980571426051215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57314870115974095234734953 42986152586980571426051215)
    ·
      refine ⟨64479228880470857139076823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42986152586980571426051215 64479228880470857139076823)
      ·
        refine ⟨96718843320706285708615235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64479228880470857139076823 96718843320706285708615235)
        ·
          refine ⟨145078264981059428562922853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96718843320706285708615235 145078264981059428562922853)
          ·
            refine ⟨27202174683948642855548035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145078264981059428562922853 27202174683948642855548035)
            ·
              refine ⟨40803262025922964283322053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27202174683948642855548035 40803262025922964283322053)
              ·
                refine ⟨7650611629860555803122885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40803262025922964283322053 7650611629860555803122885)
                ·
                  refine ⟨1434489680598854213085541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7650611629860555803122885 1434489680598854213085541)
                  ·
                    refine ⟨268966815112285164953539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1434489680598854213085541 268966815112285164953539)
                    ·
                      rfl

theorem cell23_1571433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 4, 4, 4].length) (baseStart_1571433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571433 prefixEnd_1571433 := by exact prefixLift 1571433
  have htrace : WordTrace (prefixWord ++ tailWord_1571433) baseStart_1571433 baseEnd_1571433 := by
    simpa [prefixWord, tailWord_1571433, baseEnd_1571433] using wordTrace_append hprefix tailTrace_1571433
  have hstable : (prefixWord ++ tailWord_1571433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571433).length < 2 ^ (prefixWord ++ tailWord_1571433).sum := by decide
  have hdescent : baseEnd_1571433 < baseStart_1571433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571434 : List Nat := [3, 1, 3, 2, 1, 1, 4, 3, 1, 1, 3]
def baseStart_1571434 : Nat := 118140960795 + 1571434 * 2 ^ 59
def prefixEnd_1571434 : Nat := 4983230072969 + 3 ^ 40 * 1571434 * 2
def baseEnd_1571434 : Nat := 806900958817509990948113

theorem tailTrace_1571434 : CollatzResearch.WordTrace tailWord_1571434 prefixEnd_1571434 806900958817509990948113 := by
  unfold tailWord_1571434
  simp only [CollatzResearch.WordTrace]
  refine ⟨14328726647242618101380339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38209937725980314937014237 14328726647242618101380339)
  ·
    refine ⟨21493089970863927152070509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14328726647242618101380339 21493089970863927152070509)
    ·
      refine ⟨8059908739073972682026441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21493089970863927152070509 8059908739073972682026441)
      ·
        refine ⟨6044931554305479511519831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8059908739073972682026441 6044931554305479511519831)
        ·
          refine ⟨9067397331458219267279747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6044931554305479511519831 9067397331458219267279747)
          ·
            refine ⟨13601095997187328900919621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9067397331458219267279747 13601095997187328900919621)
            ·
              refine ⟨2550205499472624168922429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13601095997187328900919621 2550205499472624168922429)
              ·
                refine ⟨956327062302234063345911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2550205499472624168922429 956327062302234063345911)
                ·
                  refine ⟨1434490593453351095018867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956327062302234063345911 1434490593453351095018867)
                  ·
                    refine ⟨2151735890180026642528301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1434490593453351095018867 2151735890180026642528301)
                    ·
                      refine ⟨806900958817509990948113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2151735890180026642528301 806900958817509990948113)
                      ·
                        rfl

theorem cell23_1571434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_1571434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571434 prefixEnd_1571434 := by exact prefixLift 1571434
  have htrace : WordTrace (prefixWord ++ tailWord_1571434) baseStart_1571434 baseEnd_1571434 := by
    simpa [prefixWord, tailWord_1571434, baseEnd_1571434] using wordTrace_append hprefix tailTrace_1571434
  have hstable : (prefixWord ++ tailWord_1571434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571434).length < 2 ^ (prefixWord ++ tailWord_1571434).sum := by decide
  have hdescent : baseEnd_1571434 < baseStart_1571434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571437 : List Nat := [1, 5, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_1571437 : Nat := 118140960795 + 1571437 * 2 ^ 59
def prefixEnd_1571437 : Nat := 4983230072969 + 3 ^ 40 * 1571437 * 2
def baseEnd_1571437 : Nat := 268967499753157826403533

theorem tailTrace_1571437 : CollatzResearch.WordTrace tailWord_1571437 prefixEnd_1571437 268967499753157826403533 := by
  unfold tailWord_1571437
  simp only [CollatzResearch.WordTrace]
  refine ⟨57315016007959603917880565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38210010671973069278587043 57315016007959603917880565)
  ·
    refine ⟨5373282750746212867301303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 57315016007959603917880565 5373282750746212867301303)
    ·
      refine ⟨8059924126119319300951955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5373282750746212867301303 8059924126119319300951955)
      ·
        refine ⟨12089886189178978951427933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8059924126119319300951955 12089886189178978951427933)
        ·
          refine ⟨4533707320942117106785475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12089886189178978951427933 4533707320942117106785475)
          ·
            refine ⟨6800560981413175660178213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533707320942117106785475 6800560981413175660178213)
            ·
              refine ⟨1275105184014970436283415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6800560981413175660178213 1275105184014970436283415)
              ·
                refine ⟨1912657776022455654425123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275105184014970436283415 1912657776022455654425123)
                ·
                  refine ⟨2868986664033683481637685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912657776022455654425123 2868986664033683481637685)
                  ·
                    refine ⟨268967499753157826403533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2868986664033683481637685 268967499753157826403533)
                    ·
                      rfl

theorem cell23_1571437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_1571437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571437 prefixEnd_1571437 := by exact prefixLift 1571437
  have htrace : WordTrace (prefixWord ++ tailWord_1571437) baseStart_1571437 baseEnd_1571437 := by
    simpa [prefixWord, tailWord_1571437, baseEnd_1571437] using wordTrace_append hprefix tailTrace_1571437
  have hstable : (prefixWord ++ tailWord_1571437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571437).length < 2 ^ (prefixWord ++ tailWord_1571437).sum := by decide
  have hdescent : baseEnd_1571437 < baseStart_1571437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571443 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 3]
def baseStart_1571443 : Nat := 118140960795 + 1571443 * 2 ^ 59
def prefixEnd_1571443 : Nat := 4983230072969 + 3 ^ 40 * 1571443 * 2
def baseEnd_1571443 : Nat := 806905580143400455735571

theorem tailTrace_1571443 : CollatzResearch.WordTrace tailWord_1571443 prefixEnd_1571443 806905580143400455735571 := by
  unfold tailWord_1571443
  simp only [CollatzResearch.WordTrace]
  refine ⟨57315234845937866942598983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38210156563958577961732655 57315234845937866942598983)
  ·
    refine ⟨85972852268906800413898475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57315234845937866942598983 85972852268906800413898475)
    ·
      refine ⟨128959278403360200620847713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85972852268906800413898475 128959278403360200620847713)
      ·
        refine ⟨96719458802520150465635785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 128959278403360200620847713 96719458802520150465635785)
        ·
          refine ⟨72539594101890112849226839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96719458802520150465635785 72539594101890112849226839)
          ·
            refine ⟨108809391152835169273840259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72539594101890112849226839 108809391152835169273840259)
            ·
              refine ⟨163214086729252753910760389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108809391152835169273840259 163214086729252753910760389)
              ·
                refine ⟨30602641261734891358267573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163214086729252753910760389 30602641261734891358267573)
                ·
                  refine ⟨2868997618287646064837585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30602641261734891358267573 2868997618287646064837585)
                  ·
                    refine ⟨2151748213715734548628189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2868997618287646064837585 2151748213715734548628189)
                    ·
                      refine ⟨806905580143400455735571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2151748213715734548628189 806905580143400455735571)
                      ·
                        rfl

theorem cell23_1571443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 5, 2, 3].length) (baseStart_1571443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571443 prefixEnd_1571443 := by exact prefixLift 1571443
  have htrace : WordTrace (prefixWord ++ tailWord_1571443) baseStart_1571443 baseEnd_1571443 := by
    simpa [prefixWord, tailWord_1571443, baseEnd_1571443] using wordTrace_append hprefix tailTrace_1571443
  have hstable : (prefixWord ++ tailWord_1571443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571443).length < 2 ^ (prefixWord ++ tailWord_1571443).sum := by decide
  have hdescent : baseEnd_1571443 < baseStart_1571443 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571460 : List Nat := [2, 3, 2, 1, 3, 2, 1, 2, 1, 1, 5]
def baseStart_1571460 : Nat := 118140960795 + 1571460 * 2 ^ 59
def prefixEnd_1571460 : Nat := 4983230072969 + 3 ^ 40 * 1571460 * 2
def baseEnd_1571460 : Nat := 806914309314526889222993

theorem tailTrace_1571460 : CollatzResearch.WordTrace tailWord_1571460 prefixEnd_1571460 806914309314526889222993 := by
  unfold tailWord_1571460
  simp only [CollatzResearch.WordTrace]
  refine ⟨28657927443438139422983917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38210569924584185897311889 28657927443438139422983917)
  ·
    refine ⟨10746722791289302283618969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28657927443438139422983917 10746722791289302283618969)
    ·
      refine ⟨8060042093466976712714227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10746722791289302283618969 8060042093466976712714227)
      ·
        refine ⟨12090063140200465069071341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8060042093466976712714227 12090063140200465069071341)
        ·
          refine ⟨4533773677575174400901753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12090063140200465069071341 4533773677575174400901753)
          ·
            refine ⟨3400330258181380800676315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4533773677575174400901753 3400330258181380800676315)
            ·
              refine ⟨5100495387272071201014473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400330258181380800676315 5100495387272071201014473)
              ·
                refine ⟨3825371540454053400760855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5100495387272071201014473 3825371540454053400760855)
                ·
                  refine ⟨5738057310681080101141283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3825371540454053400760855 5738057310681080101141283)
                  ·
                    refine ⟨8607085966021620151711925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5738057310681080101141283 8607085966021620151711925)
                    ·
                      refine ⟨806914309314526889222993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8607085966021620151711925 806914309314526889222993)
                      ·
                        rfl

theorem cell23_1571460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 2, 1, 1, 5].length) (baseStart_1571460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571460 prefixEnd_1571460 := by exact prefixLift 1571460
  have htrace : WordTrace (prefixWord ++ tailWord_1571460) baseStart_1571460 baseEnd_1571460 := by
    simpa [prefixWord, tailWord_1571460, baseEnd_1571460] using wordTrace_append hprefix tailTrace_1571460
  have hstable : (prefixWord ++ tailWord_1571460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571460).length < 2 ^ (prefixWord ++ tailWord_1571460).sum := by decide
  have hdescent : baseEnd_1571460 < baseStart_1571460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571474 : List Nat := [3, 2, 3, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_1571474 : Nat := 118140960795 + 1571474 * 2 ^ 59
def prefixEnd_1571474 : Nat := 4983230072969 + 3 ^ 40 * 1571474 * 2
def baseEnd_1571474 : Nat := 806921498043689834447929

theorem tailTrace_1571474 : CollatzResearch.WordTrace tailWord_1571474 prefixEnd_1571474 806921498043689834447929 := by
  unfold tailWord_1571474
  simp only [CollatzResearch.WordTrace]
  refine ⟨14329091377206389809244369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38210910339217039491318317 14329091377206389809244369)
  ·
    refine ⟨10746818532904792356933277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14329091377206389809244369 10746818532904792356933277)
    ·
      refine ⟨4030056949839297133849979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10746818532904792356933277 4030056949839297133849979)
      ·
        refine ⟨6045085424758945700774969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4030056949839297133849979 6045085424758945700774969)
        ·
          refine ⟨4533814068569209275581227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6045085424758945700774969 4533814068569209275581227)
          ·
            refine ⟨6800721102853813913371841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4533814068569209275581227 6800721102853813913371841)
            ·
              refine ⟨5100540827140360435028881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6800721102853813913371841 5100540827140360435028881)
              ·
                refine ⟨3825405620355270326271661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5100540827140360435028881 3825405620355270326271661)
                ·
                  refine ⟨1434527107633226372351873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3825405620355270326271661 1434527107633226372351873)
                  ·
                    refine ⟨1075895330724919779263905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1434527107633226372351873 1075895330724919779263905)
                    ·
                      refine ⟨806921498043689834447929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1075895330724919779263905 806921498043689834447929)
                      ·
                        rfl

theorem cell23_1571474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_1571474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571474 prefixEnd_1571474 := by exact prefixLift 1571474
  have htrace : WordTrace (prefixWord ++ tailWord_1571474) baseStart_1571474 baseEnd_1571474 := by
    simpa [prefixWord, tailWord_1571474, baseEnd_1571474] using wordTrace_append hprefix tailTrace_1571474
  have hstable : (prefixWord ++ tailWord_1571474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571474).length < 2 ^ (prefixWord ++ tailWord_1571474).sum := by decide
  have hdescent : baseEnd_1571474 < baseStart_1571474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571513 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1571513 : Nat := 118140960795 + 1571513 * 2 ^ 59
def prefixEnd_1571513 : Nat := 4983230072969 + 3 ^ 40 * 1571513 * 2
def baseEnd_1571513 : Nat := 806941523789215181860249

theorem tailTrace_1571513 : CollatzResearch.WordTrace tailWord_1571513 prefixEnd_1571513 806941523789215181860249 := by
  unfold tailWord_1571513
  simp only [CollatzResearch.WordTrace]
  refine ⟨57317787955684268897647193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38211858637122845931764795 57317787955684268897647193)
  ·
    refine ⟨42988340966763201673235395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57317787955684268897647193 42988340966763201673235395)
    ·
      refine ⟨64482511450144802509853093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42988340966763201673235395 64482511450144802509853093)
      ·
        refine ⟨12090470896902150470597455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64482511450144802509853093 12090470896902150470597455)
        ·
          refine ⟨18135706345353225705896183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12090470896902150470597455 18135706345353225705896183)
          ·
            refine ⟨27203559518029838558844275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18135706345353225705896183 27203559518029838558844275)
            ·
              refine ⟨40805339277044757838266413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27203559518029838558844275 40805339277044757838266413)
              ·
                refine ⟨15302002228891784189349905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40805339277044757838266413 15302002228891784189349905)
                ·
                  refine ⟨11476501671668838142012429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15302002228891784189349905 11476501671668838142012429)
                  ·
                    refine ⟨4303688126875814303254661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11476501671668838142012429 4303688126875814303254661)
                    ·
                      refine ⟨806941523789215181860249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4303688126875814303254661 806941523789215181860249)
                      ·
                        rfl

theorem cell23_1571513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1571513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571513 prefixEnd_1571513 := by exact prefixLift 1571513
  have htrace : WordTrace (prefixWord ++ tailWord_1571513) baseStart_1571513 baseEnd_1571513 := by
    simpa [prefixWord, tailWord_1571513, baseEnd_1571513] using wordTrace_append hprefix tailTrace_1571513
  have hstable : (prefixWord ++ tailWord_1571513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571513).length < 2 ^ (prefixWord ++ tailWord_1571513).sum := by decide
  have hdescent : baseEnd_1571513 < baseStart_1571513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571524 : List Nat := [2, 3, 3, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_1571524 : Nat := 118140960795 + 1571524 * 2 ^ 59
def prefixEnd_1571524 : Nat := 4983230072969 + 3 ^ 40 * 1571524 * 2
def baseEnd_1571524 : Nat := 806947172076414638822699

theorem tailTrace_1571524 : CollatzResearch.WordTrace tailWord_1571524 prefixEnd_1571524 806947172076414638822699 := by
  unfold tailWord_1571524
  simp only [CollatzResearch.WordTrace]
  refine ⟨28659094579322208888148813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38212126105762945184198417 28659094579322208888148813)
  ·
    refine ⟨10747160467245828333055805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28659094579322208888148813 10747160467245828333055805)
    ·
      refine ⟨4030185175217185624895927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10747160467245828333055805 4030185175217185624895927)
      ·
        refine ⟨6045277762825778437343891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4030185175217185624895927 6045277762825778437343891)
        ·
          refine ⟨9067916644238667656015837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6045277762825778437343891 9067916644238667656015837)
          ·
            refine ⟨3400468741589500371005939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9067916644238667656015837 3400468741589500371005939)
            ·
              refine ⟨5100703112384250556508909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400468741589500371005939 5100703112384250556508909)
              ·
                refine ⟨1912763667144093958690841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5100703112384250556508909 1912763667144093958690841)
                ·
                  refine ⟨1434572750358070469018131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1912763667144093958690841 1434572750358070469018131)
                  ·
                    refine ⟨2151859125537105703527197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1434572750358070469018131 2151859125537105703527197)
                    ·
                      refine ⟨806947172076414638822699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2151859125537105703527197 806947172076414638822699)
                      ·
                        rfl

theorem cell23_1571524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_1571524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571524 prefixEnd_1571524 := by exact prefixLift 1571524
  have htrace : WordTrace (prefixWord ++ tailWord_1571524) baseStart_1571524 baseEnd_1571524 := by
    simpa [prefixWord, tailWord_1571524, baseEnd_1571524] using wordTrace_append hprefix tailTrace_1571524
  have hstable : (prefixWord ++ tailWord_1571524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571524).length < 2 ^ (prefixWord ++ tailWord_1571524).sum := by decide
  have hdescent : baseEnd_1571524 < baseStart_1571524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571534 : List Nat := [4, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2]
def baseStart_1571534 : Nat := 118140960795 + 1571534 * 2 ^ 59
def prefixEnd_1571534 : Nat := 4983230072969 + 3 ^ 40 * 1571534 * 2
def baseEnd_1571534 : Nat := 806952306882959599697653

theorem tailTrace_1571534 : CollatzResearch.WordTrace tailWord_1571534 prefixEnd_1571534 806952306882959599697653 := by
  unfold tailWord_1571534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7164819236076023685520207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38212369259072126322774437 7164819236076023685520207)
  ·
    refine ⟨10747228854114035528280311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7164819236076023685520207 10747228854114035528280311)
    ·
      refine ⟨16120843281171053292420467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10747228854114035528280311 16120843281171053292420467)
      ·
        refine ⟨24181264921756579938630701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16120843281171053292420467 24181264921756579938630701)
        ·
          refine ⟨9067974345658717476986513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24181264921756579938630701 9067974345658717476986513)
          ·
            refine ⟨6800980759244038107739885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9067974345658717476986513 6800980759244038107739885)
            ·
              refine ⟨2550367784716514290402457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6800980759244038107739885 2550367784716514290402457)
              ·
                refine ⟨1912775838537385717801843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2550367784716514290402457 1912775838537385717801843)
                ·
                  refine ⟨2869163757806078576702765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912775838537385717801843 2869163757806078576702765)
                  ·
                    refine ⟨1075936409177279466263537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2869163757806078576702765 1075936409177279466263537)
                    ·
                      refine ⟨806952306882959599697653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1075936409177279466263537 806952306882959599697653)
                      ·
                        rfl

theorem cell23_1571534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 3, 2, 1, 3, 2].length) (baseStart_1571534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571534 prefixEnd_1571534 := by exact prefixLift 1571534
  have htrace : WordTrace (prefixWord ++ tailWord_1571534) baseStart_1571534 baseEnd_1571534 := by
    simpa [prefixWord, tailWord_1571534, baseEnd_1571534] using wordTrace_append hprefix tailTrace_1571534
  have hstable : (prefixWord ++ tailWord_1571534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571534).length < 2 ^ (prefixWord ++ tailWord_1571534).sum := by decide
  have hdescent : baseEnd_1571534 < baseStart_1571534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571580 : List Nat := [2, 2, 2, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_1571580 : Nat := 118140960795 + 1571580 * 2 ^ 59
def prefixEnd_1571580 : Nat := 4983230072969 + 3 ^ 40 * 1571580 * 2
def baseEnd_1571580 : Nat := 806975926993066419722441

theorem tailTrace_1571580 : CollatzResearch.WordTrace tailWord_1571580 prefixEnd_1571580 806975926993066419722441 := by
  unfold tailWord_1571580
  simp only [CollatzResearch.WordTrace]
  refine ⟨28660115823220769670168097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38213487764294359560224129 28660115823220769670168097)
  ·
    refine ⟨21495086867415577252626073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28660115823220769670168097 21495086867415577252626073)
    ·
      refine ⟨16121315150561682939469555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21495086867415577252626073 16121315150561682939469555)
      ·
        refine ⟨24181972725842524409204333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16121315150561682939469555 24181972725842524409204333)
        ·
          refine ⟨9068239772190946653451625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24181972725842524409204333 9068239772190946653451625)
          ·
            refine ⟨6801179829143209990088719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9068239772190946653451625 6801179829143209990088719)
            ·
              refine ⟨10201769743714814985133079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6801179829143209990088719 10201769743714814985133079)
              ·
                refine ⟨15302654615572222477699619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10201769743714814985133079 15302654615572222477699619)
                ·
                  refine ⟨22953981923358333716549429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15302654615572222477699619 22953981923358333716549429)
                  ·
                    refine ⟨2151935805314843785926509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22953981923358333716549429 2151935805314843785926509)
                    ·
                      refine ⟨806975926993066419722441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2151935805314843785926509 806975926993066419722441)
                      ·
                        rfl

theorem cell23_1571580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_1571580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571580 prefixEnd_1571580 := by exact prefixLift 1571580
  have htrace : WordTrace (prefixWord ++ tailWord_1571580) baseStart_1571580 baseEnd_1571580 := by
    simpa [prefixWord, tailWord_1571580, baseEnd_1571580] using wordTrace_append hprefix tailTrace_1571580
  have hstable : (prefixWord ++ tailWord_1571580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571580).length < 2 ^ (prefixWord ++ tailWord_1571580).sum := by decide
  have hdescent : baseEnd_1571580 < baseStart_1571580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571583 : List Nat := [1, 1, 2, 2, 1, 3, 1, 4, 1, 7]
def baseStart_1571583 : Nat := 118140960795 + 1571583 * 2 ^ 59
def prefixEnd_1571583 : Nat := 4983230072969 + 3 ^ 40 * 1571583 * 2
def baseEnd_1571583 : Nat := 268992489145009969328309

theorem tailTrace_1571583 : CollatzResearch.WordTrace tailWord_1571583 prefixEnd_1571583 268992489145009969328309 := by
  unfold tailWord_1571583
  simp only [CollatzResearch.WordTrace]
  refine ⟨57320341065430670852695403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38213560710287113901796935 57320341065430670852695403)
  ·
    refine ⟨85980511598146006279043105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57320341065430670852695403 85980511598146006279043105)
    ·
      refine ⟨64485383698609504709282329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85980511598146006279043105 64485383698609504709282329)
      ·
        refine ⟨48364037773957128531961747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64485383698609504709282329 48364037773957128531961747)
        ·
          refine ⟨72546056660935692797942621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48364037773957128531961747 72546056660935692797942621)
          ·
            refine ⟨27204771247850884799228483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72546056660935692797942621 27204771247850884799228483)
            ·
              refine ⟨40807156871776327198842725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27204771247850884799228483 40807156871776327198842725)
              ·
                refine ⟨7651341913458061349783011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40807156871776327198842725 7651341913458061349783011)
                ·
                  refine ⟨11477012870187092024674517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7651341913458061349783011 11477012870187092024674517)
                  ·
                    refine ⟨268992489145009969328309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11477012870187092024674517 268992489145009969328309)
                    ·
                      rfl

theorem cell23_1571583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 7].length) (baseStart_1571583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571583 prefixEnd_1571583 := by exact prefixLift 1571583
  have htrace : WordTrace (prefixWord ++ tailWord_1571583) baseStart_1571583 baseEnd_1571583 := by
    simpa [prefixWord, tailWord_1571583, baseEnd_1571583] using wordTrace_append hprefix tailTrace_1571583
  have hstable : (prefixWord ++ tailWord_1571583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571583).length < 2 ^ (prefixWord ++ tailWord_1571583).sum := by decide
  have hdescent : baseEnd_1571583 < baseStart_1571583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571593 : List Nat := [1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 7]
def baseStart_1571593 : Nat := 118140960795 + 1571593 * 2 ^ 59
def prefixEnd_1571593 : Nat := 4983230072969 + 3 ^ 40 * 1571593 * 2
def baseEnd_1571593 : Nat := 806982602241574868859881

theorem tailTrace_1571593 : CollatzResearch.WordTrace tailWord_1571593 prefixEnd_1571593 806982602241574868859881 := by
  unfold tailWord_1571593
  simp only [CollatzResearch.WordTrace]
  refine ⟨57320705795394442560559433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38213803863596295040372955 57320705795394442560559433)
  ·
    refine ⟨42990529346545831920419575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57320705795394442560559433 42990529346545831920419575)
    ·
      refine ⟨64485794019818747880629363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42990529346545831920419575 64485794019818747880629363)
      ·
        refine ⟨96728691029728121820944045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64485794019818747880629363 96728691029728121820944045)
        ·
          refine ⟨36273259136148045682854017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96728691029728121820944045 36273259136148045682854017)
          ·
            refine ⟨27204944352111034262140513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36273259136148045682854017 27204944352111034262140513)
            ·
              refine ⟨20403708264083275696605385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27204944352111034262140513 20403708264083275696605385)
              ·
                refine ⟨15302781198062456772454039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20403708264083275696605385 15302781198062456772454039)
                ·
                  refine ⟨22954171797093685158681059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15302781198062456772454039 22954171797093685158681059)
                  ·
                    refine ⟨34431257695640527738021589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22954171797093685158681059 34431257695640527738021589)
                    ·
                      refine ⟨806982602241574868859881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34431257695640527738021589 806982602241574868859881)
                      ·
                        rfl

theorem cell23_1571593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 1, 7].length) (baseStart_1571593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571593 prefixEnd_1571593 := by exact prefixLift 1571593
  have htrace : WordTrace (prefixWord ++ tailWord_1571593) baseStart_1571593 baseEnd_1571593 := by
    simpa [prefixWord, tailWord_1571593, baseEnd_1571593] using wordTrace_append hprefix tailTrace_1571593
  have hstable : (prefixWord ++ tailWord_1571593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571593).length < 2 ^ (prefixWord ++ tailWord_1571593).sum := by decide
  have hdescent : baseEnd_1571593 < baseStart_1571593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571640 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 3, 4, 3]
def baseStart_1571640 : Nat := 118140960795 + 1571640 * 2 ^ 59
def prefixEnd_1571640 : Nat := 4983230072969 + 3 ^ 40 * 1571640 * 2
def baseEnd_1571640 : Nat := 807006735832336184972165

theorem tailTrace_1571640 : CollatzResearch.WordTrace tailWord_1571640 prefixEnd_1571640 807006735832336184972165 := by
  unfold tailWord_1571640
  simp only [CollatzResearch.WordTrace]
  refine ⟨28661210013112084793760187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38214946684149446391680249 28661210013112084793760187)
  ·
    refine ⟨42991815019668127190640281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28661210013112084793760187 42991815019668127190640281)
    ·
      refine ⟨32243861264751095392980211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 42991815019668127190640281 32243861264751095392980211)
      ·
        refine ⟨48365791897126643089470317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32243861264751095392980211 48365791897126643089470317)
        ·
          refine ⟨18137171961422491158551369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48365791897126643089470317 18137171961422491158551369)
          ·
            refine ⟨13602878971066868368913527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18137171961422491158551369 13602878971066868368913527)
            ·
              refine ⟨20404318456600302553370291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13602878971066868368913527 20404318456600302553370291)
              ·
                refine ⟨30606477684900453830055437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20404318456600302553370291 30606477684900453830055437)
                ·
                  refine ⟨11477429131837670186270789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30606477684900453830055437 11477429131837670186270789)
                  ·
                    refine ⟨2152017962219563159925773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11477429131837670186270789 2152017962219563159925773)
                    ·
                      refine ⟨807006735832336184972165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2152017962219563159925773 807006735832336184972165)
                      ·
                        rfl

theorem cell23_1571640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 3, 4, 3].length) (baseStart_1571640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571640 prefixEnd_1571640 := by exact prefixLift 1571640
  have htrace : WordTrace (prefixWord ++ tailWord_1571640) baseStart_1571640 baseEnd_1571640 := by
    simpa [prefixWord, tailWord_1571640, baseEnd_1571640] using wordTrace_append hprefix tailTrace_1571640
  have hstable : (prefixWord ++ tailWord_1571640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571640).length < 2 ^ (prefixWord ++ tailWord_1571640).sum := by decide
  have hdescent : baseEnd_1571640 < baseStart_1571640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571647 : List Nat := [1, 1, 2, 2, 5, 1, 2, 2, 3, 4]
def baseStart_1571647 : Nat := 118140960795 + 1571647 * 2 ^ 59
def prefixEnd_1571647 : Nat := 4983230072969 + 3 ^ 40 * 1571647 * 2
def baseEnd_1571647 : Nat := 269003443398972552528211

theorem tailTrace_1571647 : CollatzResearch.WordTrace tailWord_1571647 prefixEnd_1571647 269003443398972552528211 := by
  unfold tailWord_1571647
  simp only [CollatzResearch.WordTrace]
  refine ⟨57322675337198809783025195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38215116891465873188683463 57322675337198809783025195)
  ·
    refine ⟨85984013005798214674537793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57322675337198809783025195 85984013005798214674537793)
    ·
      refine ⟨64488009754348661005903345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 85984013005798214674537793 64488009754348661005903345)
      ·
        refine ⟨48366007315761495754427509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64488009754348661005903345 48366007315761495754427509)
        ·
          refine ⟨4534313185852640226977579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48366007315761495754427509 4534313185852640226977579)
          ·
            refine ⟨6801469778778960340466369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4534313185852640226977579 6801469778778960340466369)
            ·
              refine ⟨5101102334084220255349777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6801469778778960340466369 5101102334084220255349777)
              ·
                refine ⟨3825826750563165191512333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5101102334084220255349777 3825826750563165191512333)
                ·
                  refine ⟨1434685031461186946817125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3825826750563165191512333 1434685031461186946817125)
                  ·
                    refine ⟨269003443398972552528211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1434685031461186946817125 269003443398972552528211)
                    ·
                      rfl

theorem cell23_1571647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2, 3, 4].length) (baseStart_1571647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571647 prefixEnd_1571647 := by exact prefixLift 1571647
  have htrace : WordTrace (prefixWord ++ tailWord_1571647) baseStart_1571647 baseEnd_1571647 := by
    simpa [prefixWord, tailWord_1571647, baseEnd_1571647] using wordTrace_append hprefix tailTrace_1571647
  have hstable : (prefixWord ++ tailWord_1571647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571647).length < 2 ^ (prefixWord ++ tailWord_1571647).sum := by decide
  have hdescent : baseEnd_1571647 < baseStart_1571647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571660 : List Nat := [2, 2, 1, 3, 3, 1, 1, 2, 8]
def baseStart_1571660 : Nat := 118140960795 + 1571660 * 2 ^ 59
def prefixEnd_1571660 : Nat := 4983230072969 + 3 ^ 40 * 1571660 * 2
def baseEnd_1571660 : Nat := 89668556160602900746897

theorem tailTrace_1571660 : CollatzResearch.WordTrace tailWord_1571660 prefixEnd_1571660 89668556160602900746897 := by
  unfold tailWord_1571660
  simp only [CollatzResearch.WordTrace]
  refine ⟨28661574743075856501624217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38215432990767808668832289 28661574743075856501624217)
  ·
    refine ⟨21496181057306892376218163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28661574743075856501624217 21496181057306892376218163)
    ·
      refine ⟨32244271585960338564327245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21496181057306892376218163 32244271585960338564327245)
      ·
        refine ⟨12091601844735126961622717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32244271585960338564327245 12091601844735126961622717)
        ·
          refine ⟨4534350691775672610608519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12091601844735126961622717 4534350691775672610608519)
          ·
            refine ⟨6801526037663508915912779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4534350691775672610608519 6801526037663508915912779)
            ·
              refine ⟨10202289056495263373869169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6801526037663508915912779 10202289056495263373869169)
              ·
                refine ⟨7651716792371447530401877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10202289056495263373869169 7651716792371447530401877)
                ·
                  refine ⟨89668556160602900746897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7651716792371447530401877 89668556160602900746897)
                  ·
                    rfl

theorem cell23_1571660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 8].length) (baseStart_1571660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571660 prefixEnd_1571660 := by exact prefixLift 1571660
  have htrace : WordTrace (prefixWord ++ tailWord_1571660) baseStart_1571660 baseEnd_1571660 := by
    simpa [prefixWord, tailWord_1571660, baseEnd_1571660] using wordTrace_append hprefix tailTrace_1571660
  have hstable : (prefixWord ++ tailWord_1571660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571660).length < 2 ^ (prefixWord ++ tailWord_1571660).sum := by decide
  have hdescent : baseEnd_1571660 < baseStart_1571660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571664 : List Nat := [2, 1, 1, 1, 1, 4, 5, 3, 1, 4]
def baseStart_1571664 : Nat := 118140960795 + 1571664 * 2 ^ 59
def prefixEnd_1571664 : Nat := 4983230072969 + 3 ^ 40 * 1571664 * 2
def baseEnd_1571664 : Nat := 269006353122681363690685

theorem tailTrace_1571664 : CollatzResearch.WordTrace tailWord_1571664 prefixEnd_1571664 269006353122681363690685 := by
  unfold tailWord_1571664
  simp only [CollatzResearch.WordTrace]
  refine ⟨28661647689068610843197023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38215530252091481124262697 28661647689068610843197023)
  ·
    refine ⟨42992471533602916264795535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28661647689068610843197023 42992471533602916264795535)
    ·
      refine ⟨64488707300404374397193303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42992471533602916264795535 64488707300404374397193303)
      ·
        refine ⟨96733060950606561595789955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64488707300404374397193303 96733060950606561595789955)
        ·
          refine ⟨145099591425909842393684933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96733060950606561595789955 145099591425909842393684933)
          ·
            refine ⟨27206173392358095448815925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145099591425909842393684933 27206173392358095448815925)
            ·
              refine ⟨2550578755533571448326493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27206173392358095448815925 2550578755533571448326493)
              ·
                refine ⟨956467033325089293122435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2550578755533571448326493 956467033325089293122435)
                ·
                  refine ⟨1434700549987633939683653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956467033325089293122435 1434700549987633939683653)
                  ·
                    refine ⟨269006353122681363690685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1434700549987633939683653 269006353122681363690685)
                    ·
                      rfl

theorem cell23_1571664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 5, 3, 1, 4].length) (baseStart_1571664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571664 prefixEnd_1571664 := by exact prefixLift 1571664
  have htrace : WordTrace (prefixWord ++ tailWord_1571664) baseStart_1571664 baseEnd_1571664 := by
    simpa [prefixWord, tailWord_1571664, baseEnd_1571664] using wordTrace_append hprefix tailTrace_1571664
  have hstable : (prefixWord ++ tailWord_1571664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571664).length < 2 ^ (prefixWord ++ tailWord_1571664).sum := by decide
  have hdescent : baseEnd_1571664 < baseStart_1571664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571694 : List Nat := [4, 1, 2, 3, 2, 1, 1, 3, 6]
def baseStart_1571694 : Nat := 118140960795 + 1571694 * 2 ^ 59
def prefixEnd_1571694 : Nat := 4983230072969 + 3 ^ 40 * 1571694 * 2
def baseEnd_1571694 : Nat := 89670495976408774855213

theorem tailTrace_1571694 : CollatzResearch.WordTrace tailWord_1571694 prefixEnd_1571694 89670495976408774855213 := by
  unfold tailWord_1571694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7165548696003567101248267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38216259712019024539990757 7165548696003567101248267)
  ·
    refine ⟨10748323044005350651872401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7165548696003567101248267 10748323044005350651872401)
    ·
      refine ⟨8061242283004012988904301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10748323044005350651872401 8061242283004012988904301)
      ·
        refine ⟨3022965856126504870839113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8061242283004012988904301 3022965856126504870839113)
        ·
          refine ⟨2267224392094878653129335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3022965856126504870839113 2267224392094878653129335)
          ·
            refine ⟨3400836588142317979694003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267224392094878653129335 3400836588142317979694003)
            ·
              refine ⟨5101254882213476969541005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400836588142317979694003 5101254882213476969541005)
              ·
                refine ⟨1912970580830053863577877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5101254882213476969541005 1912970580830053863577877)
                ·
                  refine ⟨89670495976408774855213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1912970580830053863577877 89670495976408774855213)
                  ·
                    rfl

theorem cell23_1571694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 1, 1, 3, 6].length) (baseStart_1571694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571694 prefixEnd_1571694 := by exact prefixLift 1571694
  have htrace : WordTrace (prefixWord ++ tailWord_1571694) baseStart_1571694 baseEnd_1571694 := by
    simpa [prefixWord, tailWord_1571694, baseEnd_1571694] using wordTrace_append hprefix tailTrace_1571694
  have hstable : (prefixWord ++ tailWord_1571694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571694).length < 2 ^ (prefixWord ++ tailWord_1571694).sum := by decide
  have hdescent : baseEnd_1571694 < baseStart_1571694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571707 : List Nat := [1, 1, 1, 1, 1, 5, 5, 2, 1, 5]
def baseStart_1571707 : Nat := 118140960795 + 1571707 * 2 ^ 59
def prefixEnd_1571707 : Nat := 4983230072969 + 3 ^ 40 * 1571707 * 2
def baseEnd_1571707 : Nat := 269013713012062474278119

theorem tailTrace_1571707 : CollatzResearch.WordTrace tailWord_1571707 prefixEnd_1571707 269013713012062474278119 := by
  unfold tailWord_1571707
  simp only [CollatzResearch.WordTrace]
  refine ⟨57324863716981440030209375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38216575811320960020139583 57324863716981440030209375)
  ·
    refine ⟨85987295575472160045314063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57324863716981440030209375 85987295575472160045314063)
    ·
      refine ⟨128980943363208240067971095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85987295575472160045314063 128980943363208240067971095)
      ·
        refine ⟨193471415044812360101956643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128980943363208240067971095 193471415044812360101956643)
        ·
          refine ⟨290207122567218540152934965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193471415044812360101956643 290207122567218540152934965)
          ·
            refine ⟨27206917740676738139337653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 290207122567218540152934965 27206917740676738139337653)
            ·
              refine ⟨2550648538188444200562905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27206917740676738139337653 2550648538188444200562905)
              ·
                refine ⟨1912986403641333150422179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2550648538188444200562905 1912986403641333150422179)
                ·
                  refine ⟨2869479605461999725633269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1912986403641333150422179 2869479605461999725633269)
                  ·
                    refine ⟨269013713012062474278119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2869479605461999725633269 269013713012062474278119)
                    ·
                      rfl

theorem cell23_1571707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 5, 2, 1, 5].length) (baseStart_1571707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571707 prefixEnd_1571707 := by exact prefixLift 1571707
  have htrace : WordTrace (prefixWord ++ tailWord_1571707) baseStart_1571707 baseEnd_1571707 := by
    simpa [prefixWord, tailWord_1571707, baseEnd_1571707] using wordTrace_append hprefix tailTrace_1571707
  have hstable : (prefixWord ++ tailWord_1571707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571707).length < 2 ^ (prefixWord ++ tailWord_1571707).sum := by decide
  have hdescent : baseEnd_1571707 < baseStart_1571707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571738 : List Nat := [3, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3]
def baseStart_1571738 : Nat := 118140960795 + 1571738 * 2 ^ 59
def prefixEnd_1571738 : Nat := 4983230072969 + 3 ^ 40 * 1571738 * 2
def baseEnd_1571738 : Nat := 807057056936476801546715

theorem tailTrace_1571738 : CollatzResearch.WordTrace tailWord_1571738 prefixEnd_1571738 807057056936476801546715 := by
  unfold tailWord_1571738
  simp only [CollatzResearch.WordTrace]
  refine ⟨14331498594967283081146967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38217329586579421549725245 14331498594967283081146967)
  ·
    refine ⟨21497247892450924621720451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14331498594967283081146967 21497247892450924621720451)
    ·
      refine ⟨32245871838676386932580677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21497247892450924621720451 32245871838676386932580677)
      ·
        refine ⟨6046100969751822549858877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32245871838676386932580677 6046100969751822549858877)
        ·
          refine ⟨2267287863656933456197079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6046100969751822549858877 2267287863656933456197079)
          ·
            refine ⟨3400931795485400184295619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267287863656933456197079 3400931795485400184295619)
            ·
              refine ⟨5101397693228100276443429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400931795485400184295619 5101397693228100276443429)
              ·
                refine ⟨956512067480268801833143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5101397693228100276443429 956512067480268801833143)
                ·
                  refine ⟨1434768101220403202749715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956512067480268801833143 1434768101220403202749715)
                  ·
                    refine ⟨2152152151830604804124573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1434768101220403202749715 2152152151830604804124573)
                    ·
                      refine ⟨807057056936476801546715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2152152151830604804124573 807057056936476801546715)
                      ·
                        rfl

theorem cell23_1571738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_1571738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571738 prefixEnd_1571738 := by exact prefixLift 1571738
  have htrace : WordTrace (prefixWord ++ tailWord_1571738) baseStart_1571738 baseEnd_1571738 := by
    simpa [prefixWord, tailWord_1571738, baseEnd_1571738] using wordTrace_append hprefix tailTrace_1571738
  have hstable : (prefixWord ++ tailWord_1571738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571738).length < 2 ^ (prefixWord ++ tailWord_1571738).sum := by decide
  have hdescent : baseEnd_1571738 < baseStart_1571738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571747 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 3]
def baseStart_1571747 : Nat := 118140960795 + 1571747 * 2 ^ 59
def prefixEnd_1571747 : Nat := 4983230072969 + 3 ^ 40 * 1571747 * 2
def baseEnd_1571747 : Nat := 807061678262367266334173

theorem tailTrace_1571747 : CollatzResearch.WordTrace tailWord_1571747 prefixEnd_1571747 807061678262367266334173 := by
  unfold tailWord_1571747
  simp only [CollatzResearch.WordTrace]
  refine ⟨57326322636836526861665495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38217548424557684574443663 57326322636836526861665495)
  ·
    refine ⟨85989483955254790292498243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57326322636836526861665495 85989483955254790292498243)
    ·
      refine ⟨128984225932882185438747365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85989483955254790292498243 128984225932882185438747365)
      ·
        refine ⟨24184542362415409769765131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 128984225932882185438747365 24184542362415409769765131)
        ·
          refine ⟨36276813543623114654647697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24184542362415409769765131 36276813543623114654647697)
          ·
            refine ⟨27207610157717335990985773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36276813543623114654647697 27207610157717335990985773)
            ·
              refine ⟨10202853809144000996619665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27207610157717335990985773 10202853809144000996619665)
              ·
                refine ⟨7652140356858000747464749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10202853809144000996619665 7652140356858000747464749)
                ·
                  refine ⟨2869552633821750280299281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7652140356858000747464749 2869552633821750280299281)
                  ·
                    refine ⟨2152164475366312710224461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2869552633821750280299281 2152164475366312710224461)
                    ·
                      refine ⟨807061678262367266334173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2152164475366312710224461 807061678262367266334173)
                      ·
                        rfl

theorem cell23_1571747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 3].length) (baseStart_1571747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571747 prefixEnd_1571747 := by exact prefixLift 1571747
  have htrace : WordTrace (prefixWord ++ tailWord_1571747) baseStart_1571747 baseEnd_1571747 := by
    simpa [prefixWord, tailWord_1571747, baseEnd_1571747] using wordTrace_append hprefix tailTrace_1571747
  have hstable : (prefixWord ++ tailWord_1571747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571747).length < 2 ^ (prefixWord ++ tailWord_1571747).sum := by decide
  have hdescent : baseEnd_1571747 < baseStart_1571747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571829 : List Nat := [1, 3, 5, 2, 1, 2, 1, 3, 1, 2, 2]
def baseStart_1571829 : Nat := 118140960795 + 1571829 * 2 ^ 59
def prefixEnd_1571829 : Nat := 4983230072969 + 3 ^ 40 * 1571829 * 2
def baseEnd_1571829 : Nat := 807103783676035945508797

theorem tailTrace_1571829 : CollatzResearch.WordTrace tailWord_1571829 prefixEnd_1571829 807103783676035945508797 := by
  unfold tailWord_1571829
  simp only [CollatzResearch.WordTrace]
  refine ⟨57329313422539454866150541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38219542281692969910767027 57329313422539454866150541)
  ·
    refine ⟨21498492533452295574806453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57329313422539454866150541 21498492533452295574806453)
    ·
      refine ⟨2015483675011152710138105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21498492533452295574806453 2015483675011152710138105)
      ·
        refine ⟨1511612756258364532603579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2015483675011152710138105 1511612756258364532603579)
        ·
          refine ⟨2267419134387546798905369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511612756258364532603579 2267419134387546798905369)
          ·
            refine ⟨1700564350790660099179027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2267419134387546798905369 1700564350790660099179027)
            ·
              refine ⟨2550846526185990148768541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700564350790660099179027 2550846526185990148768541)
              ·
                refine ⟨956567447319746305788203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2550846526185990148768541 956567447319746305788203)
                ·
                  refine ⟨1434851170979619458682305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956567447319746305788203 1434851170979619458682305)
                  ·
                    refine ⟨1076138378234714594011729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1434851170979619458682305 1076138378234714594011729)
                    ·
                      refine ⟨807103783676035945508797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076138378234714594011729 807103783676035945508797)
                      ·
                        rfl

theorem cell23_1571829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_1571829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571829 prefixEnd_1571829 := by exact prefixLift 1571829
  have htrace : WordTrace (prefixWord ++ tailWord_1571829) baseStart_1571829 baseEnd_1571829 := by
    simpa [prefixWord, tailWord_1571829, baseEnd_1571829] using wordTrace_append hprefix tailTrace_1571829
  have hstable : (prefixWord ++ tailWord_1571829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571829).length < 2 ^ (prefixWord ++ tailWord_1571829).sum := by decide
  have hdescent : baseEnd_1571829 < baseStart_1571829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571834 : List Nat := [3, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2]
def baseStart_1571834 : Nat := 118140960795 + 1571834 * 2 ^ 59
def prefixEnd_1571834 : Nat := 4983230072969 + 3 ^ 40 * 1571834 * 2
def baseEnd_1571834 : Nat := 807106351079308425946273

theorem tailTrace_1571834 : CollatzResearch.WordTrace tailWord_1571834 prefixEnd_1571834 807106351079308425946273 := by
  unfold tailWord_1571834
  simp only [CollatzResearch.WordTrace]
  refine ⟨14332373946880335180020639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38219663858347560480055037 14332373946880335180020639)
  ·
    refine ⟨21498560920320502770030959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14332373946880335180020639 21498560920320502770030959)
    ·
      refine ⟨32247841380480754155046439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21498560920320502770030959 32247841380480754155046439)
      ·
        refine ⟨48371762070721131232569659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32247841380480754155046439 48371762070721131232569659)
        ·
          refine ⟨72557643106081696848854489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48371762070721131232569659 72557643106081696848854489)
          ·
            refine ⟨54418232329561272636640867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72557643106081696848854489 54418232329561272636640867)
            ·
              refine ⟨81627348494341908954961301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54418232329561272636640867 81627348494341908954961301)
              ·
                refine ⟨3826281960672276982263811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81627348494341908954961301 3826281960672276982263811)
                ·
                  refine ⟨5739422941008415473395717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3826281960672276982263811 5739422941008415473395717)
                  ·
                    refine ⟨1076141801439077901261697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5739422941008415473395717 1076141801439077901261697)
                    ·
                      refine ⟨807106351079308425946273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076141801439077901261697 807106351079308425946273)
                      ·
                        rfl

theorem cell23_1571834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 6, 1, 4, 2].length) (baseStart_1571834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571834 prefixEnd_1571834 := by exact prefixLift 1571834
  have htrace : WordTrace (prefixWord ++ tailWord_1571834) baseStart_1571834 baseEnd_1571834 := by
    simpa [prefixWord, tailWord_1571834, baseEnd_1571834] using wordTrace_append hprefix tailTrace_1571834
  have hstable : (prefixWord ++ tailWord_1571834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571834).length < 2 ^ (prefixWord ++ tailWord_1571834).sum := by decide
  have hdescent : baseEnd_1571834 < baseStart_1571834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571837 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 1, 6, 3]
def baseStart_1571837 : Nat := 118140960795 + 1571837 * 2 ^ 59
def prefixEnd_1571837 : Nat := 4983230072969 + 3 ^ 40 * 1571837 * 2
def baseEnd_1571837 : Nat := 807107891521271914208759

theorem tailTrace_1571837 : CollatzResearch.WordTrace tailWord_1571837 prefixEnd_1571837 807107891521271914208759 := by
  unfold tailWord_1571837
  simp only [CollatzResearch.WordTrace]
  refine ⟨57329605206510472232441765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38219736804340314821627843 57329605206510472232441765)
  ·
    refine ⟨10749300976220713543582831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57329605206510472232441765 10749300976220713543582831)
    ·
      refine ⟨16123951464331070315374247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10749300976220713543582831 16123951464331070315374247)
      ·
        refine ⟨24185927196496605473061371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16123951464331070315374247 24185927196496605473061371)
        ·
          refine ⟨36278890794744908209592057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24185927196496605473061371 36278890794744908209592057)
          ·
            refine ⟨27209168096058681157194043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36278890794744908209592057 27209168096058681157194043)
            ·
              refine ⟨40813752144088021735791065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27209168096058681157194043 40813752144088021735791065)
              ·
                refine ⟨30610314108066016301843299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40813752144088021735791065 30610314108066016301843299)
                ·
                  refine ⟨45915471162099024452764949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30610314108066016301843299 45915471162099024452764949)
                  ·
                    refine ⟨2152287710723391771223357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 45915471162099024452764949 2152287710723391771223357)
                    ·
                      refine ⟨807107891521271914208759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2152287710723391771223357 807107891521271914208759)
                      ·
                        rfl

theorem cell23_1571837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 6, 3].length) (baseStart_1571837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571837 prefixEnd_1571837 := by exact prefixLift 1571837
  have htrace : WordTrace (prefixWord ++ tailWord_1571837) baseStart_1571837 baseEnd_1571837 := by
    simpa [prefixWord, tailWord_1571837, baseEnd_1571837] using wordTrace_append hprefix tailTrace_1571837
  have hstable : (prefixWord ++ tailWord_1571837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571837).length < 2 ^ (prefixWord ++ tailWord_1571837).sum := by decide
  have hdescent : baseEnd_1571837 < baseStart_1571837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571851 : List Nat := [1, 1, 1, 1, 6, 2, 2, 1, 4, 2, 2]
def baseStart_1571851 : Nat := 118140960795 + 1571851 * 2 ^ 59
def prefixEnd_1571851 : Nat := 4983230072969 + 3 ^ 40 * 1571851 * 2
def baseEnd_1571851 : Nat := 807115080250434859433695

theorem tailTrace_1571851 : CollatzResearch.WordTrace tailWord_1571851 prefixEnd_1571851 807115080250434859433695 := by
  unfold tailWord_1571851
  simp only [CollatzResearch.WordTrace]
  refine ⟨57330115828459752623451407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38220077218973168415634271 57330115828459752623451407)
  ·
    refine ⟨85995173742689628935177111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57330115828459752623451407 85995173742689628935177111)
    ·
      refine ⟨128992760614034443402765667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85995173742689628935177111 128992760614034443402765667)
      ·
        refine ⟨193489140921051665104148501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128992760614034443402765667 193489140921051665104148501)
        ·
          refine ⟨9069803480674296801756961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193489140921051665104148501 9069803480674296801756961)
          ·
            refine ⟨6802352610505722601317721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9069803480674296801756961 6802352610505722601317721)
            ·
              refine ⟨5101764457879291950988291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6802352610505722601317721 5101764457879291950988291)
              ·
                refine ⟨7652646686818937926482437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5101764457879291950988291 7652646686818937926482437)
                ·
                  refine ⟨1434871253778550861215457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7652646686818937926482437 1434871253778550861215457)
                  ·
                    refine ⟨1076153440333913145911593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1434871253778550861215457 1076153440333913145911593)
                    ·
                      refine ⟨807115080250434859433695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076153440333913145911593 807115080250434859433695)
                      ·
                        rfl

theorem cell23_1571851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 2, 1, 4, 2, 2].length) (baseStart_1571851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571851 prefixEnd_1571851 := by exact prefixLift 1571851
  have htrace : WordTrace (prefixWord ++ tailWord_1571851) baseStart_1571851 baseEnd_1571851 := by
    simpa [prefixWord, tailWord_1571851, baseEnd_1571851] using wordTrace_append hprefix tailTrace_1571851
  have hstable : (prefixWord ++ tailWord_1571851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571851).length < 2 ^ (prefixWord ++ tailWord_1571851).sum := by decide
  have hdescent : baseEnd_1571851 < baseStart_1571851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571867 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 3]
def baseStart_1571867 : Nat := 118140960795 + 1571867 * 2 ^ 59
def prefixEnd_1571867 : Nat := 4983230072969 + 3 ^ 40 * 1571867 * 2
def baseEnd_1571867 : Nat := 807123295940906796833621

theorem tailTrace_1571867 : CollatzResearch.WordTrace tailWord_1571867 prefixEnd_1571867 807123295940906796833621 := by
  unfold tailWord_1571867
  simp only [CollatzResearch.WordTrace]
  refine ⟨57330699396401787356033855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38220466264267858237355903 57330699396401787356033855)
  ·
    refine ⟨85996049094602681034050783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57330699396401787356033855 85996049094602681034050783)
    ·
      refine ⟨128994073641904021551076175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 85996049094602681034050783 128994073641904021551076175)
      ·
        refine ⟨193491110462856032326614263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 128994073641904021551076175 193491110462856032326614263)
        ·
          refine ⟨290236665694284048489921395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193491110462856032326614263 290236665694284048489921395)
          ·
            refine ⟨435354998541426072734882093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290236665694284048489921395 435354998541426072734882093)
            ·
              refine ⟨163258124453034777275580785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 435354998541426072734882093 163258124453034777275580785)
              ·
                refine ⟨122443593339776082956685589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163258124453034777275580785 122443593339776082956685589)
                ·
                  refine ⟨5739543437802003888594637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122443593339776082956685589 5739543437802003888594637)
                  ·
                    refine ⟨2152328789175751458222989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5739543437802003888594637 2152328789175751458222989)
                    ·
                      refine ⟨807123295940906796833621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2152328789175751458222989 807123295940906796833621)
                      ·
                        rfl

theorem cell23_1571867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 3].length) (baseStart_1571867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571867 prefixEnd_1571867 := by exact prefixLift 1571867
  have htrace : WordTrace (prefixWord ++ tailWord_1571867) baseStart_1571867 baseEnd_1571867 := by
    simpa [prefixWord, tailWord_1571867, baseEnd_1571867] using wordTrace_append hprefix tailTrace_1571867
  have hstable : (prefixWord ++ tailWord_1571867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571867).length < 2 ^ (prefixWord ++ tailWord_1571867).sum := by decide
  have hdescent : baseEnd_1571867 < baseStart_1571867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571872 : List Nat := [2, 1, 1, 7, 2, 1, 1, 2, 1, 3, 2]
def baseStart_1571872 : Nat := 118140960795 + 1571872 * 2 ^ 59
def prefixEnd_1571872 : Nat := 4983230072969 + 3 ^ 40 * 1571872 * 2
def baseEnd_1571872 : Nat := 807125863344179277271099

theorem tailTrace_1571872 : CollatzResearch.WordTrace tailWord_1571872 prefixEnd_1571872 807125863344179277271099 := by
  unfold tailWord_1571872
  simp only [CollatzResearch.WordTrace]
  refine ⟨28665440880691836604982935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38220587840922448806643913 28665440880691836604982935)
  ·
    refine ⟨42998161321037754907474403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28665440880691836604982935 42998161321037754907474403)
    ·
      refine ⟨64497241981556632361211605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 42998161321037754907474403 64497241981556632361211605)
      ·
        refine ⟨1511654108942733570965897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 64497241981556632361211605 1511654108942733570965897)
        ·
          refine ⟨1133740581707050178224423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1511654108942733570965897 1133740581707050178224423)
          ·
            refine ⟨1700610872560575267336635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133740581707050178224423 1700610872560575267336635)
            ·
              refine ⟨2550916308840862901004953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700610872560575267336635 2550916308840862901004953)
              ·
                refine ⟨1913187231630647175753715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2550916308840862901004953 1913187231630647175753715)
                ·
                  refine ⟨2869780847445970763630573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1913187231630647175753715 2869780847445970763630573)
                  ·
                    refine ⟨1076167817792239036361465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2869780847445970763630573 1076167817792239036361465)
                    ·
                      refine ⟨807125863344179277271099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076167817792239036361465 807125863344179277271099)
                      ·
                        rfl

theorem cell23_1571872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 1, 2, 1, 3, 2].length) (baseStart_1571872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571872 prefixEnd_1571872 := by exact prefixLift 1571872
  have htrace : WordTrace (prefixWord ++ tailWord_1571872) baseStart_1571872 baseEnd_1571872 := by
    simpa [prefixWord, tailWord_1571872, baseEnd_1571872] using wordTrace_append hprefix tailTrace_1571872
  have hstable : (prefixWord ++ tailWord_1571872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571872).length < 2 ^ (prefixWord ++ tailWord_1571872).sum := by decide
  have hdescent : baseEnd_1571872 < baseStart_1571872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571924 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_1571924 : Nat := 118140960795 + 1571924 * 2 ^ 59
def prefixEnd_1571924 : Nat := 4983230072969 + 3 ^ 40 * 1571924 * 2
def baseEnd_1571924 : Nat := 807152564338213073820859

theorem tailTrace_1571924 : CollatzResearch.WordTrace tailWord_1571924 prefixEnd_1571924 807152564338213073820859 := by
  unfold tailWord_1571924
  simp only [CollatzResearch.WordTrace]
  refine ⟨28666389178597643045429413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38221852238130190727239217 28666389178597643045429413)
  ·
    refine ⟨5374947970987058071018015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28666389178597643045429413 5374947970987058071018015)
    ·
      refine ⟨8062421956480587106527023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5374947970987058071018015 8062421956480587106527023)
      ·
        refine ⟨12093632934720880659790535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8062421956480587106527023 12093632934720880659790535)
        ·
          refine ⟨18140449402081320989685803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12093632934720880659790535 18140449402081320989685803)
          ·
            refine ⟨27210674103121981484528705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18140449402081320989685803 27210674103121981484528705)
            ·
              refine ⟨20408005577341486113396529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27210674103121981484528705 20408005577341486113396529)
              ·
                refine ⟨15306004183006114585047397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20408005577341486113396529 15306004183006114585047397)
                ·
                  refine ⟨2869875784313646484696387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15306004183006114585047397 2869875784313646484696387)
                  ·
                    refine ⟨4304813676470469727044581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2869875784313646484696387 4304813676470469727044581)
                    ·
                      refine ⟨807152564338213073820859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4304813676470469727044581 807152564338213073820859)
                      ·
                        rfl

theorem cell23_1571924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_1571924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571924 prefixEnd_1571924 := by exact prefixLift 1571924
  have htrace : WordTrace (prefixWord ++ tailWord_1571924) baseStart_1571924 baseEnd_1571924 := by
    simpa [prefixWord, tailWord_1571924, baseEnd_1571924] using wordTrace_append hprefix tailTrace_1571924
  have hstable : (prefixWord ++ tailWord_1571924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571924).length < 2 ^ (prefixWord ++ tailWord_1571924).sum := by decide
  have hdescent : baseEnd_1571924 < baseStart_1571924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571938 : List Nat := [3, 3, 2, 2, 1, 3, 1, 1, 2, 5]
def baseStart_1571938 : Nat := 118140960795 + 1571938 * 2 ^ 59
def prefixEnd_1571938 : Nat := 4983230072969 + 3 ^ 40 * 1571938 * 2
def baseEnd_1571938 : Nat := 269053251022458673015265

theorem tailTrace_1571938 : CollatzResearch.WordTrace tailWord_1571938 prefixEnd_1571938 269053251022458673015265 := by
  unfold tailWord_1571938
  simp only [CollatzResearch.WordTrace]
  refine ⟨14333322244786141620467117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38222192652763044321245645 14333322244786141620467117)
  ·
    refine ⟨5374995841794803107675169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14333322244786141620467117 5374995841794803107675169)
    ·
      refine ⟨4031246881346102330756377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5374995841794803107675169 4031246881346102330756377)
      ·
        refine ⟨3023435161009576748067283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4031246881346102330756377 3023435161009576748067283)
        ·
          refine ⟨4535152741514365122100925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3023435161009576748067283 4535152741514365122100925)
          ·
            refine ⟨1700682278067886920787847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4535152741514365122100925 1700682278067886920787847)
            ·
              refine ⟨2551023417101830381181771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700682278067886920787847 2551023417101830381181771)
              ·
                refine ⟨3826535125652745571772657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2551023417101830381181771 3826535125652745571772657)
                ·
                  refine ⟨2869901344239559178829493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3826535125652745571772657 2869901344239559178829493)
                  ·
                    refine ⟨269053251022458673015265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2869901344239559178829493 269053251022458673015265)
                    ·
                      rfl

theorem cell23_1571938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_1571938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571938 prefixEnd_1571938 := by exact prefixLift 1571938
  have htrace : WordTrace (prefixWord ++ tailWord_1571938) baseStart_1571938 baseEnd_1571938 := by
    simpa [prefixWord, tailWord_1571938, baseEnd_1571938] using wordTrace_append hprefix tailTrace_1571938
  have hstable : (prefixWord ++ tailWord_1571938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571938).length < 2 ^ (prefixWord ++ tailWord_1571938).sum := by decide
  have hdescent : baseEnd_1571938 < baseStart_1571938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1571987 : List Nat := [1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 7]
def baseStart_1571987 : Nat := 118140960795 + 1571987 * 2 ^ 59
def prefixEnd_1571987 : Nat := 4983230072969 + 3 ^ 40 * 1571987 * 2
def baseEnd_1571987 : Nat := 807184913619446327333069

theorem tailTrace_1571987 : CollatzResearch.WordTrace tailWord_1571987 prefixEnd_1571987 807184913619446327333069 := by
  unfold tailWord_1571987
  simp only [CollatzResearch.WordTrace]
  refine ⟨57335076155967047850402215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38223384103978031900268143 57335076155967047850402215)
  ·
    refine ⟨86002614233950571775603323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57335076155967047850402215 86002614233950571775603323)
    ·
      refine ⟨129003921350925857663404985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86002614233950571775603323 129003921350925857663404985)
      ·
        refine ⟨96752941013194393247553739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129003921350925857663404985 96752941013194393247553739)
        ·
          refine ⟨145129411519791589871330609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96752941013194393247553739 145129411519791589871330609)
          ·
            refine ⟨108847058639843692403497957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145129411519791589871330609 108847058639843692403497957)
            ·
              refine ⟨20408823494970692325655867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108847058639843692403497957 20408823494970692325655867)
              ·
                refine ⟨30613235242456038488483801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20408823494970692325655867 30613235242456038488483801)
                ·
                  refine ⟨22959926431842028866362851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30613235242456038488483801 22959926431842028866362851)
                  ·
                    refine ⟨34439889647763043299544277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22959926431842028866362851 34439889647763043299544277)
                    ·
                      refine ⟨807184913619446327333069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34439889647763043299544277 807184913619446327333069)
                      ·
                        rfl

theorem cell23_1571987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 7].length) (baseStart_1571987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1571987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1571987 prefixEnd_1571987 := by exact prefixLift 1571987
  have htrace : WordTrace (prefixWord ++ tailWord_1571987) baseStart_1571987 baseEnd_1571987 := by
    simpa [prefixWord, tailWord_1571987, baseEnd_1571987] using wordTrace_append hprefix tailTrace_1571987
  have hstable : (prefixWord ++ tailWord_1571987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1571987).length < 2 ^ (prefixWord ++ tailWord_1571987).sum := by decide
  have hdescent : baseEnd_1571987 < baseStart_1571987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1571987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572001 : List Nat := [1, 2, 3, 3, 1, 1, 1, 3, 1, 5, 2]
def baseStart_1572001 : Nat := 118140960795 + 1572001 * 2 ^ 59
def prefixEnd_1572001 : Nat := 4983230072969 + 3 ^ 40 * 1572001 * 2
def baseEnd_1572001 : Nat := 807192102348609272558005

theorem tailTrace_1572001 : CollatzResearch.WordTrace tailWord_1572001 prefixEnd_1572001 807192102348609272558005 := by
  unfold tailWord_1572001
  simp only [CollatzResearch.WordTrace]
  refine ⟨57335586777916328241411857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38223724518610885494274571 57335586777916328241411857)
  ·
    refine ⟨43001690083437246181058893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57335586777916328241411857 43001690083437246181058893)
    ·
      refine ⟨16125633781288967317897085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 43001690083437246181058893 16125633781288967317897085)
      ·
        refine ⟨6047112667983362744211407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16125633781288967317897085 6047112667983362744211407)
        ·
          refine ⟨9070669001975044116317111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047112667983362744211407 9070669001975044116317111)
          ·
            refine ⟨13606003502962566174475667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9070669001975044116317111 13606003502962566174475667)
            ·
              refine ⟨20409005254443849261713501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13606003502962566174475667 20409005254443849261713501)
              ·
                refine ⟨7653376970416443473142563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20409005254443849261713501 7653376970416443473142563)
                ·
                  refine ⟨11480065455624665209713845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7653376970416443473142563 11480065455624665209713845)
                  ·
                    refine ⟨1076256136464812363410673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11480065455624665209713845 1076256136464812363410673)
                    ·
                      refine ⟨807192102348609272558005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076256136464812363410673 807192102348609272558005)
                      ·
                        rfl

theorem cell23_1572001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_1572001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572001 prefixEnd_1572001 := by exact prefixLift 1572001
  have htrace : WordTrace (prefixWord ++ tailWord_1572001) baseStart_1572001 baseEnd_1572001 := by
    simpa [prefixWord, tailWord_1572001, baseEnd_1572001] using wordTrace_append hprefix tailTrace_1572001
  have hstable : (prefixWord ++ tailWord_1572001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572001).length < 2 ^ (prefixWord ++ tailWord_1572001).sum := by decide
  have hdescent : baseEnd_1572001 < baseStart_1572001 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572002 : List Nat := [3, 3, 1, 3, 2, 2, 1, 3, 1, 4]
def baseStart_1572002 : Nat := 118140960795 + 1572002 * 2 ^ 59
def prefixEnd_1572002 : Nat := 4983230072969 + 3 ^ 40 * 1572002 * 2
def baseEnd_1572002 : Nat := 269064205276421256215167

theorem tailTrace_1572002 : CollatzResearch.WordTrace tailWord_1572002 prefixEnd_1572002 269064205276421256215167 := by
  unfold tailWord_1572002
  simp only [CollatzResearch.WordTrace]
  refine ⟨14333905812728176353049565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38223748833941803608132173 14333905812728176353049565)
  ·
    refine ⟨5375214679773066132393587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14333905812728176353049565 5375214679773066132393587)
    ·
      refine ⟨8062822019659599198590381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5375214679773066132393587 8062822019659599198590381)
      ·
        refine ⟨3023558257372349699471393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8062822019659599198590381 3023558257372349699471393)
        ·
          refine ⟨2267668693029262274603545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3023558257372349699471393 2267668693029262274603545)
          ·
            refine ⟨1700751519771946705952659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2267668693029262274603545 1700751519771946705952659)
            ·
              refine ⟨2551127279657920058928989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1700751519771946705952659 2551127279657920058928989)
              ·
                refine ⟨956672729871720022098371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2551127279657920058928989 956672729871720022098371)
                ·
                  refine ⟨1435009094807580033147557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956672729871720022098371 1435009094807580033147557)
                  ·
                    refine ⟨269064205276421256215167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1435009094807580033147557 269064205276421256215167)
                    ·
                      rfl

theorem cell23_1572002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_1572002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572002 prefixEnd_1572002 := by exact prefixLift 1572002
  have htrace : WordTrace (prefixWord ++ tailWord_1572002) baseStart_1572002 baseEnd_1572002 := by
    simpa [prefixWord, tailWord_1572002, baseEnd_1572002] using wordTrace_append hprefix tailTrace_1572002
  have hstable : (prefixWord ++ tailWord_1572002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572002).length < 2 ^ (prefixWord ++ tailWord_1572002).sum := by decide
  have hdescent : baseEnd_1572002 < baseStart_1572002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572018 : List Nat := [3, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2]
def baseStart_1572018 : Nat := 118140960795 + 1572018 * 2 ^ 59
def prefixEnd_1572018 : Nat := 4983230072969 + 3 ^ 40 * 1572018 * 2
def baseEnd_1572018 : Nat := 807200831519735706045427

theorem tailTrace_1572018 : CollatzResearch.WordTrace tailWord_1572018 prefixEnd_1572018 807200831519735706045427 := by
  unfold tailWord_1572018
  simp only [CollatzResearch.WordTrace]
  refine ⟨14334051704713685036195177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38224137879236493429853805 14334051704713685036195177)
  ·
    refine ⟨10750538778535263777146383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14334051704713685036195177 10750538778535263777146383)
    ·
      refine ⟨16125808167802895665719575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10750538778535263777146383 16125808167802895665719575)
      ·
        refine ⟨24188712251704343498579363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16125808167802895665719575 24188712251704343498579363)
        ·
          refine ⟨36283068377556515247869045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24188712251704343498579363 36283068377556515247869045)
          ·
            refine ⟨3401537660395923304487723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36283068377556515247869045 3401537660395923304487723)
            ·
              refine ⟨5102306490593884956731585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3401537660395923304487723 5102306490593884956731585)
              ·
                refine ⟨3826729867945413717548689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5102306490593884956731585 3826729867945413717548689)
                ·
                  refine ⟨2870047400959060288161517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3826729867945413717548689 2870047400959060288161517)
                  ·
                    refine ⟨1076267775359647608060569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2870047400959060288161517 1076267775359647608060569)
                    ·
                      refine ⟨807200831519735706045427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076267775359647608060569 807200831519735706045427)
                      ·
                        rfl

theorem cell23_1572018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_1572018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572018 prefixEnd_1572018 := by exact prefixLift 1572018
  have htrace : WordTrace (prefixWord ++ tailWord_1572018) baseStart_1572018 baseEnd_1572018 := by
    simpa [prefixWord, tailWord_1572018, baseEnd_1572018] using wordTrace_append hprefix tailTrace_1572018
  have hstable : (prefixWord ++ tailWord_1572018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572018).length < 2 ^ (prefixWord ++ tailWord_1572018).sum := by decide
  have hdescent : baseEnd_1572018 < baseStart_1572018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572045 : List Nat := [1, 6, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1572045 : Nat := 118140960795 + 1572045 * 2 ^ 59
def prefixEnd_1572045 : Nat := 4983230072969 + 3 ^ 40 * 1572045 * 2
def baseEnd_1572045 : Nat := 269071565165802366802601

theorem tailTrace_1572045 : CollatzResearch.WordTrace tailWord_1572045 prefixEnd_1572045 269071565165802366802601 := by
  unfold tailWord_1572045
  simp only [CollatzResearch.WordTrace]
  refine ⟨57337191589756923756013589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38224794393171282504009059 57337191589756923756013589)
  ·
    refine ⟨2687680855769855801063137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 57337191589756923756013589 2687680855769855801063137)
    ·
      refine ⟨2015760641827391850797353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2687680855769855801063137 2015760641827391850797353)
      ·
        refine ⟨1511820481370543888098015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2015760641827391850797353 1511820481370543888098015)
        ·
          refine ⟨2267730722055815832147023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511820481370543888098015 2267730722055815832147023)
          ·
            refine ⟨3401596083083723748220535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267730722055815832147023 3401596083083723748220535)
            ·
              refine ⟨5102394124625585622330803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3401596083083723748220535 5102394124625585622330803)
              ·
                refine ⟨7653591186938378433496205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5102394124625585622330803 7653591186938378433496205)
                ·
                  refine ⟨2870096695101891912561077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7653591186938378433496205 2870096695101891912561077)
                  ·
                    refine ⟨269071565165802366802601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2870096695101891912561077 269071565165802366802601)
                    ·
                      rfl

theorem cell23_1572045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1572045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572045 prefixEnd_1572045 := by exact prefixLift 1572045
  have htrace : WordTrace (prefixWord ++ tailWord_1572045) baseStart_1572045 baseEnd_1572045 := by
    simpa [prefixWord, tailWord_1572045, baseEnd_1572045] using wordTrace_append hprefix tailTrace_1572045
  have hstable : (prefixWord ++ tailWord_1572045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572045).length < 2 ^ (prefixWord ++ tailWord_1572045).sum := by decide
  have hdescent : baseEnd_1572045 < baseStart_1572045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572052 : List Nat := [2, 4, 1, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_1572052 : Nat := 118140960795 + 1572052 * 2 ^ 59
def prefixEnd_1572052 : Nat := 4983230072969 + 3 ^ 40 * 1572052 * 2
def baseEnd_1572052 : Nat := 807218289861988573020271

theorem tailTrace_1572052 : CollatzResearch.WordTrace tailWord_1572052 prefixEnd_1572052 807218289861988573020271 := by
  unfold tailWord_1572052
  simp only [CollatzResearch.WordTrace]
  refine ⟨28668723450365781975759205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38224964600487709301012273 28668723450365781975759205)
  ·
    refine ⟨5375385646943584120454851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28668723450365781975759205 5375385646943584120454851)
    ·
      refine ⟨8063078470415376180682277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5375385646943584120454851 8063078470415376180682277)
      ·
        refine ⟨1511827213202883033877927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8063078470415376180682277 1511827213202883033877927)
        ·
          refine ⟨2267740819804324550816891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511827213202883033877927 2267740819804324550816891)
          ·
            refine ⟨3401611229706486826225337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267740819804324550816891 3401611229706486826225337)
            ·
              refine ⟨2551208422279865119669003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3401611229706486826225337 2551208422279865119669003)
              ·
                refine ⟨3826812633419797679503505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2551208422279865119669003 3826812633419797679503505)
                ·
                  refine ⟨2870109475064848259627629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3826812633419797679503505 2870109475064848259627629)
                  ·
                    refine ⟨1076291053149318097360361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2870109475064848259627629 1076291053149318097360361)
                    ·
                      refine ⟨807218289861988573020271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076291053149318097360361 807218289861988573020271)
                      ·
                        rfl

theorem cell23_1572052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_1572052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572052 prefixEnd_1572052 := by exact prefixLift 1572052
  have htrace : WordTrace (prefixWord ++ tailWord_1572052) baseStart_1572052 baseEnd_1572052 := by
    simpa [prefixWord, tailWord_1572052, baseEnd_1572052] using wordTrace_append hprefix tailTrace_1572052
  have hstable : (prefixWord ++ tailWord_1572052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572052).length < 2 ^ (prefixWord ++ tailWord_1572052).sum := by decide
  have hdescent : baseEnd_1572052 < baseStart_1572052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572071 : List Nat := [1, 1, 5, 3, 3, 10]
def baseStart_1572071 : Nat := 118140960795 + 1572071 * 2 ^ 59
def prefixEnd_1572071 : Nat := 4983230072969 + 3 ^ 40 * 1572071 * 2
def baseEnd_1572071 : Nat := 3321926115203390941081

theorem tailTrace_1572071 : CollatzResearch.WordTrace tailWord_1572071 prefixEnd_1572071 3321926115203390941081 := by
  unfold tailWord_1572071
  simp only [CollatzResearch.WordTrace]
  refine ⟨57338139887662730196460067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38225426591775153464306711 57338139887662730196460067)
  ·
    refine ⟨86007209831494095294690101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57338139887662730196460067 86007209831494095294690101)
    ·
      refine ⟨8063175921702571433877197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86007209831494095294690101 8063175921702571433877197)
      ·
        refine ⟨3023690970638464287703949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8063175921702571433877197 3023690970638464287703949)
        ·
          refine ⟨1133884113989424107888981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3023690970638464287703949 1133884113989424107888981)
          ·
            refine ⟨3321926115203390941081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1133884113989424107888981 3321926115203390941081)
            ·
              rfl

theorem cell23_1572071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 10].length) (baseStart_1572071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572071 prefixEnd_1572071 := by exact prefixLift 1572071
  have htrace : WordTrace (prefixWord ++ tailWord_1572071) baseStart_1572071 baseEnd_1572071 := by
    simpa [prefixWord, tailWord_1572071, baseEnd_1572071] using wordTrace_append hprefix tailTrace_1572071
  have hstable : (prefixWord ++ tailWord_1572071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572071).length < 2 ^ (prefixWord ++ tailWord_1572071).sum := by decide
  have hdescent : baseEnd_1572071 < baseStart_1572071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572108 : List Nat := [2, 2, 1, 2, 2, 3, 2, 1, 3, 3, 2]
def baseStart_1572108 : Nat := 118140960795 + 1572108 * 2 ^ 59
def prefixEnd_1572108 : Nat := 4983230072969 + 3 ^ 40 * 1572108 * 2
def baseEnd_1572108 : Nat := 807247044778640353920013

theorem tailTrace_1572108 : CollatzResearch.WordTrace tailWord_1572108 prefixEnd_1572108 807247044778640353920013 := by
  unfold tailWord_1572108
  simp only [CollatzResearch.WordTrace]
  refine ⟨28669744694264342757778489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38226326259019123677037985 28669744694264342757778489)
  ·
    refine ⟨21502308520698257068333867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28669744694264342757778489 21502308520698257068333867)
    ·
      refine ⟨32253462781047385602500801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21502308520698257068333867 32253462781047385602500801)
      ·
        refine ⟨24190097085785539201875601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32253462781047385602500801 24190097085785539201875601)
        ·
          refine ⟨18142572814339154401406701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24190097085785539201875601 18142572814339154401406701)
          ·
            refine ⟨6803464805377182900527513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18142572814339154401406701 6803464805377182900527513)
            ·
              refine ⟨5102598604032887175395635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6803464805377182900527513 5102598604032887175395635)
              ·
                refine ⟨7653897906049330763093453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5102598604032887175395635 7653897906049330763093453)
                ·
                  refine ⟨2870211714768499036160045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7653897906049330763093453 2870211714768499036160045)
                  ·
                    refine ⟨1076329393038187138560017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2870211714768499036160045 1076329393038187138560017)
                    ·
                      refine ⟨807247044778640353920013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076329393038187138560017 807247044778640353920013)
                      ·
                        rfl

theorem cell23_1572108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 2, 1, 3, 3, 2].length) (baseStart_1572108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572108 prefixEnd_1572108 := by exact prefixLift 1572108
  have htrace : WordTrace (prefixWord ++ tailWord_1572108) baseStart_1572108 baseEnd_1572108 := by
    simpa [prefixWord, tailWord_1572108, baseEnd_1572108] using wordTrace_append hprefix tailTrace_1572108
  have hstable : (prefixWord ++ tailWord_1572108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572108).length < 2 ^ (prefixWord ++ tailWord_1572108).sum := by decide
  have hdescent : baseEnd_1572108 < baseStart_1572108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572195 : List Nat := [1, 1, 1, 5, 2, 3, 3, 2, 5]
def baseStart_1572195 : Nat := 118140960795 + 1572195 * 2 ^ 59
def prefixEnd_1572195 : Nat := 4983230072969 + 3 ^ 40 * 1572195 * 2
def baseEnd_1572195 : Nat := 89699079732842390392457

theorem tailTrace_1572195 : CollatzResearch.WordTrace tailWord_1572195 prefixEnd_1572195 89699079732842390392457 := by
  unfold tailWord_1572195
  simp only [CollatzResearch.WordTrace]
  refine ⟨57342662539213499373974039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38228441692808999582649359 57342662539213499373974039)
  ·
    refine ⟨86013993808820249060961059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57342662539213499373974039 86013993808820249060961059)
    ·
      refine ⟨129020990713230373591441589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86013993808820249060961059 129020990713230373591441589)
      ·
        refine ⟨12095717879365347524197649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129020990713230373591441589 12095717879365347524197649)
        ·
          refine ⟨9071788409524010643148237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12095717879365347524197649 9071788409524010643148237)
          ·
            refine ⟨3401920653571503991180589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9071788409524010643148237 3401920653571503991180589)
            ·
              refine ⟨1275720245089313996692721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3401920653571503991180589 1275720245089313996692721)
              ·
                refine ⟨956790183816985497519541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1275720245089313996692721 956790183816985497519541)
                ·
                  refine ⟨89699079732842390392457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 956790183816985497519541 89699079732842390392457)
                  ·
                    rfl

theorem cell23_1572195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 2, 5].length) (baseStart_1572195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572195 prefixEnd_1572195 := by exact prefixLift 1572195
  have htrace : WordTrace (prefixWord ++ tailWord_1572195) baseStart_1572195 baseEnd_1572195 := by
    simpa [prefixWord, tailWord_1572195, baseEnd_1572195] using wordTrace_append hprefix tailTrace_1572195
  have hstable : (prefixWord ++ tailWord_1572195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572195).length < 2 ^ (prefixWord ++ tailWord_1572195).sum := by decide
  have hdescent : baseEnd_1572195 < baseStart_1572195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572225 : List Nat := [1, 2, 4, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1572225 : Nat := 118140960795 + 1572225 * 2 ^ 59
def prefixEnd_1572225 : Nat := 4983230072969 + 3 ^ 40 * 1572225 * 2
def baseEnd_1572225 : Nat := 269102374005072132052325

theorem tailTrace_1572225 : CollatzResearch.WordTrace tailWord_1572225 prefixEnd_1572225 269102374005072132052325 := by
  unfold tailWord_1572225
  simp only [CollatzResearch.WordTrace]
  refine ⟨57343756729104814497566129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38229171152736542998377419 57343756729104814497566129)
  ·
    refine ⟨43007817546828610873174597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57343756729104814497566129 43007817546828610873174597)
    ·
      refine ⟨8063965790030364538720237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43007817546828610873174597 8063965790030364538720237)
      ·
        refine ⟨3023987171261386702020089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8063965790030364538720237 3023987171261386702020089)
        ·
          refine ⟨2267990378446040026515067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3023987171261386702020089 2267990378446040026515067)
          ·
            refine ⟨3401985567669060039772601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267990378446040026515067 3401985567669060039772601)
            ·
              refine ⟨2551489175751795029829451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3401985567669060039772601 2551489175751795029829451)
              ·
                refine ⟨3827233763627692544744177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2551489175751795029829451 3827233763627692544744177)
                ·
                  refine ⟨2870425322720769408558133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3827233763627692544744177 2870425322720769408558133)
                  ·
                    refine ⟨269102374005072132052325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2870425322720769408558133 269102374005072132052325)
                    ·
                      rfl

theorem cell23_1572225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1572225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572225 prefixEnd_1572225 := by exact prefixLift 1572225
  have htrace : WordTrace (prefixWord ++ tailWord_1572225) baseStart_1572225 baseEnd_1572225 := by
    simpa [prefixWord, tailWord_1572225, baseEnd_1572225] using wordTrace_append hprefix tailTrace_1572225
  have hstable : (prefixWord ++ tailWord_1572225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572225).length < 2 ^ (prefixWord ++ tailWord_1572225).sum := by decide
  have hdescent : baseEnd_1572225 < baseStart_1572225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572228 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 2, 1, 4]
def baseStart_1572228 : Nat := 118140960795 + 1572228 * 2 ^ 59
def prefixEnd_1572228 : Nat := 4983230072969 + 3 ^ 40 * 1572228 * 2
def baseEnd_1572228 : Nat := 807308662457179884419461

theorem tailTrace_1572228 : CollatzResearch.WordTrace tailWord_1572228 prefixEnd_1572228 807308662457179884419461 := by
  unfold tailWord_1572228
  simp only [CollatzResearch.WordTrace]
  refine ⟨28671933074046973004962669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38229244098729297339950225 28671933074046973004962669)
  ·
    refine ⟨10751974902767614876861001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28671933074046973004962669 10751974902767614876861001)
    ·
      refine ⟨8063981177075711157645751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10751974902767614876861001 8063981177075711157645751)
      ·
        refine ⟨12095971765613566736468627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8063981177075711157645751 12095971765613566736468627)
        ·
          refine ⟨18143957648420350104702941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12095971765613566736468627 18143957648420350104702941)
          ·
            refine ⟨6803984118157631289263603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18143957648420350104702941 6803984118157631289263603)
            ·
              refine ⟨10205976177236446933895405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6803984118157631289263603 10205976177236446933895405)
              ·
                refine ⟨3827241066463667600210777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10205976177236446933895405 3827241066463667600210777)
                ·
                  refine ⟨2870430799847750700158083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3827241066463667600210777 2870430799847750700158083)
                  ·
                    refine ⟨4305646199771626050237125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2870430799847750700158083 4305646199771626050237125)
                    ·
                      refine ⟨807308662457179884419461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4305646199771626050237125 807308662457179884419461)
                      ·
                        rfl

theorem cell23_1572228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 2, 1, 4].length) (baseStart_1572228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572228 prefixEnd_1572228 := by exact prefixLift 1572228
  have htrace : WordTrace (prefixWord ++ tailWord_1572228) baseStart_1572228 baseEnd_1572228 := by
    simpa [prefixWord, tailWord_1572228, baseEnd_1572228] using wordTrace_append hprefix tailTrace_1572228
  have hstable : (prefixWord ++ tailWord_1572228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572228).length < 2 ^ (prefixWord ++ tailWord_1572228).sum := by decide
  have hdescent : baseEnd_1572228 < baseStart_1572228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572311 : List Nat := [1, 1, 3, 2, 1, 1, 1, 4, 3, 6]
def baseStart_1572311 : Nat := 118140960795 + 1572311 * 2 ^ 59
def prefixEnd_1572311 : Nat := 4983230072969 + 3 ^ 40 * 1572311 * 2
def baseEnd_1572311 : Nat := 269117093783834353227193

theorem tailTrace_1572311 : CollatzResearch.WordTrace tailWord_1572311 prefixEnd_1572311 269117093783834353227193 := by
  unfold tailWord_1572311
  simp only [CollatzResearch.WordTrace]
  refine ⟨57346893406793251185196787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38231262271195500790131191 57346893406793251185196787)
  ·
    refine ⟨86020340110189876777795181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57346893406793251185196787 86020340110189876777795181)
    ·
      refine ⟨32257627541321203791673193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86020340110189876777795181 32257627541321203791673193)
      ·
        refine ⟨24193220655990902843754895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32257627541321203791673193 24193220655990902843754895)
        ·
          refine ⟨36289830983986354265632343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24193220655990902843754895 36289830983986354265632343)
          ·
            refine ⟨54434746475979531398448515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36289830983986354265632343 54434746475979531398448515)
            ·
              refine ⟨81652119713969297097672773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54434746475979531398448515 81652119713969297097672773)
              ·
                refine ⟨15309772446369243205813645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81652119713969297097672773 15309772446369243205813645)
                ·
                  refine ⟨5741164667388466202180117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15309772446369243205813645 5741164667388466202180117)
                  ·
                    refine ⟨269117093783834353227193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5741164667388466202180117 269117093783834353227193)
                    ·
                      rfl

theorem cell23_1572311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 6].length) (baseStart_1572311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572311 prefixEnd_1572311 := by exact prefixLift 1572311
  have htrace : WordTrace (prefixWord ++ tailWord_1572311) baseStart_1572311 baseEnd_1572311 := by
    simpa [prefixWord, tailWord_1572311, baseEnd_1572311] using wordTrace_append hprefix tailTrace_1572311
  have hstable : (prefixWord ++ tailWord_1572311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572311).length < 2 ^ (prefixWord ++ tailWord_1572311).sum := by decide
  have hdescent : baseEnd_1572311 < baseStart_1572311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572312 : List Nat := [2, 1, 2, 2, 2, 1, 4, 4, 1, 1, 3]
def baseStart_1572312 : Nat := 118140960795 + 1572312 * 2 ^ 59
def prefixEnd_1572312 : Nat := 4983230072969 + 3 ^ 40 * 1572312 * 2
def baseEnd_1572312 : Nat := 807351794832157555769075

theorem tailTrace_1572312 : CollatzResearch.WordTrace tailWord_1572312 prefixEnd_1572312 807351794832157555769075 := by
  unfold tailWord_1572312
  simp only [CollatzResearch.WordTrace]
  refine ⟨28673464939894814177991595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38231286586526418903988793 28673464939894814177991595)
  ·
    refine ⟨43010197409842221266987393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28673464939894814177991595 43010197409842221266987393)
    ·
      refine ⟨32257648057381665950240545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43010197409842221266987393 32257648057381665950240545)
      ·
        refine ⟨24193236043036249462680409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32257648057381665950240545 24193236043036249462680409)
        ·
          refine ⟨18144927032277187097010307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24193236043036249462680409 18144927032277187097010307)
          ·
            refine ⟨27217390548415780645515461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18144927032277187097010307 27217390548415780645515461)
            ·
              refine ⟨5103260727827958871034149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27217390548415780645515461 5103260727827958871034149)
              ·
                refine ⟨956861386467742288318903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5103260727827958871034149 956861386467742288318903)
                ·
                  refine ⟨1435292079701613432478355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 956861386467742288318903 1435292079701613432478355)
                  ·
                    refine ⟨2152938119552420148717533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1435292079701613432478355 2152938119552420148717533)
                    ·
                      refine ⟨807351794832157555769075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2152938119552420148717533 807351794832157555769075)
                      ·
                        rfl

theorem cell23_1572312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 1, 1, 3].length) (baseStart_1572312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572312 prefixEnd_1572312 := by exact prefixLift 1572312
  have htrace : WordTrace (prefixWord ++ tailWord_1572312) baseStart_1572312 baseEnd_1572312 := by
    simpa [prefixWord, tailWord_1572312, baseEnd_1572312] using wordTrace_append hprefix tailTrace_1572312
  have hstable : (prefixWord ++ tailWord_1572312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572312).length < 2 ^ (prefixWord ++ tailWord_1572312).sum := by decide
  have hdescent : baseEnd_1572312 < baseStart_1572312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572348 : List Nat := [2, 2, 2, 1, 2, 1, 2, 4, 1, 2, 4]
def baseStart_1572348 : Nat := 118140960795 + 1572348 * 2 ^ 59
def prefixEnd_1572348 : Nat := 4983230072969 + 3 ^ 40 * 1572348 * 2
def baseEnd_1572348 : Nat := 807370280135719414918909

theorem tailTrace_1572348 : CollatzResearch.WordTrace tailWord_1572348 prefixEnd_1572348 807370280135719414918909 := by
  unfold tailWord_1572348
  simp only [CollatzResearch.WordTrace]
  refine ⟨28674121453829603252146849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38232161938439471002862465 28674121453829603252146849)
  ·
    refine ⟨21505591090372202439110137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28674121453829603252146849 21505591090372202439110137)
    ·
      refine ⟨16129193317779151829332603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21505591090372202439110137 16129193317779151829332603)
      ·
        refine ⟨24193789976668727743998905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16129193317779151829332603 24193789976668727743998905)
        ·
          refine ⟨18145342482501545807999179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24193789976668727743998905 18145342482501545807999179)
          ·
            refine ⟨27218013723752318711998769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18145342482501545807999179 27218013723752318711998769)
            ·
              refine ⟨20413510292814239033999077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27218013723752318711998769 20413510292814239033999077)
              ·
                refine ⟨3827533179902669818874827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20413510292814239033999077 3827533179902669818874827)
                ·
                  refine ⟨5741299769854004728312241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3827533179902669818874827 5741299769854004728312241)
                  ·
                    refine ⟨4305974827390503546234181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5741299769854004728312241 4305974827390503546234181)
                    ·
                      refine ⟨807370280135719414918909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4305974827390503546234181 807370280135719414918909)
                      ·
                        rfl

theorem cell23_1572348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_1572348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572348 prefixEnd_1572348 := by exact prefixLift 1572348
  have htrace : WordTrace (prefixWord ++ tailWord_1572348) baseStart_1572348 baseEnd_1572348 := by
    simpa [prefixWord, tailWord_1572348, baseEnd_1572348] using wordTrace_append hprefix tailTrace_1572348
  have hstable : (prefixWord ++ tailWord_1572348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572348).length < 2 ^ (prefixWord ++ tailWord_1572348).sum := by decide
  have hdescent : baseEnd_1572348 < baseStart_1572348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572406 : List Nat := [5, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3]
def baseStart_1572406 : Nat := 118140960795 + 1572406 * 2 ^ 59
def prefixEnd_1572406 : Nat := 4983230072969 + 3 ^ 40 * 1572406 * 2
def baseEnd_1572406 : Nat := 807400062013680187993643

theorem tailTrace_1572406 : CollatzResearch.WordTrace tailWord_1572406 prefixEnd_1572406 807400062013680187993643 := by
  unfold tailWord_1572406
  simp only [CollatzResearch.WordTrace]
  refine ⟨3584397396340567650619067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38233572227632721606603381 3584397396340567650619067)
  ·
    refine ⟨5376596094510851475928601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3584397396340567650619067 5376596094510851475928601)
    ·
      refine ⟨4032447070883138606946451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5376596094510851475928601 4032447070883138606946451)
      ·
        refine ⟨6048670606324707910419677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4032447070883138606946451 6048670606324707910419677)
        ·
          refine ⟨2268251477371765466407379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6048670606324707910419677 2268251477371765466407379)
          ·
            refine ⟨3402377216057648199611069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268251477371765466407379 3402377216057648199611069)
            ·
              refine ⟨1275891456021618074854151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3402377216057648199611069 1275891456021618074854151)
              ·
                refine ⟨1913837184032427112281227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275891456021618074854151 1913837184032427112281227)
                ·
                  refine ⟨2870755776048640668421841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1913837184032427112281227 2870755776048640668421841)
                  ·
                    refine ⟨2153066832036480501316381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2870755776048640668421841 2153066832036480501316381)
                    ·
                      refine ⟨807400062013680187993643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2153066832036480501316381 807400062013680187993643)
                      ·
                        rfl

theorem cell23_1572406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 1, 2, 3].length) (baseStart_1572406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572406 prefixEnd_1572406 := by exact prefixLift 1572406
  have htrace : WordTrace (prefixWord ++ tailWord_1572406) baseStart_1572406 baseEnd_1572406 := by
    simpa [prefixWord, tailWord_1572406, baseEnd_1572406] using wordTrace_append hprefix tailTrace_1572406
  have hstable : (prefixWord ++ tailWord_1572406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572406).length < 2 ^ (prefixWord ++ tailWord_1572406).sum := by decide
  have hdescent : baseEnd_1572406 < baseStart_1572406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572515 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 4]
def baseStart_1572515 : Nat := 118140960795 + 1572515 * 2 ^ 59
def prefixEnd_1572515 : Nat := 4983230072969 + 3 ^ 40 * 1572515 * 2
def baseEnd_1572515 : Nat := 807456031405020261530641

theorem tailTrace_1572515 : CollatzResearch.WordTrace tailWord_1572515 prefixEnd_1572515 807456031405020261530641 := by
  unfold tailWord_1572515
  simp only [CollatzResearch.WordTrace]
  refine ⟨57354333898054194025622999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38236222598702796017081999 57354333898054194025622999)
  ·
    refine ⟨86031500847081291038434499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57354333898054194025622999 86031500847081291038434499)
    ·
      refine ⟨129047251270621936557651749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86031500847081291038434499 129047251270621936557651749)
      ·
        refine ⟨24196359613241613104559703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129047251270621936557651749 24196359613241613104559703)
        ·
          refine ⟨36294539419862419656839555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24196359613241613104559703 36294539419862419656839555)
          ·
            refine ⟨54441809129793629485259333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36294539419862419656839555 54441809129793629485259333)
            ·
              refine ⟨10207839211836305528486125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54441809129793629485259333 10207839211836305528486125)
              ·
                refine ⟨3827939704438614573182297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10207839211836305528486125 3827939704438614573182297)
                ·
                  refine ⟨2870954778328960929886723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3827939704438614573182297 2870954778328960929886723)
                  ·
                    refine ⟨4306432167493441394830085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2870954778328960929886723 4306432167493441394830085)
                    ·
                      refine ⟨807456031405020261530641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4306432167493441394830085 807456031405020261530641)
                      ·
                        rfl

theorem cell23_1572515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 4].length) (baseStart_1572515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572515 prefixEnd_1572515 := by exact prefixLift 1572515
  have htrace : WordTrace (prefixWord ++ tailWord_1572515) baseStart_1572515 baseEnd_1572515 := by
    simpa [prefixWord, tailWord_1572515, baseEnd_1572515] using wordTrace_append hprefix tailTrace_1572515
  have hstable : (prefixWord ++ tailWord_1572515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572515).length < 2 ^ (prefixWord ++ tailWord_1572515).sum := by decide
  have hdescent : baseEnd_1572515 < baseStart_1572515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572528 : List Nat := [2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 6]
def baseStart_1572528 : Nat := 118140960795 + 1572528 * 2 ^ 59
def prefixEnd_1572528 : Nat := 4983230072969 + 3 ^ 40 * 1572528 * 2
def baseEnd_1572528 : Nat := 807462706653528710668081

theorem tailTrace_1572528 : CollatzResearch.WordTrace tailWord_1572528 prefixEnd_1572528 807462706653528710668081 := by
  unfold tailWord_1572528
  simp only [CollatzResearch.WordTrace]
  refine ⟨28677404023503548622923119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38236538698004731497230825 28677404023503548622923119)
  ·
    refine ⟨43016106035255322934384679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28677404023503548622923119 43016106035255322934384679)
    ·
      refine ⟨64524159052882984401577019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43016106035255322934384679 64524159052882984401577019)
      ·
        refine ⟨96786238579324476602365529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64524159052882984401577019 96786238579324476602365529)
        ·
          refine ⟨72589678934493357451774147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96786238579324476602365529 72589678934493357451774147)
          ·
            refine ⟨108884518401740036177661221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72589678934493357451774147 108884518401740036177661221)
            ·
              refine ⟨20415847200326256783311479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 108884518401740036177661221 20415847200326256783311479)
              ·
                refine ⟨30623770800489385174967219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20415847200326256783311479 30623770800489385174967219)
                ·
                  refine ⟨45935656200734077762450829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30623770800489385174967219 45935656200734077762450829)
                  ·
                    refine ⟨17225871075275279160919061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 45935656200734077762450829 17225871075275279160919061)
                    ·
                      refine ⟨807462706653528710668081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17225871075275279160919061 807462706653528710668081)
                      ·
                        rfl

theorem cell23_1572528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 6].length) (baseStart_1572528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572528 prefixEnd_1572528 := by exact prefixLift 1572528
  have htrace : WordTrace (prefixWord ++ tailWord_1572528) baseStart_1572528 baseEnd_1572528 := by
    simpa [prefixWord, tailWord_1572528, baseEnd_1572528] using wordTrace_append hprefix tailTrace_1572528
  have hstable : (prefixWord ++ tailWord_1572528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572528).length < 2 ^ (prefixWord ++ tailWord_1572528).sum := by decide
  have hdescent : baseEnd_1572528 < baseStart_1572528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572592 : List Nat := [2, 1, 1, 1, 3, 1, 2, 3, 4, 3, 2]
def baseStart_1572592 : Nat := 118140960795 + 1572592 * 2 ^ 59
def prefixEnd_1572592 : Nat := 4983230072969 + 3 ^ 40 * 1572592 * 2
def baseEnd_1572592 : Nat := 807495569415416460267787

theorem tailTrace_1572592 : CollatzResearch.WordTrace tailWord_1572592 prefixEnd_1572592 807495569415416460267787 := by
  unfold tailWord_1572592
  simp only [CollatzResearch.WordTrace]
  refine ⟨28678571159387618088088015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38238094879183490784117353 28678571159387618088088015)
  ·
    refine ⟨43017856739081427132132023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28678571159387618088088015 43017856739081427132132023)
    ·
      refine ⟨64526785108622140698198035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43017856739081427132132023 64526785108622140698198035)
      ·
        refine ⟨96790177662933211047297053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64526785108622140698198035 96790177662933211047297053)
        ·
          refine ⟨36296316623599954142736395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96790177662933211047297053 36296316623599954142736395)
          ·
            refine ⟨54444474935399931214104593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36296316623599954142736395 54444474935399931214104593)
            ·
              refine ⟨40833356201549948410578445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54444474935399931214104593 40833356201549948410578445)
              ·
                refine ⟨15312508575581230653966917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40833356201549948410578445 15312508575581230653966917)
                ·
                  refine ⟨2871095357921480747618797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15312508575581230653966917 2871095357921480747618797)
                  ·
                    refine ⟨1076660759220555280357049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2871095357921480747618797 1076660759220555280357049)
                    ·
                      refine ⟨807495569415416460267787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076660759220555280357049 807495569415416460267787)
                      ·
                        rfl

theorem cell23_1572592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 3, 4, 3, 2].length) (baseStart_1572592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572592 prefixEnd_1572592 := by exact prefixLift 1572592
  have htrace : WordTrace (prefixWord ++ tailWord_1572592) baseStart_1572592 baseEnd_1572592 := by
    simpa [prefixWord, tailWord_1572592, baseEnd_1572592] using wordTrace_append hprefix tailTrace_1572592
  have hstable : (prefixWord ++ tailWord_1572592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572592).length < 2 ^ (prefixWord ++ tailWord_1572592).sum := by decide
  have hdescent : baseEnd_1572592 < baseStart_1572592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572622 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4]
def baseStart_1572622 : Nat := 118140960795 + 1572622 * 2 ^ 59
def prefixEnd_1572622 : Nat := 4983230072969 + 3 ^ 40 * 1572622 * 2
def baseEnd_1572622 : Nat := 807510973835051342892649

theorem tailTrace_1572622 : CollatzResearch.WordTrace tailWord_1572622 prefixEnd_1572622 807510973835051342892649 := by
  unfold tailWord_1572622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7169779563583318912471015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38238824339111034199845413 7169779563583318912471015)
  ·
    refine ⟨10754669345374978368706523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7169779563583318912471015 10754669345374978368706523)
    ·
      refine ⟨16132004018062467553059785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10754669345374978368706523 16132004018062467553059785)
      ·
        refine ⟨12099003013546850664794839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16132004018062467553059785 12099003013546850664794839)
        ·
          refine ⟨18148504520320275997192259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12099003013546850664794839 18148504520320275997192259)
          ·
            refine ⟨27222756780480413995788389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18148504520320275997192259 27222756780480413995788389)
            ·
              refine ⟨5104266896340077624210323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27222756780480413995788389 5104266896340077624210323)
              ·
                refine ⟨7656400344510116436315485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5104266896340077624210323 7656400344510116436315485)
                ·
                  refine ⟨2871150129191293663618307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7656400344510116436315485 2871150129191293663618307)
                  ·
                    refine ⟨4306725193786940495427461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2871150129191293663618307 4306725193786940495427461)
                    ·
                      refine ⟨807510973835051342892649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4306725193786940495427461 807510973835051342892649)
                      ·
                        rfl

theorem cell23_1572622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_1572622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572622 prefixEnd_1572622 := by exact prefixLift 1572622
  have htrace : WordTrace (prefixWord ++ tailWord_1572622) baseStart_1572622 baseEnd_1572622 := by
    simpa [prefixWord, tailWord_1572622, baseEnd_1572622] using wordTrace_append hprefix tailTrace_1572622
  have hstable : (prefixWord ++ tailWord_1572622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572622).length < 2 ^ (prefixWord ++ tailWord_1572622).sum := by decide
  have hdescent : baseEnd_1572622 < baseStart_1572622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572626 : List Nat := [3, 2, 4, 1, 1, 2, 1, 1, 1, 5, 2]
def baseStart_1572626 : Nat := 118140960795 + 1572626 * 2 ^ 59
def prefixEnd_1572626 : Nat := 4983230072969 + 3 ^ 40 * 1572626 * 2
def baseEnd_1572626 : Nat := 807513027757669327242631

theorem tailTrace_1572626 : CollatzResearch.WordTrace tailWord_1572626 prefixEnd_1572626 807513027757669327242631 := by
  unfold tailWord_1572626
  simp only [CollatzResearch.WordTrace]
  refine ⟨14339595600163014995728433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38238921600434706655275821 14339595600163014995728433)
  ·
    refine ⟨10754696700122261246796325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14339595600163014995728433 10754696700122261246796325)
    ·
      refine ⟨2016505631272923983774311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10754696700122261246796325 2016505631272923983774311)
      ·
        refine ⟨3024758446909385975661467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016505631272923983774311 3024758446909385975661467)
        ·
          refine ⟨4537137670364078963492201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3024758446909385975661467 4537137670364078963492201)
          ·
            refine ⟨3402853252773059222619151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4537137670364078963492201 3402853252773059222619151)
            ·
              refine ⟨5104279879159588833928727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3402853252773059222619151 5104279879159588833928727)
              ·
                refine ⟨7656419818739383250893091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5104279879159588833928727 7656419818739383250893091)
                ·
                  refine ⟨11484629728109074876339637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7656419818739383250893091 11484629728109074876339637)
                  ·
                    refine ⟨1076684037010225769656841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11484629728109074876339637 1076684037010225769656841)
                    ·
                      refine ⟨807513027757669327242631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076684037010225769656841 807513027757669327242631)
                      ·
                        rfl

theorem cell23_1572626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_1572626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572626 prefixEnd_1572626 := by exact prefixLift 1572626
  have htrace : WordTrace (prefixWord ++ tailWord_1572626) baseStart_1572626 baseEnd_1572626 := by
    simpa [prefixWord, tailWord_1572626, baseEnd_1572626] using wordTrace_append hprefix tailTrace_1572626
  have hstable : (prefixWord ++ tailWord_1572626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572626).length < 2 ^ (prefixWord ++ tailWord_1572626).sum := by decide
  have hdescent : baseEnd_1572626 < baseStart_1572626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572639 : List Nat := [1, 1, 2, 4, 2, 1, 1, 2, 5, 2, 2]
def baseStart_1572639 : Nat := 118140960795 + 1572639 * 2 ^ 59
def prefixEnd_1572639 : Nat := 4983230072969 + 3 ^ 40 * 1572639 * 2
def baseEnd_1572639 : Nat := 807519703006177776380071

theorem tailTrace_1572639 : CollatzResearch.WordTrace tailWord_1572639 prefixEnd_1572639 807519703006177776380071 := by
  unfold tailWord_1572639
  simp only [CollatzResearch.WordTrace]
  refine ⟨57358856549604963203136971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38239237699736642135424647 57358856549604963203136971)
  ·
    refine ⟨86038284824407444804705457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57358856549604963203136971 86038284824407444804705457)
    ·
      refine ⟨64528713618305583603529093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86038284824407444804705457 64528713618305583603529093)
      ·
        refine ⟨12099133803432296925661705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64528713618305583603529093 12099133803432296925661705)
        ·
          refine ⟨9074350352574222694246279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12099133803432296925661705 9074350352574222694246279)
          ·
            refine ⟨13611525528861334041369419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9074350352574222694246279 13611525528861334041369419)
            ·
              refine ⟨20417288293292001062054129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13611525528861334041369419 20417288293292001062054129)
              ·
                refine ⟨15312966219969000796540597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20417288293292001062054129 15312966219969000796540597)
                ·
                  refine ⟨1435590583122093824675681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 15312966219969000796540597 1435590583122093824675681)
                  ·
                    refine ⟨1076692937341570368506761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1435590583122093824675681 1076692937341570368506761)
                    ·
                      refine ⟨807519703006177776380071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076692937341570368506761 807519703006177776380071)
                      ·
                        rfl

theorem cell23_1572639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 2, 5, 2, 2].length) (baseStart_1572639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572639 prefixEnd_1572639 := by exact prefixLift 1572639
  have htrace : WordTrace (prefixWord ++ tailWord_1572639) baseStart_1572639 baseEnd_1572639 := by
    simpa [prefixWord, tailWord_1572639, baseEnd_1572639] using wordTrace_append hprefix tailTrace_1572639
  have hstable : (prefixWord ++ tailWord_1572639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572639).length < 2 ^ (prefixWord ++ tailWord_1572639).sum := by decide
  have hdescent : baseEnd_1572639 < baseStart_1572639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572642 : List Nat := [3, 3, 1, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_1572642 : Nat := 118140960795 + 1572642 * 2 ^ 59
def prefixEnd_1572642 : Nat := 4983230072969 + 3 ^ 40 * 1572642 * 2
def baseEnd_1572642 : Nat := 807521243448141264642557

theorem tailTrace_1572642 : CollatzResearch.WordTrace tailWord_1572642 prefixEnd_1572642 807521243448141264642557 := by
  unfold tailWord_1572642
  simp only [CollatzResearch.WordTrace]
  refine ⟨14339741492148523678874045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38239310645729396476997453 14339741492148523678874045)
  ·
    refine ⟨5377403059555696379577767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14339741492148523678874045 5377403059555696379577767)
    ·
      refine ⟨8066104589333544569366651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5377403059555696379577767 8066104589333544569366651)
      ·
        refine ⟨12099156884000316854049977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8066104589333544569366651 12099156884000316854049977)
        ·
          refine ⟨9074367663000237640537483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12099156884000316854049977 9074367663000237640537483)
          ·
            refine ⟨13611551494500356460806225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9074367663000237640537483 13611551494500356460806225)
            ·
              refine ⟨10208663620875267345604669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13611551494500356460806225 10208663620875267345604669)
              ·
                refine ⟨3828248857828225254601751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10208663620875267345604669 3828248857828225254601751)
                ·
                  refine ⟨5742373286742337881902627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828248857828225254601751 5742373286742337881902627)
                  ·
                    refine ⟨8613559930113506822853941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5742373286742337881902627 8613559930113506822853941)
                    ·
                      refine ⟨807521243448141264642557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8613559930113506822853941 807521243448141264642557)
                      ·
                        rfl

theorem cell23_1572642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_1572642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572642 prefixEnd_1572642 := by exact prefixLift 1572642
  have htrace : WordTrace (prefixWord ++ tailWord_1572642) baseStart_1572642 baseEnd_1572642 := by
    simpa [prefixWord, tailWord_1572642, baseEnd_1572642] using wordTrace_append hprefix tailTrace_1572642
  have hstable : (prefixWord ++ tailWord_1572642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572642).length < 2 ^ (prefixWord ++ tailWord_1572642).sum := by decide
  have hdescent : baseEnd_1572642 < baseStart_1572642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572645 : List Nat := [1, 3, 1, 2, 3, 3, 10]
def baseStart_1572645 : Nat := 118140960795 + 1572645 * 2 ^ 59
def prefixEnd_1572645 : Nat := 4983230072969 + 3 ^ 40 * 1572645 * 2
def baseEnd_1572645 : Nat := 9969417085063021640803

theorem tailTrace_1572645 : CollatzResearch.WordTrace tailWord_1572645 prefixEnd_1572645 9969417085063021640803 := by
  unfold tailWord_1572645
  simp only [CollatzResearch.WordTrace]
  refine ⟨57359075387583226227855389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38239383591722150818570259 57359075387583226227855389)
  ·
    refine ⟨21509653270343709835445771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57359075387583226227855389 21509653270343709835445771)
    ·
      refine ⟨32264479905515564753168657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21509653270343709835445771 32264479905515564753168657)
      ·
        refine ⟨24198359929136673564876493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32264479905515564753168657 24198359929136673564876493)
        ·
          refine ⟨9074384973426252586828685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24198359929136673564876493 9074384973426252586828685)
          ·
            refine ⟨3402894365034844720060757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9074384973426252586828685 3402894365034844720060757)
            ·
              refine ⟨9969417085063021640803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3402894365034844720060757 9969417085063021640803)
              ·
                rfl

theorem cell23_1572645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 10].length) (baseStart_1572645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572645 prefixEnd_1572645 := by exact prefixLift 1572645
  have htrace : WordTrace (prefixWord ++ tailWord_1572645) baseStart_1572645 baseEnd_1572645 := by
    simpa [prefixWord, tailWord_1572645, baseEnd_1572645] using wordTrace_append hprefix tailTrace_1572645
  have hstable : (prefixWord ++ tailWord_1572645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572645).length < 2 ^ (prefixWord ++ tailWord_1572645).sum := by decide
  have hdescent : baseEnd_1572645 < baseStart_1572645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572666 : List Nat := [3, 1, 1, 1, 5, 2, 3, 1, 2, 4]
def baseStart_1572666 : Nat := 118140960795 + 1572666 * 2 ^ 59
def prefixEnd_1572666 : Nat := 4983230072969 + 3 ^ 40 * 1572666 * 2
def baseEnd_1572666 : Nat := 269177855661283056914149

theorem tailTrace_1572666 : CollatzResearch.WordTrace tailWord_1572666 prefixEnd_1572666 269177855661283056914149 := by
  unfold tailWord_1572666
  simp only [CollatzResearch.WordTrace]
  refine ⟨14339960330126786703592463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38239894213671431209579901 14339960330126786703592463)
  ·
    refine ⟨21509940495190180055388695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14339960330126786703592463 21509940495190180055388695)
    ·
      refine ⟨32264910742785270083083043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21509940495190180055388695 32264910742785270083083043)
      ·
        refine ⟨48397366114177905124624565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32264910742785270083083043 48397366114177905124624565)
        ·
          refine ⟨4537253073204178605433553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48397366114177905124624565 4537253073204178605433553)
          ·
            refine ⟨3402939804903133954075165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4537253073204178605433553 3402939804903133954075165)
            ·
              refine ⟨1276102426838675232778187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3402939804903133954075165 1276102426838675232778187)
              ·
                refine ⟨1914153640258012849167281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276102426838675232778187 1914153640258012849167281)
                ·
                  refine ⟨1435615230193509636875461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1914153640258012849167281 1435615230193509636875461)
                  ·
                    refine ⟨269177855661283056914149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1435615230193509636875461 269177855661283056914149)
                    ·
                      rfl

theorem cell23_1572666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_1572666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572666 prefixEnd_1572666 := by exact prefixLift 1572666
  have htrace : WordTrace (prefixWord ++ tailWord_1572666) baseStart_1572666 baseEnd_1572666 := by
    simpa [prefixWord, tailWord_1572666, baseEnd_1572666] using wordTrace_append hprefix tailTrace_1572666
  have hstable : (prefixWord ++ tailWord_1572666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572666).length < 2 ^ (prefixWord ++ tailWord_1572666).sum := by decide
  have hdescent : baseEnd_1572666 < baseStart_1572666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572669 : List Nat := [1, 4, 1, 4, 1, 1, 3, 1, 1, 2, 4]
def baseStart_1572669 : Nat := 118140960795 + 1572669 * 2 ^ 59
def prefixEnd_1572669 : Nat := 4983230072969 + 3 ^ 40 * 1572669 * 2
def baseEnd_1572669 : Nat := 807535107425812659004933

theorem tailTrace_1572669 : CollatzResearch.WordTrace tailWord_1572669 prefixEnd_1572669 807535107425812659004933 := by
  unfold tailWord_1572669
  simp only [CollatzResearch.WordTrace]
  refine ⟨57359950739496278326729061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38239967159664185551152707 57359950739496278326729061)
  ·
    refine ⟨10754990763655552186261699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57359950739496278326729061 10754990763655552186261699)
    ·
      refine ⟨16132486145483328279392549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10754990763655552186261699 16132486145483328279392549)
      ·
        refine ⟨3024841152278124052386103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16132486145483328279392549 3024841152278124052386103)
        ·
          refine ⟨4537261728417186078579155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3024841152278124052386103 4537261728417186078579155)
          ·
            refine ⟨6805892592625779117868733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537261728417186078579155 6805892592625779117868733)
            ·
              refine ⟨2552209722234667169200775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6805892592625779117868733 2552209722234667169200775)
              ·
                refine ⟨3828314583352000753801163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2552209722234667169200775 3828314583352000753801163)
                ·
                  refine ⟨5742471875028001130701745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828314583352000753801163 5742471875028001130701745)
                  ·
                    refine ⟨4306853906271000848026309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5742471875028001130701745 4306853906271000848026309)
                    ·
                      refine ⟨807535107425812659004933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4306853906271000848026309 807535107425812659004933)
                      ·
                        rfl

theorem cell23_1572669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 3, 1, 1, 2, 4].length) (baseStart_1572669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572669 prefixEnd_1572669 := by exact prefixLift 1572669
  have htrace : WordTrace (prefixWord ++ tailWord_1572669) baseStart_1572669 baseEnd_1572669 := by
    simpa [prefixWord, tailWord_1572669, baseEnd_1572669] using wordTrace_append hprefix tailTrace_1572669
  have hstable : (prefixWord ++ tailWord_1572669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572669).length < 2 ^ (prefixWord ++ tailWord_1572669).sum := by decide
  have hdescent : baseEnd_1572669 < baseStart_1572669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572689 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 4, 1, 3]
def baseStart_1572689 : Nat := 118140960795 + 1572689 * 2 ^ 59
def prefixEnd_1572689 : Nat := 4983230072969 + 3 ^ 40 * 1572689 * 2
def baseEnd_1572689 : Nat := 807545377038902580754841

theorem tailTrace_1572689 : CollatzResearch.WordTrace tailWord_1572689 prefixEnd_1572689 807545377038902580754841 := by
  unfold tailWord_1572689
  simp only [CollatzResearch.WordTrace]
  refine ⟨57360680199423821742457121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38240453466282547828304747 57360680199423821742457121)
  ·
    refine ⟨43020510149567866306842841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57360680199423821742457121 43020510149567866306842841)
    ·
      refine ⟨32265382612175899730132131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43020510149567866306842841 32265382612175899730132131)
      ·
        refine ⟨48398073918263849595198197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32265382612175899730132131 48398073918263849595198197)
        ·
          refine ⟨4537319429837235899549831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48398073918263849595198197 4537319429837235899549831)
          ·
            refine ⟨6805979144755853849324747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537319429837235899549831 6805979144755853849324747)
            ·
              refine ⟨10208968717133780773987121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6805979144755853849324747 10208968717133780773987121)
              ·
                refine ⟨7656726537850335580490341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10208968717133780773987121 7656726537850335580490341)
                ·
                  refine ⟨1435636225846937921341939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7656726537850335580490341 1435636225846937921341939)
                  ·
                    refine ⟨2153454338770406882012909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1435636225846937921341939 2153454338770406882012909)
                    ·
                      refine ⟨807545377038902580754841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2153454338770406882012909 807545377038902580754841)
                      ·
                        rfl

theorem cell23_1572689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 1, 3].length) (baseStart_1572689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572689 prefixEnd_1572689 := by exact prefixLift 1572689
  have htrace : WordTrace (prefixWord ++ tailWord_1572689) baseStart_1572689 baseEnd_1572689 := by
    simpa [prefixWord, tailWord_1572689, baseEnd_1572689] using wordTrace_append hprefix tailTrace_1572689
  have hstable : (prefixWord ++ tailWord_1572689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572689).length < 2 ^ (prefixWord ++ tailWord_1572689).sum := by decide
  have hdescent : baseEnd_1572689 < baseStart_1572689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572690 : List Nat := [3, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2]
def baseStart_1572690 : Nat := 118140960795 + 1572690 * 2 ^ 59
def prefixEnd_1572690 : Nat := 4983230072969 + 3 ^ 40 * 1572690 * 2
def baseEnd_1572690 : Nat := 807545890519557076842337

theorem tailTrace_1572690 : CollatzResearch.WordTrace tailWord_1572690 prefixEnd_1572690 807545890519557076842337 := by
  unfold tailWord_1572690
  simp only [CollatzResearch.WordTrace]
  refine ⟨14340179168105049728310881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38240477781613465942162349 14340179168105049728310881)
  ·
    refine ⟨10755134376078787296233161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14340179168105049728310881 10755134376078787296233161)
    ·
      refine ⟨8066350782059090472174871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10755134376078787296233161 8066350782059090472174871)
      ·
        refine ⟨12099526173088635708262307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8066350782059090472174871 12099526173088635708262307)
        ·
          refine ⟨18149289259632953562393461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12099526173088635708262307 18149289259632953562393461)
          ·
            refine ⟨1701495868090589396474387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18149289259632953562393461 1701495868090589396474387)
            ·
              refine ⟨2552243802135884094711581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1701495868090589396474387 2552243802135884094711581)
              ·
                refine ⟨957091425800956535516843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2552243802135884094711581 957091425800956535516843)
                ·
                  refine ⟨1435637138701434803275265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957091425800956535516843 1435637138701434803275265)
                  ·
                    refine ⟨1076727854026076102456449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1435637138701434803275265 1076727854026076102456449)
                    ·
                      refine ⟨807545890519557076842337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076727854026076102456449 807545890519557076842337)
                      ·
                        rfl

theorem cell23_1572690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2].length) (baseStart_1572690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572690 prefixEnd_1572690 := by exact prefixLift 1572690
  have htrace : WordTrace (prefixWord ++ tailWord_1572690) baseStart_1572690 baseEnd_1572690 := by
    simpa [prefixWord, tailWord_1572690, baseEnd_1572690] using wordTrace_append hprefix tailTrace_1572690
  have hstable : (prefixWord ++ tailWord_1572690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572690).length < 2 ^ (prefixWord ++ tailWord_1572690).sum := by decide
  have hdescent : baseEnd_1572690 < baseStart_1572690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572706 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_1572706 : Nat := 118140960795 + 1572706 * 2 ^ 59
def prefixEnd_1572706 : Nat := 4983230072969 + 3 ^ 40 * 1572706 * 2
def baseEnd_1572706 : Nat := 807554106210029014242263

theorem tailTrace_1572706 : CollatzResearch.WordTrace tailWord_1572706 prefixEnd_1572706 807554106210029014242263 := by
  unfold tailWord_1572706
  simp only [CollatzResearch.WordTrace]
  refine ⟨14340325060090558411456493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38240866826908155763883981 14340325060090558411456493)
  ·
    refine ⟨5377621897533959404296185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14340325060090558411456493 5377621897533959404296185)
    ·
      refine ⟨4033216423150469553222139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5377621897533959404296185 4033216423150469553222139)
      ·
        refine ⟨6049824634725704329833209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033216423150469553222139 6049824634725704329833209)
        ·
          refine ⟨4537368476044278247374907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6049824634725704329833209 4537368476044278247374907)
          ·
            refine ⟨6806052714066417371062361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537368476044278247374907 6806052714066417371062361)
            ·
              refine ⟨5104539535549813028296771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6806052714066417371062361 5104539535549813028296771)
              ·
                refine ⟨7656809303324719542445157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5104539535549813028296771 7656809303324719542445157)
                ·
                  refine ⟨1435651744373384914208467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7656809303324719542445157 1435651744373384914208467)
                  ·
                    refine ⟨2153477616560077371312701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1435651744373384914208467 2153477616560077371312701)
                    ·
                      refine ⟨807554106210029014242263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2153477616560077371312701 807554106210029014242263)
                      ·
                        rfl

theorem cell23_1572706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_1572706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572706 prefixEnd_1572706 := by exact prefixLift 1572706
  have htrace : WordTrace (prefixWord ++ tailWord_1572706) baseStart_1572706 baseEnd_1572706 := by
    simpa [prefixWord, tailWord_1572706, baseEnd_1572706] using wordTrace_append hprefix tailTrace_1572706
  have hstable : (prefixWord ++ tailWord_1572706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572706).length < 2 ^ (prefixWord ++ tailWord_1572706).sum := by decide
  have hdescent : baseEnd_1572706 < baseStart_1572706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572712 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 2, 3, 4]
def baseStart_1572712 : Nat := 118140960795 + 1572712 * 2 ^ 59
def prefixEnd_1572712 : Nat := 4983230072969 + 3 ^ 40 * 1572712 * 2
def baseEnd_1572712 : Nat := 807557187093955990767235

theorem tailTrace_1572712 : CollatzResearch.WordTrace tailWord_1572712 prefixEnd_1572712 807557187093955990767235 := by
  unfold tailWord_1572712
  simp only [CollatzResearch.WordTrace]
  refine ⟨28680759539170248335272195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38241012718893664447029593 28680759539170248335272195)
  ·
    refine ⟨43021139308755372502908293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28680759539170248335272195 43021139308755372502908293)
    ·
      refine ⟨8066463620391632344295305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43021139308755372502908293 8066463620391632344295305)
      ·
        refine ⟨6049847715293724258221479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8066463620391632344295305 6049847715293724258221479)
        ·
          refine ⟨9074771572940586387332219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6049847715293724258221479 9074771572940586387332219)
          ·
            refine ⟨13612157359410879580998329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9074771572940586387332219 13612157359410879580998329)
            ·
              refine ⟨10209118019558159685748747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13612157359410879580998329 10209118019558159685748747)
              ·
                refine ⟨15313677029337239528623121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10209118019558159685748747 15313677029337239528623121)
                ·
                  refine ⟨11485257772002929646467341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15313677029337239528623121 11485257772002929646467341)
                  ·
                    refine ⟨4306971664501098617425253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11485257772002929646467341 4306971664501098617425253)
                    ·
                      refine ⟨807557187093955990767235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4306971664501098617425253 807557187093955990767235)
                      ·
                        rfl

theorem cell23_1572712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_1572712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572712 prefixEnd_1572712 := by exact prefixLift 1572712
  have htrace : WordTrace (prefixWord ++ tailWord_1572712) baseStart_1572712 baseEnd_1572712 := by
    simpa [prefixWord, tailWord_1572712, baseEnd_1572712] using wordTrace_append hprefix tailTrace_1572712
  have hstable : (prefixWord ++ tailWord_1572712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572712).length < 2 ^ (prefixWord ++ tailWord_1572712).sum := by decide
  have hdescent : baseEnd_1572712 < baseStart_1572712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572715 : List Nat := [1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 5]
def baseStart_1572715 : Nat := 118140960795 + 1572715 * 2 ^ 59
def prefixEnd_1572715 : Nat := 4983230072969 + 3 ^ 40 * 1572715 * 2
def baseEnd_1572715 : Nat := 807558727535919479029721

theorem tailTrace_1572715 : CollatzResearch.WordTrace tailWord_1572715 prefixEnd_1572715 807558727535919479029721 := by
  unfold tailWord_1572715
  simp only [CollatzResearch.WordTrace]
  refine ⟨57361628497329628182903599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38241085664886418788602399 57361628497329628182903599)
  ·
    refine ⟨86042442745994442274355399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57361628497329628182903599 86042442745994442274355399)
    ·
      refine ⟨129063664118991663411533099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86042442745994442274355399 129063664118991663411533099)
      ·
        refine ⟨193595496178487495117299649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129063664118991663411533099 193595496178487495117299649)
        ·
          refine ⟨145196622133865621337974737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193595496178487495117299649 145196622133865621337974737)
          ·
            refine ⟨108897466600399216003481053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145196622133865621337974737 108897466600399216003481053)
            ·
              refine ⟨40836549975149706001305395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108897466600399216003481053 40836549975149706001305395)
              ·
                refine ⟨61254824962724559001958093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40836549975149706001305395 61254824962724559001958093)
                ·
                  refine ⟨22970559361021709625734285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61254824962724559001958093 22970559361021709625734285)
                  ·
                    refine ⟨8613959760383141109650357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22970559361021709625734285 8613959760383141109650357)
                    ·
                      refine ⟨807558727535919479029721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8613959760383141109650357 807558727535919479029721)
                      ·
                        rfl

theorem cell23_1572715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 5].length) (baseStart_1572715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572715 prefixEnd_1572715 := by exact prefixLift 1572715
  have htrace : WordTrace (prefixWord ++ tailWord_1572715) baseStart_1572715 baseEnd_1572715 := by
    simpa [prefixWord, tailWord_1572715, baseEnd_1572715] using wordTrace_append hprefix tailTrace_1572715
  have hstable : (prefixWord ++ tailWord_1572715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572715).length < 2 ^ (prefixWord ++ tailWord_1572715).sum := by decide
  have hdescent : baseEnd_1572715 < baseStart_1572715 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572729 : List Nat := [1, 2, 1, 3, 2, 2, 2, 3, 1, 4, 2]
def baseStart_1572729 : Nat := 118140960795 + 1572729 * 2 ^ 59
def prefixEnd_1572729 : Nat := 4983230072969 + 3 ^ 40 * 1572729 * 2
def baseEnd_1572729 : Nat := 807565916265082424254657

theorem tailTrace_1572729 : CollatzResearch.WordTrace tailWord_1572729 prefixEnd_1572729 807565916265082424254657 := by
  unfold tailWord_1572729
  simp only [CollatzResearch.WordTrace]
  refine ⟨57362139119278908573913241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38241426079519272382608827 57362139119278908573913241)
  ·
    refine ⟨43021604339459181430434931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57362139119278908573913241 43021604339459181430434931)
    ·
      refine ⟨64532406509188772145652397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43021604339459181430434931 64532406509188772145652397)
      ·
        refine ⟨24199652440945789554619649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64532406509188772145652397 24199652440945789554619649)
        ·
          refine ⟨18149739330709342165964737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24199652440945789554619649 18149739330709342165964737)
          ·
            refine ⟨13612304498032006624473553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18149739330709342165964737 13612304498032006624473553)
            ·
              refine ⟨10209228373524004968355165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13612304498032006624473553 10209228373524004968355165)
              ·
                refine ⟨3828460640071501863133187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10209228373524004968355165 3828460640071501863133187)
                ·
                  refine ⟨5742690960107252794699781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3828460640071501863133187 5742690960107252794699781)
                  ·
                    refine ⟨1076754555020109899006209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5742690960107252794699781 1076754555020109899006209)
                    ·
                      refine ⟨807565916265082424254657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076754555020109899006209 807565916265082424254657)
                      ·
                        rfl

theorem cell23_1572729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 3, 1, 4, 2].length) (baseStart_1572729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572729 prefixEnd_1572729 := by exact prefixLift 1572729
  have htrace : WordTrace (prefixWord ++ tailWord_1572729) baseStart_1572729 baseEnd_1572729 := by
    simpa [prefixWord, tailWord_1572729, baseEnd_1572729] using wordTrace_append hprefix tailTrace_1572729
  have hstable : (prefixWord ++ tailWord_1572729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572729).length < 2 ^ (prefixWord ++ tailWord_1572729).sum := by decide
  have hdescent : baseEnd_1572729 < baseStart_1572729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572735 : List Nat := [1, 1, 2, 2, 1, 1, 3, 3, 9]
def baseStart_1572735 : Nat := 118140960795 + 1572735 * 2 ^ 59
def prefixEnd_1572735 : Nat := 4983230072969 + 3 ^ 40 * 1572735 * 2
def baseEnd_1572735 : Nat := 89729888572112155642181

theorem tailTrace_1572735 : CollatzResearch.WordTrace tailWord_1572735 prefixEnd_1572735 89729888572112155642181 := by
  unfold tailWord_1572735
  simp only [CollatzResearch.WordTrace]
  refine ⟨57362357957257171598631659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38241571971504781065754439 57362357957257171598631659)
  ·
    refine ⟨86043536935885757397947489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57362357957257171598631659 86043536935885757397947489)
    ·
      refine ⟨64532652701914318048460617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86043536935885757397947489 64532652701914318048460617)
      ·
        refine ⟨48399489526435738536345463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64532652701914318048460617 48399489526435738536345463)
        ·
          refine ⟨72599234289653607804518195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48399489526435738536345463 72599234289653607804518195)
          ·
            refine ⟨108898851434480411706777293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72599234289653607804518195 108898851434480411706777293)
            ·
              refine ⟨40837069287930154390041485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 108898851434480411706777293 40837069287930154390041485)
              ·
                refine ⟨15313900982973807896265557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40837069287930154390041485 15313900982973807896265557)
                ·
                  refine ⟨89729888572112155642181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15313900982973807896265557 89729888572112155642181)
                  ·
                    rfl

theorem cell23_1572735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 3, 9].length) (baseStart_1572735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572735 prefixEnd_1572735 := by exact prefixLift 1572735
  have htrace : WordTrace (prefixWord ++ tailWord_1572735) baseStart_1572735 baseEnd_1572735 := by
    simpa [prefixWord, tailWord_1572735, baseEnd_1572735] using wordTrace_append hprefix tailTrace_1572735
  have hstable : (prefixWord ++ tailWord_1572735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572735).length < 2 ^ (prefixWord ++ tailWord_1572735).sum := by decide
  have hdescent : baseEnd_1572735 < baseStart_1572735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572755 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 8]
def baseStart_1572755 : Nat := 118140960795 + 1572755 * 2 ^ 59
def prefixEnd_1572755 : Nat := 4983230072969 + 3 ^ 40 * 1572755 * 2
def baseEnd_1572755 : Nat := 807579266762099322529537

theorem tailTrace_1572755 : CollatzResearch.WordTrace tailWord_1572755 prefixEnd_1572755 807579266762099322529537 := by
  unfold tailWord_1572755
  simp only [CollatzResearch.WordTrace]
  refine ⟨57363087417184715014359719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38242058278123143342906479 57363087417184715014359719)
  ·
    refine ⟨86044631125777072521539579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57363087417184715014359719 86044631125777072521539579)
    ·
      refine ⟨129066946688665608782309369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86044631125777072521539579 129066946688665608782309369)
      ·
        refine ⟨96800210016499206586732027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129066946688665608782309369 96800210016499206586732027)
        ·
          refine ⟨145200315024748809880098041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96800210016499206586732027 145200315024748809880098041)
          ·
            refine ⟨108900236268561607410073531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145200315024748809880098041 108900236268561607410073531)
            ·
              refine ⟨163350354402842411115110297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108900236268561607410073531 163350354402842411115110297)
              ·
                refine ⟨122512765802131808336332723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163350354402842411115110297 122512765802131808336332723)
                ·
                  refine ⟨183769148703197712504499085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 122512765802131808336332723 183769148703197712504499085)
                  ·
                    refine ⟨68913430763699142189187157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 183769148703197712504499085 68913430763699142189187157)
                    ·
                      refine ⟨807579266762099322529537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 68913430763699142189187157 807579266762099322529537)
                      ·
                        rfl

theorem cell23_1572755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_1572755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572755 prefixEnd_1572755 := by exact prefixLift 1572755
  have htrace : WordTrace (prefixWord ++ tailWord_1572755) baseStart_1572755 baseEnd_1572755 := by
    simpa [prefixWord, tailWord_1572755, baseEnd_1572755] using wordTrace_append hprefix tailTrace_1572755
  have hstable : (prefixWord ++ tailWord_1572755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572755).length < 2 ^ (prefixWord ++ tailWord_1572755).sum := by decide
  have hdescent : baseEnd_1572755 < baseStart_1572755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572758 : List Nat := [5, 3, 1, 1, 3, 1, 2, 2, 1, 2, 2]
def baseStart_1572758 : Nat := 118140960795 + 1572758 * 2 ^ 59
def prefixEnd_1572758 : Nat := 4983230072969 + 3 ^ 40 * 1572758 * 2
def baseEnd_1572758 : Nat := 807580807204062810792025

theorem tailTrace_1572758 : CollatzResearch.WordTrace tailWord_1572758 prefixEnd_1572758 807580807204062810792025 := by
  unfold tailWord_1572758
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585199802260865407919933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 38242131224115897684479285 3585199802260865407919933)
  ·
    refine ⟨1344449925847824527969975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3585199802260865407919933 1344449925847824527969975)
    ·
      refine ⟨2016674888771736791954963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1344449925847824527969975 2016674888771736791954963)
      ·
        refine ⟨3025012333157605187932445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016674888771736791954963 3025012333157605187932445)
        ·
          refine ⟨1134379624934101945474667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3025012333157605187932445 1134379624934101945474667)
          ·
            refine ⟨1701569437401152918212001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134379624934101945474667 1701569437401152918212001)
            ·
              refine ⟨1276177078050864688659001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701569437401152918212001 1276177078050864688659001)
              ·
                refine ⟨957132808538148516494251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1276177078050864688659001 957132808538148516494251)
                ·
                  refine ⟨1435699212807222774741377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 957132808538148516494251 1435699212807222774741377)
                  ·
                    refine ⟨1076774409605417081056033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1435699212807222774741377 1076774409605417081056033)
                    ·
                      refine ⟨807580807204062810792025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076774409605417081056033 807580807204062810792025)
                      ·
                        rfl

theorem cell23_1572758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_1572758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572758 prefixEnd_1572758 := by exact prefixLift 1572758
  have htrace : WordTrace (prefixWord ++ tailWord_1572758) baseStart_1572758 baseEnd_1572758 := by
    simpa [prefixWord, tailWord_1572758, baseEnd_1572758] using wordTrace_append hprefix tailTrace_1572758
  have hstable : (prefixWord ++ tailWord_1572758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572758).length < 2 ^ (prefixWord ++ tailWord_1572758).sum := by decide
  have hdescent : baseEnd_1572758 < baseStart_1572758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572846 : List Nat := [4, 1, 2, 1, 3, 1, 2, 2, 3, 4]
def baseStart_1572846 : Nat := 118140960795 + 1572846 * 2 ^ 59
def prefixEnd_1572846 : Nat := 4983230072969 + 3 ^ 40 * 1572846 * 2
def baseEnd_1572846 : Nat := 269208664500552822163873

theorem tailTrace_1572846 : CollatzResearch.WordTrace tailWord_1572846 prefixEnd_1572846 269208664500552822163873 := by
  unfold tailWord_1572846
  simp only [CollatzResearch.WordTrace]
  refine ⟨7170800807481879694490299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38244270973236691703948261 7170800807481879694490299)
  ·
    refine ⟨10756201211222819541735449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7170800807481879694490299 10756201211222819541735449)
    ·
      refine ⟨8067150908417114656301587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10756201211222819541735449 8067150908417114656301587)
      ·
        refine ⟨12100726362625671984452381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8067150908417114656301587 12100726362625671984452381)
        ·
          refine ⟨4537772385984626994169643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12100726362625671984452381 4537772385984626994169643)
          ·
            refine ⟨6806658578976940491254465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537772385984626994169643 6806658578976940491254465)
            ·
              refine ⟨5104993934232705368440849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6806658578976940491254465 5104993934232705368440849)
              ·
                refine ⟨3828745450674529026330637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5104993934232705368440849 3828745450674529026330637)
                ·
                  refine ⟨1435779544002948384873989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3828745450674529026330637 1435779544002948384873989)
                  ·
                    refine ⟨269208664500552822163873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1435779544002948384873989 269208664500552822163873)
                    ·
                      rfl

theorem cell23_1572846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 2, 2, 3, 4].length) (baseStart_1572846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572846 prefixEnd_1572846 := by exact prefixLift 1572846
  have htrace : WordTrace (prefixWord ++ tailWord_1572846) baseStart_1572846 baseEnd_1572846 := by
    simpa [prefixWord, tailWord_1572846, baseEnd_1572846] using wordTrace_append hprefix tailTrace_1572846
  have hstable : (prefixWord ++ tailWord_1572846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572846).length < 2 ^ (prefixWord ++ tailWord_1572846).sum := by decide
  have hdescent : baseEnd_1572846 < baseStart_1572846 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572893 : List Nat := [1, 4, 2, 2, 2, 3, 2, 1, 6]
def baseStart_1572893 : Nat := 118140960795 + 1572893 * 2 ^ 59
def prefixEnd_1572893 : Nat := 4983230072969 + 3 ^ 40 * 1572893 * 2
def baseEnd_1572893 : Nat := 89738903010268864733767

theorem tailTrace_1572893 : CollatzResearch.WordTrace tailWord_1572893 prefixEnd_1572893 89738903010268864733767 := by
  unfold tailWord_1572893
  simp only [CollatzResearch.WordTrace]
  refine ⟨57368120690684764582883333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38245413793789843055255555 57368120690684764582883333)
  ·
    refine ⟨10756522629503393359290625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57368120690684764582883333 10756522629503393359290625)
    ·
      refine ⟨8067391972127545019467969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10756522629503393359290625 8067391972127545019467969)
      ·
        refine ⟨6050543979095658764600977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8067391972127545019467969 6050543979095658764600977)
        ·
          refine ⟨4537907984321744073450733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6050543979095658764600977 4537907984321744073450733)
          ·
            refine ⟨1701715494120654027544025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4537907984321744073450733 1701715494120654027544025)
            ·
              refine ⟨1276286620590490520658019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701715494120654027544025 1276286620590490520658019)
              ·
                refine ⟨1914429930885735780987029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1276286620590490520658019 1914429930885735780987029)
                ·
                  refine ⟨89738903010268864733767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1914429930885735780987029 89738903010268864733767)
                  ·
                    rfl

theorem cell23_1572893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_1572893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572893 prefixEnd_1572893 := by exact prefixLift 1572893
  have htrace : WordTrace (prefixWord ++ tailWord_1572893) baseStart_1572893 baseEnd_1572893 := by
    simpa [prefixWord, tailWord_1572893, baseEnd_1572893] using wordTrace_append hprefix tailTrace_1572893
  have hstable : (prefixWord ++ tailWord_1572893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572893).length < 2 ^ (prefixWord ++ tailWord_1572893).sum := by decide
  have hdescent : baseEnd_1572893 < baseStart_1572893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572906 : List Nat := [3, 1, 4, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1572906 : Nat := 118140960795 + 1572906 * 2 ^ 59
def prefixEnd_1572906 : Nat := 4983230072969 + 3 ^ 40 * 1572906 * 2
def baseEnd_1572906 : Nat := 269218934113642743913781

theorem tailTrace_1572906 : CollatzResearch.WordTrace tailWord_1572906 prefixEnd_1572906 269218934113642743913781 := by
  unfold tailWord_1572906
  simp only [CollatzResearch.WordTrace]
  refine ⟨14342148709909416950776643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38245729893091778535404381 14342148709909416950776643)
  ·
    refine ⟨21513223064864125426164965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14342148709909416950776643 21513223064864125426164965)
    ·
      refine ⟨4033729324662023517405931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21513223064864125426164965 4033729324662023517405931)
      ·
        refine ⟨6050593986993035276108897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033729324662023517405931 6050593986993035276108897)
        ·
          refine ⟨4537945490244776457081673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6050593986993035276108897 4537945490244776457081673)
          ·
            refine ⟨3403459117683582342811255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4537945490244776457081673 3403459117683582342811255)
            ·
              refine ⟨5105188676525373514216883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403459117683582342811255 5105188676525373514216883)
              ·
                refine ⟨7657783014788060271325325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5105188676525373514216883 7657783014788060271325325)
                ·
                  refine ⟨2871668630545522601746997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7657783014788060271325325 2871668630545522601746997)
                  ·
                    refine ⟨269218934113642743913781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2871668630545522601746997 269218934113642743913781)
                    ·
                      rfl

theorem cell23_1572906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1572906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572906 prefixEnd_1572906 := by exact prefixLift 1572906
  have htrace : WordTrace (prefixWord ++ tailWord_1572906) baseStart_1572906 baseEnd_1572906 := by
    simpa [prefixWord, tailWord_1572906, baseEnd_1572906] using wordTrace_append hprefix tailTrace_1572906
  have hstable : (prefixWord ++ tailWord_1572906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572906).length < 2 ^ (prefixWord ++ tailWord_1572906).sum := by decide
  have hdescent : baseEnd_1572906 < baseStart_1572906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572913 : List Nat := [1, 2, 2, 3, 1, 4, 2, 1, 2, 3, 2]
def baseStart_1572913 : Nat := 118140960795 + 1572913 * 2 ^ 59
def prefixEnd_1572913 : Nat := 4983230072969 + 3 ^ 40 * 1572913 * 2
def baseEnd_1572913 : Nat := 807660396705509704353811

theorem tailTrace_1572913 : CollatzResearch.WordTrace tailWord_1572913 prefixEnd_1572913 807660396705509704353811 := by
  unfold tailWord_1572913
  simp only [CollatzResearch.WordTrace]
  refine ⟨57368850150612307998611393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38245900100408205332407595 57368850150612307998611393)
  ·
    refine ⟨43026637612959230998958545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57368850150612307998611393 43026637612959230998958545)
    ·
      refine ⟨32269978209719423249218909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43026637612959230998958545 32269978209719423249218909)
      ·
        refine ⟨12101241828644783718457091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32269978209719423249218909 12101241828644783718457091)
        ·
          refine ⟨18151862742967175577685637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12101241828644783718457091 18151862742967175577685637)
          ·
            refine ⟨3403474264306345420816057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18151862742967175577685637 3403474264306345420816057)
            ·
              refine ⟨2552605698229759065612043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3403474264306345420816057 2552605698229759065612043)
              ·
                refine ⟨3828908547344638598418065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2552605698229759065612043 3828908547344638598418065)
                ·
                  refine ⟨2871681410508478948813549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3828908547344638598418065 2871681410508478948813549)
                  ·
                    refine ⟨1076880528940679605805081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2871681410508478948813549 1076880528940679605805081)
                    ·
                      refine ⟨807660396705509704353811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076880528940679605805081 807660396705509704353811)
                      ·
                        rfl

theorem cell23_1572913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 1, 2, 3, 2].length) (baseStart_1572913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572913 prefixEnd_1572913 := by exact prefixLift 1572913
  have htrace : WordTrace (prefixWord ++ tailWord_1572913) baseStart_1572913 baseEnd_1572913 := by
    simpa [prefixWord, tailWord_1572913, baseEnd_1572913] using wordTrace_append hprefix tailTrace_1572913
  have hstable : (prefixWord ++ tailWord_1572913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572913).length < 2 ^ (prefixWord ++ tailWord_1572913).sum := by decide
  have hdescent : baseEnd_1572913 < baseStart_1572913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572919 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 6, 4]
def baseStart_1572919 : Nat := 118140960795 + 1572919 * 2 ^ 59
def prefixEnd_1572919 : Nat := 4983230072969 + 3 ^ 40 * 1572919 * 2
def baseEnd_1572919 : Nat := 269221159196478893626261

theorem tailTrace_1572919 : CollatzResearch.WordTrace tailWord_1572919 prefixEnd_1572919 269221159196478893626261 := by
  unfold tailWord_1572919
  simp only [CollatzResearch.WordTrace]
  refine ⟨57369068988590571023329811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38246045992393714015553207 57369068988590571023329811)
  ·
    refine ⟨86053603482885856534994717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57369068988590571023329811 86053603482885856534994717)
    ·
      refine ⟨32270101306082196200623019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86053603482885856534994717 32270101306082196200623019)
      ·
        refine ⟨48405151959123294300934529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32270101306082196200623019 48405151959123294300934529)
        ·
          refine ⟨36303863969342470725700897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48405151959123294300934529 36303863969342470725700897)
          ·
            refine ⟨27227897977006853044275673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36303863969342470725700897 27227897977006853044275673)
            ·
              refine ⟨20420923482755139783206755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27227897977006853044275673 20420923482755139783206755)
              ·
                refine ⟨30631385224132709674810133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20420923482755139783206755 30631385224132709674810133)
                ·
                  refine ⟨1435846182381220766006725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 30631385224132709674810133 1435846182381220766006725)
                  ·
                    refine ⟨269221159196478893626261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1435846182381220766006725 269221159196478893626261)
                    ·
                      rfl

theorem cell23_1572919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 6, 4].length) (baseStart_1572919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572919 prefixEnd_1572919 := by exact prefixLift 1572919
  have htrace : WordTrace (prefixWord ++ tailWord_1572919) baseStart_1572919 baseEnd_1572919 := by
    simpa [prefixWord, tailWord_1572919, baseEnd_1572919] using wordTrace_append hprefix tailTrace_1572919
  have hstable : (prefixWord ++ tailWord_1572919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572919).length < 2 ^ (prefixWord ++ tailWord_1572919).sum := by decide
  have hdescent : baseEnd_1572919 < baseStart_1572919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572932 : List Nat := [2, 3, 18]
def baseStart_1572932 : Nat := 118140960795 + 1572932 * 2 ^ 59
def prefixEnd_1572932 : Nat := 4983230072969 + 3 ^ 40 * 1572932 * 2
def baseEnd_1572932 : Nat := 123101684627030198143

theorem tailTrace_1572932 : CollatzResearch.WordTrace tailWord_1572932 prefixEnd_1572932 123101684627030198143 := by
  unfold tailWord_1572932
  simp only [CollatzResearch.WordTrace]
  refine ⟨28684771568771737121776525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38246362091695649495702033 28684771568771737121776525)
  ·
    refine ⟨10756789338289401420666197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28684771568771737121776525 10756789338289401420666197)
    ·
      refine ⟨123101684627030198143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 18 10756789338289401420666197 123101684627030198143)
      ·
        rfl

theorem cell23_1572932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 18].length) (baseStart_1572932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572932 prefixEnd_1572932 := by exact prefixLift 1572932
  have htrace : WordTrace (prefixWord ++ tailWord_1572932) baseStart_1572932 baseEnd_1572932 := by
    simpa [prefixWord, tailWord_1572932, baseEnd_1572932] using wordTrace_append hprefix tailTrace_1572932
  have hstable : (prefixWord ++ tailWord_1572932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572932).length < 2 ^ (prefixWord ++ tailWord_1572932).sum := by decide
  have hdescent : baseEnd_1572932 < baseStart_1572932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572949 : List Nat := [1, 3, 2, 2, 1, 3, 3, 8]
def baseStart_1572949 : Nat := 118140960795 + 1572949 * 2 ^ 59
def prefixEnd_1572949 : Nat := 4983230072969 + 3 ^ 40 * 1572949 * 2
def baseEnd_1572949 : Nat := 29914032667002650500135

theorem tailTrace_1572949 : CollatzResearch.WordTrace tailWord_1572949 prefixEnd_1572949 29914032667002650500135 := by
  unfold tailWord_1572949
  simp only [CollatzResearch.WordTrace]
  refine ⟨57370163178481886146921901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38246775452321257431281267 57370163178481886146921901)
  ·
    refine ⟨21513811191930707305095713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57370163178481886146921901 21513811191930707305095713)
    ·
      refine ⟨16135358393948030478821785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21513811191930707305095713 16135358393948030478821785)
      ·
        refine ⟨12101518795461022859116339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16135358393948030478821785 12101518795461022859116339)
        ·
          refine ⟨18152278193191534288674509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12101518795461022859116339 18152278193191534288674509)
          ·
            refine ⟨6807104322446825358252941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18152278193191534288674509 6807104322446825358252941)
            ·
              refine ⟨2552664120917559509344853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6807104322446825358252941 2552664120917559509344853)
              ·
                refine ⟨29914032667002650500135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2552664120917559509344853 29914032667002650500135)
                ·
                  rfl

theorem cell23_1572949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 8].length) (baseStart_1572949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572949 prefixEnd_1572949 := by exact prefixLift 1572949
  have htrace : WordTrace (prefixWord ++ tailWord_1572949) baseStart_1572949 baseEnd_1572949 := by
    simpa [prefixWord, tailWord_1572949, baseEnd_1572949] using wordTrace_append hprefix tailTrace_1572949
  have hstable : (prefixWord ++ tailWord_1572949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572949).length < 2 ^ (prefixWord ++ tailWord_1572949).sum := by decide
  have hdescent : baseEnd_1572949 < baseStart_1572949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572956 : List Nat := [2, 2, 4, 1, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1572956 : Nat := 118140960795 + 1572956 * 2 ^ 59
def prefixEnd_1572956 : Nat := 4983230072969 + 3 ^ 40 * 1572956 * 2
def baseEnd_1572956 : Nat := 807682476373653036116113

theorem tailTrace_1572956 : CollatzResearch.WordTrace tailWord_1572956 prefixEnd_1572956 807682476373653036116113 := by
  unfold tailWord_1572956
  simp only [CollatzResearch.WordTrace]
  refine ⟨28685209244728263171213361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38246945659637684228284481 28685209244728263171213361)
  ·
    refine ⟨21513906933546197378410021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28685209244728263171213361 21513906933546197378410021)
    ·
      refine ⟨4033857550039912008451879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21513906933546197378410021 4033857550039912008451879)
      ·
        refine ⟨6050786325059868012677819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033857550039912008451879 6050786325059868012677819)
        ·
          refine ⟨9076179487589802019016729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6050786325059868012677819 9076179487589802019016729)
          ·
            refine ⟨6807134615692351514262547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9076179487589802019016729 6807134615692351514262547)
            ·
              refine ⟨10210701923538527271393821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807134615692351514262547 10210701923538527271393821)
              ·
                refine ⟨3829013221326947726772683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10210701923538527271393821 3829013221326947726772683)
                ·
                  refine ⟨5743519831990421590159025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829013221326947726772683 5743519831990421590159025)
                  ·
                    refine ⟨4307639873992816192619269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5743519831990421590159025 4307639873992816192619269)
                    ·
                      refine ⟨807682476373653036116113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4307639873992816192619269 807682476373653036116113)
                      ·
                        rfl

theorem cell23_1572956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1572956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572956 prefixEnd_1572956 := by exact prefixLift 1572956
  have htrace : WordTrace (prefixWord ++ tailWord_1572956) baseStart_1572956 baseEnd_1572956 := by
    simpa [prefixWord, tailWord_1572956, baseEnd_1572956] using wordTrace_append hprefix tailTrace_1572956
  have hstable : (prefixWord ++ tailWord_1572956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572956).length < 2 ^ (prefixWord ++ tailWord_1572956).sum := by decide
  have hdescent : baseEnd_1572956 < baseStart_1572956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572976 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 3]
def baseStart_1572976 : Nat := 118140960795 + 1572976 * 2 ^ 59
def prefixEnd_1572976 : Nat := 4983230072969 + 3 ^ 40 * 1572976 * 2
def baseEnd_1572976 : Nat := 807692745986742957866021

theorem tailTrace_1572976 : CollatzResearch.WordTrace tailWord_1572976 prefixEnd_1572976 807692745986742957866021 := by
  unfold tailWord_1572976
  simp only [CollatzResearch.WordTrace]
  refine ⟨28685573974692034879077391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38247431966256046505436521 28685573974692034879077391)
  ·
    refine ⟨43028360962038052318616087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28685573974692034879077391 43028360962038052318616087)
    ·
      refine ⟨64542541443057078477924131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43028360962038052318616087 64542541443057078477924131)
      ·
        refine ⟨96813812164585617716886197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64542541443057078477924131 96813812164585617716886197)
        ·
          refine ⟨9076294890429901660958081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96813812164585617716886197 9076294890429901660958081)
          ·
            refine ⟨6807221167822426245718561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9076294890429901660958081 6807221167822426245718561)
            ·
              refine ⟨5105415875866819684288921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6807221167822426245718561 5105415875866819684288921)
              ·
                refine ⟨3829061906900114763216691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5105415875866819684288921 3829061906900114763216691)
                ·
                  refine ⟨5743592860350172144825037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829061906900114763216691 5743592860350172144825037)
                  ·
                    refine ⟨2153847322631314554309389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5743592860350172144825037 2153847322631314554309389)
                    ·
                      refine ⟨807692745986742957866021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2153847322631314554309389 807692745986742957866021)
                      ·
                        rfl

theorem cell23_1572976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 3, 3].length) (baseStart_1572976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572976 prefixEnd_1572976 := by exact prefixLift 1572976
  have htrace : WordTrace (prefixWord ++ tailWord_1572976) baseStart_1572976 baseEnd_1572976 := by
    simpa [prefixWord, tailWord_1572976, baseEnd_1572976] using wordTrace_append hprefix tailTrace_1572976
  have hstable : (prefixWord ++ tailWord_1572976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572976).length < 2 ^ (prefixWord ++ tailWord_1572976).sum := by decide
  have hdescent : baseEnd_1572976 < baseStart_1572976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1572999 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 4]
def baseStart_1572999 : Nat := 118140960795 + 1572999 * 2 ^ 59
def prefixEnd_1572999 : Nat := 4983230072969 + 3 ^ 40 * 1572999 * 2
def baseEnd_1572999 : Nat := 807704556041796367878415

theorem tailTrace_1572999 : CollatzResearch.WordTrace tailWord_1572999 prefixEnd_1572999 807704556041796367878415 := by
  unfold tailWord_1572999
  simp only [CollatzResearch.WordTrace]
  refine ⟨57371986828300744686242051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38247991218867163124161367 57371986828300744686242051)
  ·
    refine ⟨86057980242451117029363077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57371986828300744686242051 86057980242451117029363077)
    ·
      refine ⟨16135871295459584443005577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86057980242451117029363077 16135871295459584443005577)
      ·
        refine ⟨12101903471594688332254183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16135871295459584443005577 12101903471594688332254183)
        ·
          refine ⟨18152855207392032498381275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12101903471594688332254183 18152855207392032498381275)
          ·
            refine ⟨27229282811088048747571913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18152855207392032498381275 27229282811088048747571913)
            ·
              refine ⟨20421962108316036560678935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27229282811088048747571913 20421962108316036560678935)
              ·
                refine ⟨30632943162474054841018403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20421962108316036560678935 30632943162474054841018403)
                ·
                  refine ⟨45949414743711082261527605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30632943162474054841018403 45949414743711082261527605)
                  ·
                    refine ⟨4307757632222913962018213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 45949414743711082261527605 4307757632222913962018213)
                    ·
                      refine ⟨807704556041796367878415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4307757632222913962018213 807704556041796367878415)
                      ·
                        rfl

theorem cell23_1572999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_1572999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1572999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1572999 prefixEnd_1572999 := by exact prefixLift 1572999
  have htrace : WordTrace (prefixWord ++ tailWord_1572999) baseStart_1572999 baseEnd_1572999 := by
    simpa [prefixWord, tailWord_1572999, baseEnd_1572999] using wordTrace_append hprefix tailTrace_1572999
  have hstable : (prefixWord ++ tailWord_1572999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1572999).length < 2 ^ (prefixWord ++ tailWord_1572999).sum := by decide
  have hdescent : baseEnd_1572999 < baseStart_1572999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1572999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573020 : List Nat := [2, 2, 3, 2, 1, 1, 4, 2, 1, 3, 2]
def baseStart_1573020 : Nat := 118140960795 + 1573020 * 2 ^ 59
def prefixEnd_1573020 : Nat := 4983230072969 + 3 ^ 40 * 1573020 * 2
def baseEnd_1573020 : Nat := 807715339135540785715819

theorem tailTrace_1573020 : CollatzResearch.WordTrace tailWord_1573020 prefixEnd_1573020 807715339135540785715819 := by
  unfold tailWord_1573020
  simp only [CollatzResearch.WordTrace]
  refine ⟨28686376380612332636378257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38248501840816443515171009 28686376380612332636378257)
  ·
    refine ⟨21514782285459249477283693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28686376380612332636378257 21514782285459249477283693)
    ·
      refine ⟨8068043357047218553981385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21514782285459249477283693 8068043357047218553981385)
      ·
        refine ⟨6051032517785413915486039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8068043357047218553981385 6051032517785413915486039)
        ·
          refine ⟨9076548776678120873229059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6051032517785413915486039 9076548776678120873229059)
          ·
            refine ⟨13614823165017181309843589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9076548776678120873229059 13614823165017181309843589)
            ·
              refine ⟨2552779343440721495595673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13614823165017181309843589 2552779343440721495595673)
              ·
                refine ⟨1914584507580541121696755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2552779343440721495595673 1914584507580541121696755)
                ·
                  refine ⟨2871876761370811682545133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1914584507580541121696755 2871876761370811682545133)
                  ·
                    refine ⟨1076953785514054380954425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2871876761370811682545133 1076953785514054380954425)
                    ·
                      refine ⟨807715339135540785715819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1076953785514054380954425 807715339135540785715819)
                      ·
                        rfl

theorem cell23_1573020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_1573020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573020 prefixEnd_1573020 := by exact prefixLift 1573020
  have htrace : WordTrace (prefixWord ++ tailWord_1573020) baseStart_1573020 baseEnd_1573020 := by
    simpa [prefixWord, tailWord_1573020, baseEnd_1573020] using wordTrace_append hprefix tailTrace_1573020
  have hstable : (prefixWord ++ tailWord_1573020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573020).length < 2 ^ (prefixWord ++ tailWord_1573020).sum := by decide
  have hdescent : baseEnd_1573020 < baseStart_1573020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573049 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1573049 : Nat := 118140960795 + 1573049 * 2 ^ 59
def prefixEnd_1573049 : Nat := 4983230072969 + 3 ^ 40 * 1573049 * 2
def baseEnd_1573049 : Nat := 807730230074521172253185

theorem tailTrace_1573049 : CollatzResearch.WordTrace tailWord_1573049 prefixEnd_1573049 807730230074521172253185 := by
  unfold tailWord_1573049
  simp only [CollatzResearch.WordTrace]
  refine ⟨57373810478119603225562201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38249206985413068817041467 57373810478119603225562201)
  ·
    refine ⟨43030357858589702419171651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57373810478119603225562201 43030357858589702419171651)
    ·
      refine ⟨64545536787884553628757477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43030357858589702419171651 64545536787884553628757477)
      ·
        refine ⟨12102288147728353805392027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64545536787884553628757477 12102288147728353805392027)
        ·
          refine ⟨18153432221592530708088041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12102288147728353805392027 18153432221592530708088041)
          ·
            refine ⟨13615074166194398031066031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18153432221592530708088041 13615074166194398031066031)
            ·
              refine ⟨20422611249291597046599047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13615074166194398031066031 20422611249291597046599047)
              ·
                refine ⟨30633916873937395569898571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20422611249291597046599047 30633916873937395569898571)
                ·
                  refine ⟨45950875310906093354847857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30633916873937395569898571 45950875310906093354847857)
                  ·
                    refine ⟨34463156483179570016135893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 45950875310906093354847857 34463156483179570016135893)
                    ·
                      refine ⟨807730230074521172253185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34463156483179570016135893 807730230074521172253185)
                      ·
                        rfl

theorem cell23_1573049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1573049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573049 prefixEnd_1573049 := by exact prefixLift 1573049
  have htrace : WordTrace (prefixWord ++ tailWord_1573049) baseStart_1573049 baseEnd_1573049 := by
    simpa [prefixWord, tailWord_1573049, baseEnd_1573049] using wordTrace_append hprefix tailTrace_1573049
  have hstable : (prefixWord ++ tailWord_1573049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573049).length < 2 ^ (prefixWord ++ tailWord_1573049).sum := by decide
  have hdescent : baseEnd_1573049 < baseStart_1573049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573056 : List Nat := [2, 1, 1, 2, 5, 1, 3, 1, 7]
def baseStart_1573056 : Nat := 118140960795 + 1573056 * 2 ^ 59
def prefixEnd_1573056 : Nat := 4983230072969 + 3 ^ 40 * 1573056 * 2
def baseEnd_1573056 : Nat := 89748202715455849429517

theorem tailTrace_1573056 : CollatzResearch.WordTrace tailWord_1573056 prefixEnd_1573056 89748202715455849429517 := by
  unfold tailWord_1573056
  simp only [CollatzResearch.WordTrace]
  refine ⟨28687032894547121710533511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38249377192729495614044681 28687032894547121710533511)
  ·
    refine ⟨43030549341820682565800267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28687032894547121710533511 43030549341820682565800267)
    ·
      refine ⟨64545824012731023848700401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43030549341820682565800267 64545824012731023848700401)
      ·
        refine ⟨48409368009548267886525301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64545824012731023848700401 48409368009548267886525301)
        ·
          refine ⟨4538378250895150114361747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48409368009548267886525301 4538378250895150114361747)
          ·
            refine ⟨6807567376342725171542621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4538378250895150114361747 6807567376342725171542621)
            ·
              refine ⟨2552837766128521939328483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6807567376342725171542621 2552837766128521939328483)
              ·
                refine ⟨3829256649192782908992725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2552837766128521939328483 3829256649192782908992725)
                ·
                  refine ⟨89748202715455849429517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3829256649192782908992725 89748202715455849429517)
                  ·
                    rfl

theorem cell23_1573056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 1, 7].length) (baseStart_1573056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573056 prefixEnd_1573056 := by exact prefixLift 1573056
  have htrace : WordTrace (prefixWord ++ tailWord_1573056) baseStart_1573056 baseEnd_1573056 := by
    simpa [prefixWord, tailWord_1573056, baseEnd_1573056] using wordTrace_append hprefix tailTrace_1573056
  have hstable : (prefixWord ++ tailWord_1573056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573056).length < 2 ^ (prefixWord ++ tailWord_1573056).sum := by decide
  have hdescent : baseEnd_1573056 < baseStart_1573056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573066 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 1, 5, 3]
def baseStart_1573066 : Nat := 118140960795 + 1573066 * 2 ^ 59
def prefixEnd_1573066 : Nat := 4983230072969 + 3 ^ 40 * 1573066 * 2
def baseEnd_1573066 : Nat := 807738959245647605740607

theorem tailTrace_1573066 : CollatzResearch.WordTrace tailWord_1573066 prefixEnd_1573066 807738959245647605740607 := by
  unfold tailWord_1573066
  simp only [CollatzResearch.WordTrace]
  refine ⟨14343607629764503782232763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38249620346038676752620701 14343607629764503782232763)
  ·
    refine ⟨21515411444646755673349145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14343607629764503782232763 21515411444646755673349145)
    ·
      refine ⟨16136558583485066755011859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21515411444646755673349145 16136558583485066755011859)
      ·
        refine ⟨24204837875227600132517789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16136558583485066755011859 24204837875227600132517789)
        ·
          refine ⟨9076814203210350049694171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24204837875227600132517789 9076814203210350049694171)
          ·
            refine ⟨13615221304815525074541257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9076814203210350049694171 13615221304815525074541257)
            ·
              refine ⟨10211415978611643805905943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13615221304815525074541257 10211415978611643805905943)
              ·
                refine ⟨15317123967917465708858915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10211415978611643805905943 15317123967917465708858915)
                ·
                  refine ⟨22975685951876198563288373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15317123967917465708858915 22975685951876198563288373)
                  ·
                    refine ⟨2153970557988393615308285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22975685951876198563288373 2153970557988393615308285)
                    ·
                      refine ⟨807738959245647605740607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2153970557988393615308285 807738959245647605740607)
                      ·
                        rfl

theorem cell23_1573066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 5, 3].length) (baseStart_1573066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573066 prefixEnd_1573066 := by exact prefixLift 1573066
  have htrace : WordTrace (prefixWord ++ tailWord_1573066) baseStart_1573066 baseEnd_1573066 := by
    simpa [prefixWord, tailWord_1573066, baseEnd_1573066] using wordTrace_append hprefix tailTrace_1573066
  have hstable : (prefixWord ++ tailWord_1573066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573066).length < 2 ^ (prefixWord ++ tailWord_1573066).sum := by decide
  have hdescent : baseEnd_1573066 < baseStart_1573066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573079 : List Nat := [1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 7]
def baseStart_1573079 : Nat := 118140960795 + 1573079 * 2 ^ 59
def prefixEnd_1573079 : Nat := 4983230072969 + 3 ^ 40 * 1573079 * 2
def baseEnd_1573079 : Nat := 807745634494156054878047

theorem tailTrace_1573079 : CollatzResearch.WordTrace tailWord_1573079 prefixEnd_1573079 807745634494156054878047 := by
  unfold tailWord_1573079
  simp only [CollatzResearch.WordTrace]
  refine ⟨57374904668010918349154291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38249936445340612232769527 57374904668010918349154291)
  ·
    refine ⟨86062357002016377523731437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57374904668010918349154291 86062357002016377523731437)
    ·
      refine ⟨32273383875756141571399289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86062357002016377523731437 32273383875756141571399289)
      ·
        refine ⟨24205037906817106178549467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32273383875756141571399289 24205037906817106178549467)
        ·
          refine ⟨36307556860225659267824201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24205037906817106178549467 36307556860225659267824201)
          ·
            refine ⟨27230667645169244450868151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36307556860225659267824201 27230667645169244450868151)
            ·
              refine ⟨40846001467753866676302227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27230667645169244450868151 40846001467753866676302227)
              ·
                refine ⟨61269002201630800014453341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40846001467753866676302227 61269002201630800014453341)
                ·
                  refine ⟨22975875825611550005420003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61269002201630800014453341 22975875825611550005420003)
                  ·
                    refine ⟨34463813738417325008130005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 22975875825611550005420003 34463813738417325008130005)
                    ·
                      refine ⟨807745634494156054878047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 34463813738417325008130005 807745634494156054878047)
                      ·
                        rfl

theorem cell23_1573079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_1573079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573079 prefixEnd_1573079 := by exact prefixLift 1573079
  have htrace : WordTrace (prefixWord ++ tailWord_1573079) baseStart_1573079 baseEnd_1573079 := by
    simpa [prefixWord, tailWord_1573079, baseEnd_1573079] using wordTrace_append hprefix tailTrace_1573079
  have hstable : (prefixWord ++ tailWord_1573079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573079).length < 2 ^ (prefixWord ++ tailWord_1573079).sum := by decide
  have hdescent : baseEnd_1573079 < baseStart_1573079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573096 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 1, 2, 5]
def baseStart_1573096 : Nat := 118140960795 + 1573096 * 2 ^ 59
def prefixEnd_1573096 : Nat := 4983230072969 + 3 ^ 40 * 1573096 * 2
def baseEnd_1573096 : Nat := 807754363665282488365469

theorem tailTrace_1573096 : CollatzResearch.WordTrace tailWord_1573096 prefixEnd_1573096 807754363665282488365469 := by
  unfold tailWord_1573096
  simp only [CollatzResearch.WordTrace]
  refine ⟨28687762354474665126261571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38250349805966220168348761 28687762354474665126261571)
  ·
    refine ⟨43031643531711997689392357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28687762354474665126261571 43031643531711997689392357)
    ·
      refine ⟨8068433162195999566761067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43031643531711997689392357 8068433162195999566761067)
      ·
        refine ⟨12102649743293999350141601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8068433162195999566761067 12102649743293999350141601)
        ·
          refine ⟨9076987307470499512606201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12102649743293999350141601 9076987307470499512606201)
          ·
            refine ⟨6807740480602874634454651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9076987307470499512606201 6807740480602874634454651)
            ·
              refine ⟨10211610720904311951681977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6807740480602874634454651 10211610720904311951681977)
              ·
                refine ⟨7658708040678233963761483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10211610720904311951681977 7658708040678233963761483)
                ·
                  refine ⟨11488062061017350945642225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7658708040678233963761483 11488062061017350945642225)
                  ·
                    refine ⟨8616046545763013209231669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11488062061017350945642225 8616046545763013209231669)
                    ·
                      refine ⟨807754363665282488365469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8616046545763013209231669 807754363665282488365469)
                      ·
                        rfl

theorem cell23_1573096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_1573096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573096 prefixEnd_1573096 := by exact prefixLift 1573096
  have htrace : WordTrace (prefixWord ++ tailWord_1573096) baseStart_1573096 baseEnd_1573096 := by
    simpa [prefixWord, tailWord_1573096, baseEnd_1573096] using wordTrace_append hprefix tailTrace_1573096
  have hstable : (prefixWord ++ tailWord_1573096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573096).length < 2 ^ (prefixWord ++ tailWord_1573096).sum := by decide
  have hdescent : baseEnd_1573096 < baseStart_1573096 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573123 : List Nat := [1, 1, 1, 3, 2, 3, 3, 1, 2, 4, 2]
def baseStart_1573123 : Nat := 118140960795 + 1573123 * 2 ^ 59
def prefixEnd_1573123 : Nat := 4983230072969 + 3 ^ 40 * 1573123 * 2
def baseEnd_1573123 : Nat := 807768227642953882727845

theorem tailTrace_1573123 : CollatzResearch.WordTrace tailWord_1573123 prefixEnd_1573123 807768227642953882727845 := by
  unfold tailWord_1573123
  simp only [CollatzResearch.WordTrace]
  refine ⟨57376509479851513863756023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38251006319901009242504015 57376509479851513863756023)
  ·
    refine ⟨86064764219777270795634035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57376509479851513863756023 86064764219777270795634035)
    ·
      refine ⟨129097146329665906193451053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86064764219777270795634035 129097146329665906193451053)
      ·
        refine ⟨48411429873624714822544145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129097146329665906193451053 48411429873624714822544145)
        ·
          refine ⟨36308572405218536116908109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48411429873624714822544145 36308572405218536116908109)
          ·
            refine ⟨13615714651956951043840541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36308572405218536116908109 13615714651956951043840541)
            ·
              refine ⟨5105892994483856641440203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13615714651956951043840541 5105892994483856641440203)
              ·
                refine ⟨7658839491725784962160305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5105892994483856641440203 7658839491725784962160305)
                ·
                  refine ⟨5744129618794338721620229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7658839491725784962160305 5744129618794338721620229)
                  ·
                    refine ⟨1077024303523938510303793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5744129618794338721620229 1077024303523938510303793)
                    ·
                      refine ⟨807768227642953882727845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077024303523938510303793 807768227642953882727845)
                      ·
                        rfl

theorem cell23_1573123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 3, 1, 2, 4, 2].length) (baseStart_1573123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573123 prefixEnd_1573123 := by exact prefixLift 1573123
  have htrace : WordTrace (prefixWord ++ tailWord_1573123) baseStart_1573123 baseEnd_1573123 := by
    simpa [prefixWord, tailWord_1573123, baseEnd_1573123] using wordTrace_append hprefix tailTrace_1573123
  have hstable : (prefixWord ++ tailWord_1573123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573123).length < 2 ^ (prefixWord ++ tailWord_1573123).sum := by decide
  have hdescent : baseEnd_1573123 < baseStart_1573123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573143 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 3]
def baseStart_1573143 : Nat := 118140960795 + 1573143 * 2 ^ 59
def prefixEnd_1573143 : Nat := 4983230072969 + 3 ^ 40 * 1573143 * 2
def baseEnd_1573143 : Nat := 807778497256043804477753

theorem tailTrace_1573143 : CollatzResearch.WordTrace tailWord_1573143 prefixEnd_1573143 807778497256043804477753 := by
  unfold tailWord_1573143
  simp only [CollatzResearch.WordTrace]
  refine ⟨57377238939779057279484083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38251492626519371519656055 57377238939779057279484083)
  ·
    refine ⟨86065858409668585919226125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57377238939779057279484083 86065858409668585919226125)
    ·
      refine ⟨32274696903625719719709797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86065858409668585919226125 32274696903625719719709797)
      ·
        refine ⟨6051505669429822447445587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32274696903625719719709797 6051505669429822447445587)
        ·
          refine ⟨9077258504144733671168381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6051505669429822447445587 9077258504144733671168381)
          ·
            refine ⟨3403971939054275126688143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9077258504144733671168381 3403971939054275126688143)
            ·
              refine ⟨5105957908581412690032215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3403971939054275126688143 5105957908581412690032215)
              ·
                refine ⟨7658936862872119035048323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5105957908581412690032215 7658936862872119035048323)
                ·
                  refine ⟨11488405294308178552572485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7658936862872119035048323 11488405294308178552572485)
                  ·
                    refine ⟨2154075992682783478607341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 11488405294308178552572485 2154075992682783478607341)
                    ·
                      refine ⟨807778497256043804477753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2154075992682783478607341 807778497256043804477753)
                      ·
                        rfl

theorem cell23_1573143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_1573143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573143 prefixEnd_1573143 := by exact prefixLift 1573143
  have htrace : WordTrace (prefixWord ++ tailWord_1573143) baseStart_1573143 baseEnd_1573143 := by
    simpa [prefixWord, tailWord_1573143, baseEnd_1573143] using wordTrace_append hprefix tailTrace_1573143
  have hstable : (prefixWord ++ tailWord_1573143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573143).length < 2 ^ (prefixWord ++ tailWord_1573143).sum := by decide
  have hdescent : baseEnd_1573143 < baseStart_1573143 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573176 : List Nat := [2, 1, 2, 1, 3, 1, 2, 1, 5, 5]
def baseStart_1573176 : Nat := 118140960795 + 1573176 * 2 ^ 59
def prefixEnd_1573176 : Nat := 4983230072969 + 3 ^ 40 * 1573176 * 2
def baseEnd_1573176 : Nat := 269265147372547391788367

theorem tailTrace_1573176 : CollatzResearch.WordTrace tailWord_1573176 prefixEnd_1573176 269265147372547391788367 := by
  unfold tailWord_1573176
  simp only [CollatzResearch.WordTrace]
  refine ⟨28689221274329751957717691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38252295032439669276956921 28689221274329751957717691)
  ·
    refine ⟨43033831911494627936576537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28689221274329751957717691 43033831911494627936576537)
    ·
      refine ⟨32275373933620970952432403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43033831911494627936576537 32275373933620970952432403)
      ·
        refine ⟨48413060900431456428648605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32275373933620970952432403 48413060900431456428648605)
        ·
          refine ⟨18154897837661796160743227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48413060900431456428648605 18154897837661796160743227)
          ·
            refine ⟨27232346756492694241114841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18154897837661796160743227 27232346756492694241114841)
            ·
              refine ⟨20424260067369520680836131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27232346756492694241114841 20424260067369520680836131)
              ·
                refine ⟨30636390101054281021254197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20424260067369520680836131 30636390101054281021254197)
                ·
                  refine ⟨2872161571973838845742581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 30636390101054281021254197 2872161571973838845742581)
                  ·
                    refine ⟨269265147372547391788367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2872161571973838845742581 269265147372547391788367)
                    ·
                      rfl

theorem cell23_1573176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_1573176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573176 prefixEnd_1573176 := by exact prefixLift 1573176
  have htrace : WordTrace (prefixWord ++ tailWord_1573176) baseStart_1573176 baseEnd_1573176 := by
    simpa [prefixWord, tailWord_1573176, baseEnd_1573176] using wordTrace_append hprefix tailTrace_1573176
  have hstable : (prefixWord ++ tailWord_1573176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573176).length < 2 ^ (prefixWord ++ tailWord_1573176).sum := by decide
  have hdescent : baseEnd_1573176 < baseStart_1573176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573183 : List Nat := [1, 1, 2, 2, 4, 1, 1, 1, 3, 5, 2]
def baseStart_1573183 : Nat := 118140960795 + 1573183 * 2 ^ 59
def prefixEnd_1573183 : Nat := 4983230072969 + 3 ^ 40 * 1573183 * 2
def baseEnd_1573183 : Nat := 807799036482223647977569

theorem tailTrace_1573183 : CollatzResearch.WordTrace tailWord_1573183 prefixEnd_1573183 807799036482223647977569 := by
  unfold tailWord_1573183
  simp only [CollatzResearch.WordTrace]
  refine ⟨57378697859634144110940203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38252465239756096073960135 57378697859634144110940203)
  ·
    refine ⟨86068046789451216166410305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57378697859634144110940203 86068046789451216166410305)
    ·
      refine ⟨64551035092088412124807729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86068046789451216166410305 64551035092088412124807729)
      ·
        refine ⟨48413276319066309093605797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64551035092088412124807729 48413276319066309093605797)
        ·
          refine ⟨9077489309824932955051087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48413276319066309093605797 9077489309824932955051087)
          ·
            refine ⟨13616233964737399432576631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9077489309824932955051087 13616233964737399432576631)
            ·
              refine ⟨20424350947106099148864947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13616233964737399432576631 20424350947106099148864947)
              ·
                refine ⟨30636526420659148723297421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20424350947106099148864947 30636526420659148723297421)
                ·
                  refine ⟨11488697407747180771236533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30636526420659148723297421 11488697407747180771236533)
                  ·
                    refine ⟨1077065381976298197303425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11488697407747180771236533 1077065381976298197303425)
                    ·
                      refine ⟨807799036482223647977569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077065381976298197303425 807799036482223647977569)
                      ·
                        rfl

theorem cell23_1573183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 1, 3, 5, 2].length) (baseStart_1573183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573183 prefixEnd_1573183 := by exact prefixLift 1573183
  have htrace : WordTrace (prefixWord ++ tailWord_1573183) baseStart_1573183 baseEnd_1573183 := by
    simpa [prefixWord, tailWord_1573183, baseEnd_1573183] using wordTrace_append hprefix tailTrace_1573183
  have hstable : (prefixWord ++ tailWord_1573183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573183).length < 2 ^ (prefixWord ++ tailWord_1573183).sum := by decide
  have hdescent : baseEnd_1573183 < baseStart_1573183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573233 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 3, 2, 3]
def baseStart_1573233 : Nat := 118140960795 + 1573233 * 2 ^ 59
def prefixEnd_1573233 : Nat := 4983230072969 + 3 ^ 40 * 1573233 * 2
def baseEnd_1573233 : Nat := 807824710514948452352339

theorem tailTrace_1573233 : CollatzResearch.WordTrace tailWord_1573233 prefixEnd_1573233 807824710514948452352339 := by
  unfold tailWord_1573233
  simp only [CollatzResearch.WordTrace]
  refine ⟨57380521509453002650260353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38253681006302001766840235 57380521509453002650260353)
  ·
    refine ⟨43035391132089751987695265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57380521509453002650260353 43035391132089751987695265)
    ·
      refine ⟨32276543349067313990771449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43035391132089751987695265 32276543349067313990771449)
      ·
        refine ⟨24207407511800485493078587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32276543349067313990771449 24207407511800485493078587)
        ·
          refine ⟨36311111267700728239617881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24207407511800485493078587 36311111267700728239617881)
          ·
            refine ⟨27233333450775546179713411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36311111267700728239617881 27233333450775546179713411)
            ·
              refine ⟨40850000176163319269570117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27233333450775546179713411 40850000176163319269570117)
              ·
                refine ⟨7659375033030622363044397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40850000176163319269570117 7659375033030622363044397)
                ·
                  refine ⟨2872265637386483386141649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7659375033030622363044397 2872265637386483386141649)
                  ·
                    refine ⟨2154199228039862539606237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2872265637386483386141649 2154199228039862539606237)
                    ·
                      refine ⟨807824710514948452352339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2154199228039862539606237 807824710514948452352339)
                      ·
                        rfl

theorem cell23_1573233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 2, 3].length) (baseStart_1573233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573233 prefixEnd_1573233 := by exact prefixLift 1573233
  have htrace : WordTrace (prefixWord ++ tailWord_1573233) baseStart_1573233 baseEnd_1573233 := by
    simpa [prefixWord, tailWord_1573233, baseEnd_1573233] using wordTrace_append hprefix tailTrace_1573233
  have hstable : (prefixWord ++ tailWord_1573233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573233).length < 2 ^ (prefixWord ++ tailWord_1573233).sum := by decide
  have hdescent : baseEnd_1573233 < baseStart_1573233 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573297 : List Nat := [1, 2, 2, 4, 1, 2, 2, 3, 2, 1, 3]
def baseStart_1573297 : Nat := 118140960795 + 1573297 * 2 ^ 59
def prefixEnd_1573297 : Nat := 4983230072969 + 3 ^ 40 * 1573297 * 2
def baseEnd_1573297 : Nat := 807857573276836201952045

theorem tailTrace_1573297 : CollatzResearch.WordTrace tailWord_1573297 prefixEnd_1573297 807857573276836201952045 := by
  unfold tailWord_1573297
  simp only [CollatzResearch.WordTrace]
  refine ⟨57382855781221141580590145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38255237187480761053726763 57382855781221141580590145)
  ·
    refine ⟨43037141835915856185442609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57382855781221141580590145 43037141835915856185442609)
    ·
      refine ⟨32277856376936892139081957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43037141835915856185442609 32277856376936892139081957)
      ·
        refine ⟨6052098070675667276077867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32277856376936892139081957 6052098070675667276077867)
        ·
          refine ⟨9078147106013500914116801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6052098070675667276077867 9078147106013500914116801)
          ·
            refine ⟨6808610329510125685587601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9078147106013500914116801 6808610329510125685587601)
            ·
              refine ⟨5106457747132594264190701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6808610329510125685587601 5106457747132594264190701)
              ·
                refine ⟨1914921655174722849071513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5106457747132594264190701 1914921655174722849071513)
                ·
                  refine ⟨1436191241381042136803635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1914921655174722849071513 1436191241381042136803635)
                  ·
                    refine ⟨2154286862071563205205453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1436191241381042136803635 2154286862071563205205453)
                    ·
                      refine ⟨807857573276836201952045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2154286862071563205205453 807857573276836201952045)
                      ·
                        rfl

theorem cell23_1573297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 1, 3].length) (baseStart_1573297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573297 prefixEnd_1573297 := by exact prefixLift 1573297
  have htrace : WordTrace (prefixWord ++ tailWord_1573297) baseStart_1573297 baseEnd_1573297 := by
    simpa [prefixWord, tailWord_1573297, baseEnd_1573297] using wordTrace_append hprefix tailTrace_1573297
  have hstable : (prefixWord ++ tailWord_1573297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573297).length < 2 ^ (prefixWord ++ tailWord_1573297).sum := by decide
  have hdescent : baseEnd_1573297 < baseStart_1573297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573324 : List Nat := [2, 2, 1, 4, 3, 1, 1, 3, 1, 3, 2]
def baseStart_1573324 : Nat := 118140960795 + 1573324 * 2 ^ 59
def prefixEnd_1573324 : Nat := 4983230072969 + 3 ^ 40 * 1573324 * 2
def baseEnd_1573324 : Nat := 807871437254507596314421

theorem tailTrace_1573324 : CollatzResearch.WordTrace tailWord_1573324 prefixEnd_1573324 807871437254507596314421 := by
  unfold tailWord_1573324
  simp only [CollatzResearch.WordTrace]
  refine ⟨28691920276061662595911513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38255893701415550127882017 28691920276061662595911513)
  ·
    refine ⟨21518940207046246946933635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28691920276061662595911513 21518940207046246946933635)
    ·
      refine ⟨32278410310569370420400453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21518940207046246946933635 32278410310569370420400453)
      ·
        refine ⟨6052201933231756953825085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32278410310569370420400453 6052201933231756953825085)
        ·
          refine ⟨2269575724961908857684407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6052201933231756953825085 2269575724961908857684407)
          ·
            refine ⟨3404363587442863286526611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2269575724961908857684407 3404363587442863286526611)
            ·
              refine ⟨5106545381164294929789917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404363587442863286526611 5106545381164294929789917)
              ·
                refine ⟨1914954517936610598671219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5106545381164294929789917 1914954517936610598671219)
                ·
                  refine ⟨2872431776904915898006829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1914954517936610598671219 2872431776904915898006829)
                  ·
                    refine ⟨1077161916339343461752561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2872431776904915898006829 1077161916339343461752561)
                    ·
                      refine ⟨807871437254507596314421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077161916339343461752561 807871437254507596314421)
                      ·
                        rfl

theorem cell23_1573324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_1573324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573324 prefixEnd_1573324 := by exact prefixLift 1573324
  have htrace : WordTrace (prefixWord ++ tailWord_1573324) baseStart_1573324 baseEnd_1573324 := by
    simpa [prefixWord, tailWord_1573324, baseEnd_1573324] using wordTrace_append hprefix tailTrace_1573324
  have hstable : (prefixWord ++ tailWord_1573324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573324).length < 2 ^ (prefixWord ++ tailWord_1573324).sum := by decide
  have hdescent : baseEnd_1573324 < baseStart_1573324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573337 : List Nat := [1, 2, 1, 2, 4, 1, 3, 1, 4, 2, 2]
def baseStart_1573337 : Nat := 118140960795 + 1573337 * 2 ^ 59
def prefixEnd_1573337 : Nat := 4983230072969 + 3 ^ 40 * 1573337 * 2
def baseEnd_1573337 : Nat := 807878112503016045451861

theorem tailTrace_1573337 : CollatzResearch.WordTrace tailWord_1573337 prefixEnd_1573337 807878112503016045451861 := by
  unfold tailWord_1573337
  simp only [CollatzResearch.WordTrace]
  refine ⟨57384314701076228412046265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38256209800717485608030843 57384314701076228412046265)
  ·
    refine ⟨43038236025807171309034699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57384314701076228412046265 43038236025807171309034699)
    ·
      refine ⟨64557354038710756963552049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43038236025807171309034699 64557354038710756963552049)
      ·
        refine ⟨48418015529033067722664037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64557354038710756963552049 48418015529033067722664037)
        ·
          refine ⟨9078377911693700197999507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48418015529033067722664037 9078377911693700197999507)
          ·
            refine ⟨13617566867540550296999261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9078377911693700197999507 13617566867540550296999261)
            ·
              refine ⟨5106587575327706361374723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13617566867540550296999261 5106587575327706361374723)
              ·
                refine ⟨7659881362991559542062085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5106587575327706361374723 7659881362991559542062085)
                ·
                  refine ⟨1436227755560917414136641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7659881362991559542062085 1436227755560917414136641)
                  ·
                    refine ⟨1077170816670688060602481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1436227755560917414136641 1077170816670688060602481)
                    ·
                      refine ⟨807878112503016045451861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077170816670688060602481 807878112503016045451861)
                      ·
                        rfl

theorem cell23_1573337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 3, 1, 4, 2, 2].length) (baseStart_1573337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573337 prefixEnd_1573337 := by exact prefixLift 1573337
  have htrace : WordTrace (prefixWord ++ tailWord_1573337) baseStart_1573337 baseEnd_1573337 := by
    simpa [prefixWord, tailWord_1573337, baseEnd_1573337] using wordTrace_append hprefix tailTrace_1573337
  have hstable : (prefixWord ++ tailWord_1573337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573337).length < 2 ^ (prefixWord ++ tailWord_1573337).sum := by decide
  have hdescent : baseEnd_1573337 < baseStart_1573337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573343 : List Nat := [1, 1, 2, 3, 3, 2, 1, 3, 7]
def baseStart_1573343 : Nat := 118140960795 + 1573343 * 2 ^ 59
def prefixEnd_1573343 : Nat := 4983230072969 + 3 ^ 40 * 1573343 * 2
def baseEnd_1573343 : Nat := 89764577042993669108537

theorem tailTrace_1573343 : CollatzResearch.WordTrace tailWord_1573343 prefixEnd_1573343 89764577042993669108537 := by
  unfold tailWord_1573343
  simp only [CollatzResearch.WordTrace]
  refine ⟨57384533539054491436764683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38256355692702994291176455 57384533539054491436764683)
  ·
    refine ⟨86076800308581737155147025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57384533539054491436764683 86076800308581737155147025)
    ·
      refine ⟨64557600231436302866360269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86076800308581737155147025 64557600231436302866360269)
      ·
        refine ⟨24209100086788613574885101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64557600231436302866360269 24209100086788613574885101)
        ·
          refine ⟨9078412532545730090581913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24209100086788613574885101 9078412532545730090581913)
          ·
            refine ⟨6808809399409297567936435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9078412532545730090581913 6808809399409297567936435)
            ·
              refine ⟨10213214099113946351904653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6808809399409297567936435 10213214099113946351904653)
              ·
                refine ⟨3829955287167729881964245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10213214099113946351904653 3829955287167729881964245)
                ·
                  refine ⟨89764577042993669108537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3829955287167729881964245 89764577042993669108537)
                  ·
                    rfl

theorem cell23_1573343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 7].length) (baseStart_1573343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573343 prefixEnd_1573343 := by exact prefixLift 1573343
  have htrace : WordTrace (prefixWord ++ tailWord_1573343) baseStart_1573343 baseEnd_1573343 := by
    simpa [prefixWord, tailWord_1573343, baseEnd_1573343] using wordTrace_append hprefix tailTrace_1573343
  have hstable : (prefixWord ++ tailWord_1573343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573343).length < 2 ^ (prefixWord ++ tailWord_1573343).sum := by decide
  have hdescent : baseEnd_1573343 < baseStart_1573343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573353 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 1, 5, 3]
def baseStart_1573353 : Nat := 118140960795 + 1573353 * 2 ^ 59
def prefixEnd_1573353 : Nat := 4983230072969 + 3 ^ 40 * 1573353 * 2
def baseEnd_1573353 : Nat := 807886328193487982851787

theorem tailTrace_1573353 : CollatzResearch.WordTrace tailWord_1573353 prefixEnd_1573353 807886328193487982851787 := by
  unfold tailWord_1573353
  simp only [CollatzResearch.WordTrace]
  refine ⟨57384898269018263144628713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38256598846012175429752475 57384898269018263144628713)
  ·
    refine ⟨43038673701763697358471535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57384898269018263144628713 43038673701763697358471535)
    ·
      refine ⟨64558010552645546037707303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43038673701763697358471535 64558010552645546037707303)
      ·
        refine ⟨96837015828968319056560955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64558010552645546037707303 96837015828968319056560955)
        ·
          refine ⟨145255523743452478584841433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96837015828968319056560955 145255523743452478584841433)
          ·
            refine ⟨108941642807589358938631075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145255523743452478584841433 108941642807589358938631075)
            ·
              refine ⟨163412464211384038407946613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 108941642807589358938631075 163412464211384038407946613)
              ·
                refine ⟨15319918519817253600744995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163412464211384038407946613 15319918519817253600744995)
                ·
                  refine ⟨22979877779725880401117493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15319918519817253600744995 22979877779725880401117493)
                  ·
                    refine ⟨2154363541849301287604765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 22979877779725880401117493 2154363541849301287604765)
                    ·
                      refine ⟨807886328193487982851787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2154363541849301287604765 807886328193487982851787)
                      ·
                        rfl

theorem cell23_1573353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 5, 3].length) (baseStart_1573353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573353 prefixEnd_1573353 := by exact prefixLift 1573353
  have htrace : WordTrace (prefixWord ++ tailWord_1573353) baseStart_1573353 baseEnd_1573353 := by
    simpa [prefixWord, tailWord_1573353, baseEnd_1573353] using wordTrace_append hprefix tailTrace_1573353
  have hstable : (prefixWord ++ tailWord_1573353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573353).length < 2 ^ (prefixWord ++ tailWord_1573353).sum := by decide
  have hdescent : baseEnd_1573353 < baseStart_1573353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573354 : List Nat := [3, 1, 3, 1, 3, 3, 1, 1, 1, 4, 2]
def baseStart_1573354 : Nat := 118140960795 + 1573354 * 2 ^ 59
def prefixEnd_1573354 : Nat := 4983230072969 + 3 ^ 40 * 1573354 * 2
def baseEnd_1573354 : Nat := 807886841674142478939283

theorem tailTrace_1573354 : CollatzResearch.WordTrace tailWord_1573354 prefixEnd_1573354 807886841674142478939283 := by
  unfold tailWord_1573354
  simp only [CollatzResearch.WordTrace]
  refine ⟨14346233685503660078853779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38256623161343093543610077 14346233685503660078853779)
  ·
    refine ⟨21519350528255490118280669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14346233685503660078853779 21519350528255490118280669)
    ·
      refine ⟨8069756448095808794355251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21519350528255490118280669 8069756448095808794355251)
      ·
        refine ⟨12104634672143713191532877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8069756448095808794355251 12104634672143713191532877)
        ·
          refine ⟨4539238002053892446824829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12104634672143713191532877 4539238002053892446824829)
          ·
            refine ⟨1702214250770209667559311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4539238002053892446824829 1702214250770209667559311)
            ·
              refine ⟨2553321376155314501338967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702214250770209667559311 2553321376155314501338967)
              ·
                refine ⟨3829982064232971752008451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2553321376155314501338967 3829982064232971752008451)
                ·
                  refine ⟨5744973096349457628012677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3829982064232971752008451 5744973096349457628012677)
                  ·
                    refine ⟨1077182455565523305252377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5744973096349457628012677 1077182455565523305252377)
                    ·
                      refine ⟨807886841674142478939283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077182455565523305252377 807886841674142478939283)
                      ·
                        rfl

theorem cell23_1573354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 1, 1, 4, 2].length) (baseStart_1573354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573354 prefixEnd_1573354 := by exact prefixLift 1573354
  have htrace : WordTrace (prefixWord ++ tailWord_1573354) baseStart_1573354 baseEnd_1573354 := by
    simpa [prefixWord, tailWord_1573354, baseEnd_1573354] using wordTrace_append hprefix tailTrace_1573354
  have hstable : (prefixWord ++ tailWord_1573354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573354).length < 2 ^ (prefixWord ++ tailWord_1573354).sum := by decide
  have hdescent : baseEnd_1573354 < baseStart_1573354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573373 : List Nat := [1, 4, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_1573373 : Nat := 118140960795 + 1573373 * 2 ^ 59
def prefixEnd_1573373 : Nat := 4983230072969 + 3 ^ 40 * 1573373 * 2
def baseEnd_1573373 : Nat := 269298865935525968200565

theorem tailTrace_1573373 : CollatzResearch.WordTrace tailWord_1573373 prefixEnd_1573373 269298865935525968200565 := by
  unfold tailWord_1573373
  simp only [CollatzResearch.WordTrace]
  refine ⟨57385627728945806560356773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38257085152630537706904515 57385627728945806560356773)
  ·
    refine ⟨10759805199177338730066895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57385627728945806560356773 10759805199177338730066895)
    ·
      refine ⟨16139707798766008095100343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10759805199177338730066895 16139707798766008095100343)
      ·
        refine ⟨24209561698149012142650515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16139707798766008095100343 24209561698149012142650515)
        ·
          refine ⟨36314342547223518213975773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24209561698149012142650515 36314342547223518213975773)
          ·
            refine ⟨13617878455208819330240915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36314342547223518213975773 13617878455208819330240915)
            ·
              refine ⟨20426817682813228995361373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13617878455208819330240915 20426817682813228995361373)
              ·
                refine ⟨7660056631054960873260515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20426817682813228995361373 7660056631054960873260515)
                ·
                  refine ⟨11490084946582441309890773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7660056631054960873260515 11490084946582441309890773)
                  ·
                    refine ⟨269298865935525968200565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 11490084946582441309890773 269298865935525968200565)
                    ·
                      rfl

theorem cell23_1573373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_1573373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573373 prefixEnd_1573373 := by exact prefixLift 1573373
  have htrace : WordTrace (prefixWord ++ tailWord_1573373) baseStart_1573373 baseEnd_1573373 := by
    simpa [prefixWord, tailWord_1573373, baseEnd_1573373] using wordTrace_append hprefix tailTrace_1573373
  have hstable : (prefixWord ++ tailWord_1573373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573373).length < 2 ^ (prefixWord ++ tailWord_1573373).sum := by decide
  have hdescent : baseEnd_1573373 < baseStart_1573373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573377 : List Nat := [1, 2, 4, 1, 3, 1, 3, 3, 5]
def baseStart_1573377 : Nat := 118140960795 + 1573377 * 2 ^ 59
def prefixEnd_1573377 : Nat := 4983230072969 + 3 ^ 40 * 1573377 * 2
def baseEnd_1573377 : Nat := 89766516858799543216853

theorem tailTrace_1573377 : CollatzResearch.WordTrace tailWord_1573377 prefixEnd_1573377 89766516858799543216853 := by
  unfold tailWord_1573377
  simp only [CollatzResearch.WordTrace]
  refine ⟨57385773620931315243502385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38257182413954210162334923 57385773620931315243502385)
  ·
    refine ⟨43039330215698486432626789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57385773620931315243502385 43039330215698486432626789)
    ·
      refine ⟨8069874415443466206117523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 43039330215698486432626789 8069874415443466206117523)
      ·
        refine ⟨12104811623165199309176285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8069874415443466206117523 12104811623165199309176285)
        ·
          refine ⟨4539304358686949740941107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12104811623165199309176285 4539304358686949740941107)
          ·
            refine ⟨6808956538030424611411661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539304358686949740941107 6808956538030424611411661)
            ·
              refine ⟨2553358701761409229279373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6808956538030424611411661 2553358701761409229279373)
              ·
                refine ⟨957509513160528460979765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2553358701761409229279373 957509513160528460979765)
                ·
                  refine ⟨89766516858799543216853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 957509513160528460979765 89766516858799543216853)
                  ·
                    rfl

theorem cell23_1573377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 3, 5].length) (baseStart_1573377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573377 prefixEnd_1573377 := by exact prefixLift 1573377
  have htrace : WordTrace (prefixWord ++ tailWord_1573377) baseStart_1573377 baseEnd_1573377 := by
    simpa [prefixWord, tailWord_1573377, baseEnd_1573377] using wordTrace_append hprefix tailTrace_1573377
  have hstable : (prefixWord ++ tailWord_1573377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573377).length < 2 ^ (prefixWord ++ tailWord_1573377).sum := by decide
  have hdescent : baseEnd_1573377 < baseStart_1573377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573390 : List Nat := [4, 1, 1, 2, 3, 1, 1, 1, 4, 5]
def baseStart_1573390 : Nat := 118140960795 + 1573390 * 2 ^ 59
def prefixEnd_1573390 : Nat := 4983230072969 + 3 ^ 40 * 1573390 * 2
def baseEnd_1573390 : Nat := 269301775659234779363039

theorem tailTrace_1573390 : CollatzResearch.WordTrace tailWord_1573390 prefixEnd_1573390 269301775659234779363039 := by
  unfold tailWord_1573390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7173280971235527307965703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38257498513256145642483749 7173280971235527307965703)
  ·
    refine ⟨10759921456853290961948555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7173280971235527307965703 10759921456853290961948555)
    ·
      refine ⟨16139882185279936442922833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10759921456853290961948555 16139882185279936442922833)
      ·
        refine ⟨12104911638959952332192125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16139882185279936442922833 12104911638959952332192125)
        ·
          refine ⟨4539341864609982124572047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12104911638959952332192125 4539341864609982124572047)
          ·
            refine ⟨6809012796914973186858071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539341864609982124572047 6809012796914973186858071)
            ·
              refine ⟨10213519195372459780287107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6809012796914973186858071 10213519195372459780287107)
              ·
                refine ⟨15320278793058689670430661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10213519195372459780287107 15320278793058689670430661)
                ·
                  refine ⟨2872552273698504313205749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15320278793058689670430661 2872552273698504313205749)
                  ·
                    refine ⟨269301775659234779363039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2872552273698504313205749 269301775659234779363039)
                    ·
                      rfl

theorem cell23_1573390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 1, 4, 5].length) (baseStart_1573390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573390 prefixEnd_1573390 := by exact prefixLift 1573390
  have htrace : WordTrace (prefixWord ++ tailWord_1573390) baseStart_1573390 baseEnd_1573390 := by
    simpa [prefixWord, tailWord_1573390, baseEnd_1573390] using wordTrace_append hprefix tailTrace_1573390
  have hstable : (prefixWord ++ tailWord_1573390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573390).length < 2 ^ (prefixWord ++ tailWord_1573390).sum := by decide
  have hdescent : baseEnd_1573390 < baseStart_1573390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573393 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_1573393 : Nat := 118140960795 + 1573393 * 2 ^ 59
def prefixEnd_1573393 : Nat := 4983230072969 + 3 ^ 40 * 1573393 * 2
def baseEnd_1573393 : Nat := 807906867419667826351603

theorem tailTrace_1573393 : CollatzResearch.WordTrace tailWord_1573393 prefixEnd_1573393 807906867419667826351603 := by
  unfold tailWord_1573393
  simp only [CollatzResearch.WordTrace]
  refine ⟨57386357188873349976084833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38257571459248899984056555 57386357188873349976084833)
  ·
    refine ⟨43039767891655012482063625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57386357188873349976084833 43039767891655012482063625)
    ·
      refine ⟨32279825918741259361547719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43039767891655012482063625 32279825918741259361547719)
      ·
        refine ⟨48419738878111889042321579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32279825918741259361547719 48419738878111889042321579)
        ·
          refine ⟨72629608317167833563482369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48419738878111889042321579 72629608317167833563482369)
          ·
            refine ⟨54472206237875875172611777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72629608317167833563482369 54472206237875875172611777)
            ·
              refine ⟨40854154678406906379458833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54472206237875875172611777 40854154678406906379458833)
              ·
                refine ⟨30640616008805179784594125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40854154678406906379458833 30640616008805179784594125)
                ·
                  refine ⟨11490231003301942419222797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30640616008805179784594125 11490231003301942419222797)
                  ·
                    refine ⟨4308836626238228407208549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11490231003301942419222797 4308836626238228407208549)
                    ·
                      refine ⟨807906867419667826351603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4308836626238228407208549 807906867419667826351603)
                      ·
                        rfl

theorem cell23_1573393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_1573393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573393 prefixEnd_1573393 := by exact prefixLift 1573393
  have htrace : WordTrace (prefixWord ++ tailWord_1573393) baseStart_1573393 baseEnd_1573393 := by
    simpa [prefixWord, tailWord_1573393, baseEnd_1573393] using wordTrace_append hprefix tailTrace_1573393
  have hstable : (prefixWord ++ tailWord_1573393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573393).length < 2 ^ (prefixWord ++ tailWord_1573393).sum := by decide
  have hdescent : baseEnd_1573393 < baseStart_1573393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573400 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_1573400 : Nat := 118140960795 + 1573400 * 2 ^ 59
def prefixEnd_1573400 : Nat := 4983230072969 + 3 ^ 40 * 1573400 * 2
def baseEnd_1573400 : Nat := 807910461784249298964071

theorem tailTrace_1573400 : CollatzResearch.WordTrace tailWord_1573400 prefixEnd_1573400 807910461784249298964071 := by
  unfold tailWord_1573400
  simp only [CollatzResearch.WordTrace]
  refine ⟨28693306249923995085794827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38257741666565326781059769 28693306249923995085794827)
  ·
    refine ⟨43039959374885992628692241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28693306249923995085794827 43039959374885992628692241)
    ·
      refine ⟨32279969531164494471519181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43039959374885992628692241 32279969531164494471519181)
      ·
        refine ⟨12104988574186685426819693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32279969531164494471519181 12104988574186685426819693)
        ·
          refine ⟨4539370715320007035057385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12104988574186685426819693 4539370715320007035057385)
          ·
            refine ⟨3404528036490005276293039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4539370715320007035057385 3404528036490005276293039)
            ·
              refine ⟨5106792054735007914439559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404528036490005276293039 5106792054735007914439559)
              ·
                refine ⟨7660188082102511871659339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5106792054735007914439559 7660188082102511871659339)
                ·
                  refine ⟨11490282123153767807489009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7660188082102511871659339 11490282123153767807489009)
                  ·
                    refine ⟨8617711592365325855616757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11490282123153767807489009 8617711592365325855616757)
                    ·
                      refine ⟨807910461784249298964071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8617711592365325855616757 807910461784249298964071)
                      ·
                        rfl

theorem cell23_1573400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_1573400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573400 prefixEnd_1573400 := by exact prefixLift 1573400
  have htrace : WordTrace (prefixWord ++ tailWord_1573400) baseStart_1573400 baseEnd_1573400 := by
    simpa [prefixWord, tailWord_1573400, baseEnd_1573400] using wordTrace_append hprefix tailTrace_1573400
  have hstable : (prefixWord ++ tailWord_1573400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573400).length < 2 ^ (prefixWord ++ tailWord_1573400).sum := by decide
  have hdescent : baseEnd_1573400 < baseStart_1573400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573410 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_1573410 : Nat := 118140960795 + 1573410 * 2 ^ 59
def prefixEnd_1573410 : Nat := 4983230072969 + 3 ^ 40 * 1573410 * 2
def baseEnd_1573410 : Nat := 807915596590794259839025

theorem tailTrace_1573410 : CollatzResearch.WordTrace tailWord_1573410 prefixEnd_1573410 807915596590794259839025 := by
  unfold tailWord_1573410
  simp only [CollatzResearch.WordTrace]
  refine ⟨14346744307452940469863421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38257984819874507919635789 14346744307452940469863421)
  ·
    refine ⟨5380029115294852676198783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14346744307452940469863421 5380029115294852676198783)
    ·
      refine ⟨8070043672942279014298175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5380029115294852676198783 8070043672942279014298175)
      ·
        refine ⟨12105065509413418521447263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8070043672942279014298175 12105065509413418521447263)
        ·
          refine ⟨18157598264120127782170895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12105065509413418521447263 18157598264120127782170895)
          ·
            refine ⟨27236397396180191673256343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18157598264120127782170895 27236397396180191673256343)
            ·
              refine ⟨40854596094270287509884515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27236397396180191673256343 40854596094270287509884515)
              ·
                refine ⟨61281894141405431264826773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40854596094270287509884515 61281894141405431264826773)
                ·
                  refine ⟨2872588787878379590538755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 61281894141405431264826773 2872588787878379590538755)
                  ·
                    refine ⟨4308883181817569385808133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2872588787878379590538755 4308883181817569385808133)
                    ·
                      refine ⟨807915596590794259839025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4308883181817569385808133 807915596590794259839025)
                      ·
                        rfl

theorem cell23_1573410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_1573410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573410 prefixEnd_1573410 := by exact prefixLift 1573410
  have htrace : WordTrace (prefixWord ++ tailWord_1573410) baseStart_1573410 baseEnd_1573410 := by
    simpa [prefixWord, tailWord_1573410, baseEnd_1573410] using wordTrace_append hprefix tailTrace_1573410
  have hstable : (prefixWord ++ tailWord_1573410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573410).length < 2 ^ (prefixWord ++ tailWord_1573410).sum := by decide
  have hdescent : baseEnd_1573410 < baseStart_1573410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573420 : List Nat := [2, 2, 1, 1, 1, 2, 1, 6, 3, 4]
def baseStart_1573420 : Nat := 118140960795 + 1573420 * 2 ^ 59
def prefixEnd_1573420 : Nat := 4983230072969 + 3 ^ 40 * 1573420 * 2
def baseEnd_1573420 : Nat := 269306910465779740237993

theorem tailTrace_1573420 : CollatzResearch.WordTrace tailWord_1573420 prefixEnd_1573420 269306910465779740237993 := by
  unfold tailWord_1573420
  simp only [CollatzResearch.WordTrace]
  refine ⟨28693670979887766793658857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38258227973183689058211809 28693670979887766793658857)
  ·
    refine ⟨21520253234915825095244143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28693670979887766793658857 21520253234915825095244143)
    ·
      refine ⟨32280379852373737642866215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21520253234915825095244143 32280379852373737642866215)
      ·
        refine ⟨48420569778560606464299323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32280379852373737642866215 48420569778560606464299323)
        ·
          refine ⟨72630854667840909696448985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48420569778560606464299323 72630854667840909696448985)
          ·
            refine ⟨54473141000880682272336739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72630854667840909696448985 54473141000880682272336739)
            ·
              refine ⟨81709711501321023408505109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54473141000880682272336739 81709711501321023408505109)
              ·
                refine ⟨3830142726624422972273677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81709711501321023408505109 3830142726624422972273677)
                ·
                  refine ⟨1436303522484158614602629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3830142726624422972273677 1436303522484158614602629)
                  ·
                    refine ⟨269306910465779740237993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1436303522484158614602629 269306910465779740237993)
                    ·
                      rfl

theorem cell23_1573420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 3, 4].length) (baseStart_1573420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573420 prefixEnd_1573420 := by exact prefixLift 1573420
  have htrace : WordTrace (prefixWord ++ tailWord_1573420) baseStart_1573420 baseEnd_1573420 := by
    simpa [prefixWord, tailWord_1573420, baseEnd_1573420] using wordTrace_append hprefix tailTrace_1573420
  have hstable : (prefixWord ++ tailWord_1573420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573420).length < 2 ^ (prefixWord ++ tailWord_1573420).sum := by decide
  have hdescent : baseEnd_1573420 < baseStart_1573420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573447 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 3]
def baseStart_1573447 : Nat := 118140960795 + 1573447 * 2 ^ 59
def prefixEnd_1573447 : Nat := 4983230072969 + 3 ^ 40 * 1573447 * 2
def baseEnd_1573447 : Nat := 807934595375010615076355

theorem tailTrace_1573447 : CollatzResearch.WordTrace tailWord_1573447 prefixEnd_1573447 807934595375010615076355 := by
  unfold tailWord_1573447
  simp only [CollatzResearch.WordTrace]
  refine ⟨57388326730677717198550595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38258884487118478132367063 57388326730677717198550595)
  ·
    refine ⟨86082490096016575797825893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57388326730677717198550595 86082490096016575797825893)
    ·
      refine ⟨16140466893003107962092355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86082490096016575797825893 16140466893003107962092355)
      ·
        refine ⟨24210700339504661943138533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16140466893003107962092355 24210700339504661943138533)
        ·
          refine ⟨4539506313657124114338475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24210700339504661943138533 4539506313657124114338475)
          ·
            refine ⟨6809259470485686171507713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4539506313657124114338475 6809259470485686171507713)
            ·
              refine ⟨5106944602864264628630785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6809259470485686171507713 5106944602864264628630785)
              ·
                refine ⟨3830208452148198471473089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5106944602864264628630785 3830208452148198471473089)
                ·
                  refine ⟨2872656339111148853604817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3830208452148198471473089 2872656339111148853604817)
                  ·
                    refine ⟨2154492254333361640203613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2872656339111148853604817 2154492254333361640203613)
                    ·
                      refine ⟨807934595375010615076355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2154492254333361640203613 807934595375010615076355)
                      ·
                        rfl

theorem cell23_1573447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 2, 3].length) (baseStart_1573447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573447 prefixEnd_1573447 := by exact prefixLift 1573447
  have htrace : WordTrace (prefixWord ++ tailWord_1573447) baseStart_1573447 baseEnd_1573447 := by
    simpa [prefixWord, tailWord_1573447, baseEnd_1573447] using wordTrace_append hprefix tailTrace_1573447
  have hstable : (prefixWord ++ tailWord_1573447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573447).length < 2 ^ (prefixWord ++ tailWord_1573447).sum := by decide
  have hdescent : baseEnd_1573447 < baseStart_1573447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573450 : List Nat := [3, 1, 2, 1, 1, 4, 1, 4, 6]
def baseStart_1573450 : Nat := 118140960795 + 1573450 * 2 ^ 59
def prefixEnd_1573450 : Nat := 4983230072969 + 3 ^ 40 * 1573450 * 2
def baseEnd_1573450 : Nat := 89770681757441567037649

theorem tailTrace_1573450 : CollatzResearch.WordTrace tailWord_1573450 prefixEnd_1573450 89770681757441567037649 := by
  unfold tailWord_1573450
  simp only [CollatzResearch.WordTrace]
  refine ⟨14347109037416712177727451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38258957433111232473939869 14347109037416712177727451)
  ·
    refine ⟨21520663556125068266591177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14347109037416712177727451 21520663556125068266591177)
    ·
      refine ⟨16140497667093801199943383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21520663556125068266591177 16140497667093801199943383)
      ·
        refine ⟨24210746500640701799915075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16140497667093801199943383 24210746500640701799915075)
        ·
          refine ⟨36316119750961052699872613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24210746500640701799915075 36316119750961052699872613)
          ·
            refine ⟨6809272453305197381226115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36316119750961052699872613 6809272453305197381226115)
            ·
              refine ⟨10213908679957796071839173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6809272453305197381226115 10213908679957796071839173)
              ·
                refine ⟨1915107877492086763469845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10213908679957796071839173 1915107877492086763469845)
                ·
                  refine ⟨89770681757441567037649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1915107877492086763469845 89770681757441567037649)
                  ·
                    rfl

theorem cell23_1573450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 4, 6].length) (baseStart_1573450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573450 prefixEnd_1573450 := by exact prefixLift 1573450
  have htrace : WordTrace (prefixWord ++ tailWord_1573450) baseStart_1573450 baseEnd_1573450 := by
    simpa [prefixWord, tailWord_1573450, baseEnd_1573450] using wordTrace_append hprefix tailTrace_1573450
  have hstable : (prefixWord ++ tailWord_1573450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573450).length < 2 ^ (prefixWord ++ tailWord_1573450).sum := by decide
  have hdescent : baseEnd_1573450 < baseStart_1573450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573497 : List Nat := [1, 2, 1, 3, 3, 3, 1, 3, 1, 5]
def baseStart_1573497 : Nat := 118140960795 + 1573497 * 2 ^ 59
def prefixEnd_1573497 : Nat := 4983230072969 + 3 ^ 40 * 1573497 * 2
def baseEnd_1573497 : Nat := 269320089802578473150375

theorem tailTrace_1573497 : CollatzResearch.WordTrace tailWord_1573497 prefixEnd_1573497 269320089802578473150375 := by
  unfold tailWord_1573497
  simp only [CollatzResearch.WordTrace]
  refine ⟨57390150380496575737870745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38260100253664383825247163 57390150380496575737870745)
  ·
    refine ⟨43042612785372431803403059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57390150380496575737870745 43042612785372431803403059)
    ·
      refine ⟨64563919178058647705104589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43042612785372431803403059 64563919178058647705104589)
      ·
        refine ⟨24211469691771992889414221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64563919178058647705104589 24211469691771992889414221)
        ·
          refine ⟨9079301134414497333530333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24211469691771992889414221 9079301134414497333530333)
          ·
            refine ⟨3404737925405436500073875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9079301134414497333530333 3404737925405436500073875)
            ·
              refine ⟨5107106888108154750110813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3404737925405436500073875 5107106888108154750110813)
              ·
                refine ⟨1915165083040558031291555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5107106888108154750110813 1915165083040558031291555)
                ·
                  refine ⟨2872747624560837046937333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915165083040558031291555 2872747624560837046937333)
                  ·
                    refine ⟨269320089802578473150375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2872747624560837046937333 269320089802578473150375)
                    ·
                      rfl

theorem cell23_1573497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 1, 3, 1, 5].length) (baseStart_1573497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573497 prefixEnd_1573497 := by exact prefixLift 1573497
  have htrace : WordTrace (prefixWord ++ tailWord_1573497) baseStart_1573497 baseEnd_1573497 := by
    simpa [prefixWord, tailWord_1573497, baseEnd_1573497] using wordTrace_append hprefix tailTrace_1573497
  have hstable : (prefixWord ++ tailWord_1573497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573497).length < 2 ^ (prefixWord ++ tailWord_1573497).sum := by decide
  have hdescent : baseEnd_1573497 < baseStart_1573497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573534 : List Nat := [4, 3, 1, 1, 1, 1, 1, 1, 2, 6, 2]
def baseStart_1573534 : Nat := 118140960795 + 1573534 * 2 ^ 59
def prefixEnd_1573534 : Nat := 4983230072969 + 3 ^ 40 * 1573534 * 2
def baseEnd_1573534 : Nat := 807979268191951774688455

theorem tailTrace_1573534 : CollatzResearch.WordTrace tailWord_1573534 prefixEnd_1573534 807979268191951774688455 := by
  unfold tailWord_1573534
  simp only [CollatzResearch.WordTrace]
  refine ⟨7173937485170316382120957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38260999920908354037978437 7173937485170316382120957)
  ·
    refine ⟨2690226556938868643295359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7173937485170316382120957 2690226556938868643295359)
    ·
      refine ⟨4035339835408302964943039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2690226556938868643295359 4035339835408302964943039)
      ·
        refine ⟨6053009753112454447414559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035339835408302964943039 6053009753112454447414559)
        ·
          refine ⟨9079514629668681671121839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6053009753112454447414559 9079514629668681671121839)
          ·
            refine ⟨13619271944503022506682759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9079514629668681671121839 13619271944503022506682759)
            ·
              refine ⟨20428907916754533760024139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13619271944503022506682759 20428907916754533760024139)
              ·
                refine ⟨30643361875131800640036209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20428907916754533760024139 30643361875131800640036209)
                ·
                  refine ⟨22982521406348850480027157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30643361875131800640036209 22982521406348850480027157)
                  ·
                    refine ⟨1077305690922602366251273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22982521406348850480027157 1077305690922602366251273)
                    ·
                      refine ⟨807979268191951774688455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077305690922602366251273 807979268191951774688455)
                      ·
                        rfl

theorem cell23_1573534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 1, 2, 6, 2].length) (baseStart_1573534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573534 prefixEnd_1573534 := by exact prefixLift 1573534
  have htrace : WordTrace (prefixWord ++ tailWord_1573534) baseStart_1573534 baseEnd_1573534 := by
    simpa [prefixWord, tailWord_1573534, baseEnd_1573534] using wordTrace_append hprefix tailTrace_1573534
  have hstable : (prefixWord ++ tailWord_1573534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573534).length < 2 ^ (prefixWord ++ tailWord_1573534).sum := by decide
  have hdescent : baseEnd_1573534 < baseStart_1573534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573540 : List Nat := [2, 3, 1, 2, 2, 1, 3, 9]
def baseStart_1573540 : Nat := 118140960795 + 1573540 * 2 ^ 59
def prefixEnd_1573540 : Nat := 4983230072969 + 3 ^ 40 * 1573540 * 2
def baseEnd_1573540 : Nat := 29925272187995509304201

theorem tailTrace_1573540 : CollatzResearch.WordTrace tailWord_1573540 prefixEnd_1573540 29925272187995509304201 := by
  unfold tailWord_1573540
  simp only [CollatzResearch.WordTrace]
  refine ⟨28695859359670397040843037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38261145812893862721124049 28695859359670397040843037)
  ·
    refine ⟨10760947259876398890316139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28695859359670397040843037 10760947259876398890316139)
    ·
      refine ⟨16141420889814598335474209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10760947259876398890316139 16141420889814598335474209)
      ·
        refine ⟨12106065667360948751605657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16141420889814598335474209 12106065667360948751605657)
        ·
          refine ⟨9079549250520711563704243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12106065667360948751605657 9079549250520711563704243)
          ·
            refine ⟨13619323875781067345556365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9079549250520711563704243 13619323875781067345556365)
            ·
              refine ⟨5107246453417900254583637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13619323875781067345556365 5107246453417900254583637)
              ·
                refine ⟨29925272187995509304201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5107246453417900254583637 29925272187995509304201)
                ·
                  rfl

theorem cell23_1573540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 9].length) (baseStart_1573540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573540 prefixEnd_1573540 := by exact prefixLift 1573540
  have htrace : WordTrace (prefixWord ++ tailWord_1573540) baseStart_1573540 baseEnd_1573540 := by
    simpa [prefixWord, tailWord_1573540, baseEnd_1573540] using wordTrace_append hprefix tailTrace_1573540
  have hstable : (prefixWord ++ tailWord_1573540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573540).length < 2 ^ (prefixWord ++ tailWord_1573540).sum := by decide
  have hdescent : baseEnd_1573540 < baseStart_1573540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573557 : List Nat := [1, 3, 3, 3, 1, 3, 9]
def baseStart_1573557 : Nat := 118140960795 + 1573557 * 2 ^ 59
def prefixEnd_1573557 : Nat := 4983230072969 + 3 ^ 40 * 1573557 * 2
def baseEnd_1573557 : Nat := 9975198496876607218529

theorem tailTrace_1573557 : CollatzResearch.WordTrace tailWord_1573557 prefixEnd_1573557 9975198496876607218529 := by
  unfold tailWord_1573557
  simp only [CollatzResearch.WordTrace]
  refine ⟨57392338760279205985054925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38261559173519470656703283 57392338760279205985054925)
  ·
    refine ⟨21522127035104702244395597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57392338760279205985054925 21522127035104702244395597)
    ·
      refine ⟨8070797638164263341648349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21522127035104702244395597 8070797638164263341648349)
      ·
        refine ⟨3026549114311598753118131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8070797638164263341648349 3026549114311598753118131)
        ·
          refine ⟨4539823671467398129677197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026549114311598753118131 4539823671467398129677197)
          ·
            refine ⟨1702433876800274298628949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4539823671467398129677197 1702433876800274298628949)
            ·
              refine ⟨9975198496876607218529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1702433876800274298628949 9975198496876607218529)
              ·
                rfl

theorem cell23_1573557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 9].length) (baseStart_1573557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573557 prefixEnd_1573557 := by exact prefixLift 1573557
  have htrace : WordTrace (prefixWord ++ tailWord_1573557) baseStart_1573557 baseEnd_1573557 := by
    simpa [prefixWord, tailWord_1573557, baseEnd_1573557] using wordTrace_append hprefix tailTrace_1573557
  have hstable : (prefixWord ++ tailWord_1573557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573557).length < 2 ^ (prefixWord ++ tailWord_1573557).sum := by decide
  have hdescent : baseEnd_1573557 < baseStart_1573557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573588 : List Nat := [2, 4, 1, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_1573588 : Nat := 118140960795 + 1573588 * 2 ^ 59
def prefixEnd_1573588 : Nat := 4983230072969 + 3 ^ 40 * 1573588 * 2
def baseEnd_1573588 : Nat := 808006996147294563413207

theorem tailTrace_1573588 : CollatzResearch.WordTrace tailWord_1573588 prefixEnd_1573588 808006996147294563413207 := by
  unfold tailWord_1573588
  simp only [CollatzResearch.WordTrace]
  refine ⟨28696734711583449139716709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38262312948777932186288945 28696734711583449139716709)
  ·
    refine ⟨5380637758421896713696883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 28696734711583449139716709 5380637758421896713696883)
    ·
      refine ⟨8070956637632845070545325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5380637758421896713696883 8070956637632845070545325)
      ·
        refine ⟨3026608739112316901454497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8070956637632845070545325 3026608739112316901454497)
        ·
          refine ⟨2269956554334237676090873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3026608739112316901454497 2269956554334237676090873)
          ·
            refine ⟨1702467415750678257068155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2269956554334237676090873 1702467415750678257068155)
            ·
              refine ⟨2553701123626017385602233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702467415750678257068155 2553701123626017385602233)
              ·
                refine ⟨1915275842719513039201675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2553701123626017385602233 1915275842719513039201675)
                ·
                  refine ⟨2872913764079269558802513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915275842719513039201675 2872913764079269558802513)
                  ·
                    refine ⟨2154685323059452169101885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2872913764079269558802513 2154685323059452169101885)
                    ·
                      refine ⟨808006996147294563413207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2154685323059452169101885 808006996147294563413207)
                      ·
                        rfl

theorem cell23_1573588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_1573588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573588 prefixEnd_1573588 := by exact prefixLift 1573588
  have htrace : WordTrace (prefixWord ++ tailWord_1573588) baseStart_1573588 baseEnd_1573588 := by
    simpa [prefixWord, tailWord_1573588, baseEnd_1573588] using wordTrace_append hprefix tailTrace_1573588
  have hstable : (prefixWord ++ tailWord_1573588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573588).length < 2 ^ (prefixWord ++ tailWord_1573588).sum := by decide
  have hdescent : baseEnd_1573588 < baseStart_1573588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573594 : List Nat := [3, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2]
def baseStart_1573594 : Nat := 118140960795 + 1573594 * 2 ^ 59
def prefixEnd_1573594 : Nat := 4983230072969 + 3 ^ 40 * 1573594 * 2
def baseEnd_1573594 : Nat := 808010077031221539938179

theorem tailTrace_1573594 : CollatzResearch.WordTrace tailWord_1573594 prefixEnd_1573594 808010077031221539938179 := by
  unfold tailWord_1573594
  simp only [CollatzResearch.WordTrace]
  refine ⟨14348422065286290326037959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38262458840763440869434557 14348422065286290326037959)
  ·
    refine ⟨21522633097929435489056939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14348422065286290326037959 21522633097929435489056939)
    ·
      refine ⟨32283949646894153233585409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21522633097929435489056939 32283949646894153233585409)
      ·
        refine ⟨24212962235170614925189057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32283949646894153233585409 24212962235170614925189057)
        ·
          refine ⟨18159721676377961193891793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24212962235170614925189057 18159721676377961193891793)
          ·
            refine ⟨13619791257283470895418845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18159721676377961193891793 13619791257283470895418845)
            ·
              refine ⟨5107421721481301585782067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13619791257283470895418845 5107421721481301585782067)
              ·
                refine ⟨7661132582221952378673101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107421721481301585782067 7661132582221952378673101)
                ·
                  refine ⟨2872924718333232142002413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7661132582221952378673101 2872924718333232142002413)
                  ·
                    refine ⟨1077346769374962053250905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2872924718333232142002413 1077346769374962053250905)
                    ·
                      refine ⟨808010077031221539938179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077346769374962053250905 808010077031221539938179)
                      ·
                        rfl

theorem cell23_1573594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_1573594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573594 prefixEnd_1573594 := by exact prefixLift 1573594
  have htrace : WordTrace (prefixWord ++ tailWord_1573594) baseStart_1573594 baseEnd_1573594 := by
    simpa [prefixWord, tailWord_1573594, baseEnd_1573594] using wordTrace_append hprefix tailTrace_1573594
  have hstable : (prefixWord ++ tailWord_1573594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573594).length < 2 ^ (prefixWord ++ tailWord_1573594).sum := by decide
  have hdescent : baseEnd_1573594 < baseStart_1573594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573600 : List Nat := [2, 1, 1, 3, 1, 2, 1, 2, 4, 6]
def baseStart_1573600 : Nat := 118140960795 + 1573600 * 2 ^ 59
def prefixEnd_1573600 : Nat := 4983230072969 + 3 ^ 40 * 1573600 * 2
def baseEnd_1573600 : Nat := 269337719305049505487717

theorem tailTrace_1573600 : CollatzResearch.WordTrace tailWord_1573600 prefixEnd_1573600 269337719305049505487717 := by
  unfold tailWord_1573600
  simp only [CollatzResearch.WordTrace]
  refine ⟨28696953549561712164435127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38262604732748949552580169 28696953549561712164435127)
  ·
    refine ⟨43045430324342568246652691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28696953549561712164435127 43045430324342568246652691)
    ·
      refine ⟨64568145486513852369979037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43045430324342568246652691 64568145486513852369979037)
      ·
        refine ⟨24213054557442694638742139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64568145486513852369979037 24213054557442694638742139)
        ·
          refine ⟨36319581836164041958113209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24213054557442694638742139 36319581836164041958113209)
          ·
            refine ⟨27239686377123031468584907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36319581836164041958113209 27239686377123031468584907)
            ·
              refine ⟨40859529565684547202877361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27239686377123031468584907 40859529565684547202877361)
              ·
                refine ⟨30644647174263410402158021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40859529565684547202877361 30644647174263410402158021)
                ·
                  refine ⟨5745871345174389450404629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30644647174263410402158021 5745871345174389450404629)
                  ·
                    refine ⟨269337719305049505487717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5745871345174389450404629 269337719305049505487717)
                    ·
                      rfl

theorem cell23_1573600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_1573600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573600 prefixEnd_1573600 := by exact prefixLift 1573600
  have htrace : WordTrace (prefixWord ++ tailWord_1573600) baseStart_1573600 baseEnd_1573600 := by
    simpa [prefixWord, tailWord_1573600, baseEnd_1573600] using wordTrace_append hprefix tailTrace_1573600
  have hstable : (prefixWord ++ tailWord_1573600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573600).length < 2 ^ (prefixWord ++ tailWord_1573600).sum := by decide
  have hdescent : baseEnd_1573600 < baseStart_1573600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573634 : List Nat := [3, 4, 1, 1, 1, 3, 1, 1, 2, 6]
def baseStart_1573634 : Nat := 118140960795 + 1573634 * 2 ^ 59
def prefixEnd_1573634 : Nat := 4983230072969 + 3 ^ 40 * 1573634 * 2
def baseEnd_1573634 : Nat := 269343538752467127812665

theorem tailTrace_1573634 : CollatzResearch.WordTrace tailWord_1573634 prefixEnd_1573634 269343538752467127812665 := by
  unfold tailWord_1573634
  simp only [CollatzResearch.WordTrace]
  refine ⟨14348786795250062033901989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38263431454000165423738637 14348786795250062033901989)
  ·
    refine ⟨2690397524109386631356623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14348786795250062033901989 2690397524109386631356623)
    ·
      refine ⟨4035596286164079947034935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2690397524109386631356623 4035596286164079947034935)
      ·
        refine ⟨6053394429246119920552403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4035596286164079947034935 6053394429246119920552403)
        ·
          refine ⟨9080091643869179880828605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6053394429246119920552403 9080091643869179880828605)
          ·
            refine ⟨3405034366450942455310727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9080091643869179880828605 3405034366450942455310727)
            ·
              refine ⟨5107551549676413682966091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3405034366450942455310727 5107551549676413682966091)
              ·
                refine ⟨7661327324514620524449137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5107551549676413682966091 7661327324514620524449137)
                ·
                  refine ⟨5745995493385965393336853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7661327324514620524449137 5745995493385965393336853)
                  ·
                    refine ⟨269343538752467127812665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5745995493385965393336853 269343538752467127812665)
                    ·
                      rfl

theorem cell23_1573634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_1573634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573634 prefixEnd_1573634 := by exact prefixLift 1573634
  have htrace : WordTrace (prefixWord ++ tailWord_1573634) baseStart_1573634 baseEnd_1573634 := by
    simpa [prefixWord, tailWord_1573634, baseEnd_1573634] using wordTrace_append hprefix tailTrace_1573634
  have hstable : (prefixWord ++ tailWord_1573634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573634).length < 2 ^ (prefixWord ++ tailWord_1573634).sum := by decide
  have hdescent : baseEnd_1573634 < baseStart_1573634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573641 : List Nat := [1, 2, 1, 1, 3, 2, 4, 3, 2, 2, 2]
def baseStart_1573641 : Nat := 118140960795 + 1573641 * 2 ^ 59
def prefixEnd_1573641 : Nat := 4983230072969 + 3 ^ 40 * 1573641 * 2
def baseEnd_1573641 : Nat := 808034210621982856050463

theorem tailTrace_1573641 : CollatzResearch.WordTrace tailWord_1573641 prefixEnd_1573641 808034210621982856050463 := by
  unfold tailWord_1573641
  simp only [CollatzResearch.WordTrace]
  refine ⟨57395402491974888331112777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38263601661316592220741851 57395402491974888331112777)
  ·
    refine ⟨43046551868981166248334583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57395402491974888331112777 43046551868981166248334583)
    ·
      refine ⟨64569827803471749372501875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43046551868981166248334583 64569827803471749372501875)
      ·
        refine ⟨96854741705207624058752813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64569827803471749372501875 96854741705207624058752813)
        ·
          refine ⟨36320528139452859022032305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96854741705207624058752813 36320528139452859022032305)
          ·
            refine ⟨27240396104589644266524229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36320528139452859022032305 27240396104589644266524229)
            ·
              refine ⟨5107574269610558299973293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27240396104589644266524229 5107574269610558299973293)
              ·
                refine ⟨1915340351103959362489985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5107574269610558299973293 1915340351103959362489985)
                ·
                  refine ⟨1436505263327969521867489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1915340351103959362489985 1436505263327969521867489)
                  ·
                    refine ⟨1077378947495977141400617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1436505263327969521867489 1077378947495977141400617)
                    ·
                      refine ⟨808034210621982856050463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1077378947495977141400617 808034210621982856050463)
                      ·
                        rfl

theorem cell23_1573641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 4, 3, 2, 2, 2].length) (baseStart_1573641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573641 prefixEnd_1573641 := by exact prefixLift 1573641
  have htrace : WordTrace (prefixWord ++ tailWord_1573641) baseStart_1573641 baseEnd_1573641 := by
    simpa [prefixWord, tailWord_1573641, baseEnd_1573641] using wordTrace_append hprefix tailTrace_1573641
  have hstable : (prefixWord ++ tailWord_1573641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573641).length < 2 ^ (prefixWord ++ tailWord_1573641).sum := by decide
  have hdescent : baseEnd_1573641 < baseStart_1573641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573664 : List Nat := [2, 1, 1, 5, 1, 2, 1, 5, 5]
def baseStart_1573664 : Nat := 118140960795 + 1573664 * 2 ^ 59
def prefixEnd_1573664 : Nat := 4983230072969 + 3 ^ 40 * 1573664 * 2
def baseEnd_1573664 : Nat := 89782891186337362895873

theorem tailTrace_1573664 : CollatzResearch.WordTrace tailWord_1573664 prefixEnd_1573664 89782891186337362895873 := by
  unfold tailWord_1573664
  simp only [CollatzResearch.WordTrace]
  refine ⟨28698120685445781629600023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 38264160913927708839466697 28698120685445781629600023)
  ·
    refine ⟨43047181028168672444400035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28698120685445781629600023 43047181028168672444400035)
    ·
      refine ⟨64570771542253008666600053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43047181028168672444400035 64570771542253008666600053)
      ·
        refine ⟨6053509832086219562493755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64570771542253008666600053 6053509832086219562493755)
        ·
          refine ⟨9080264748129329343740633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6053509832086219562493755 9080264748129329343740633)
          ·
            refine ⟨6810198561096997007805475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9080264748129329343740633 6810198561096997007805475)
            ·
              refine ⟨10215297841645495511708213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6810198561096997007805475 10215297841645495511708213)
              ·
                refine ⟨957684172654265204222645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10215297841645495511708213 957684172654265204222645)
                ·
                  refine ⟨89782891186337362895873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 957684172654265204222645 89782891186337362895873)
                  ·
                    rfl

theorem cell23_1573664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 5].length) (baseStart_1573664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573664 prefixEnd_1573664 := by exact prefixLift 1573664
  have htrace : WordTrace (prefixWord ++ tailWord_1573664) baseStart_1573664 baseEnd_1573664 := by
    simpa [prefixWord, tailWord_1573664, baseEnd_1573664] using wordTrace_append hprefix tailTrace_1573664
  have hstable : (prefixWord ++ tailWord_1573664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573664).length < 2 ^ (prefixWord ++ tailWord_1573664).sum := by decide
  have hdescent : baseEnd_1573664 < baseStart_1573664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573714 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4]
def baseStart_1573714 : Nat := 118140960795 + 1573714 * 2 ^ 59
def prefixEnd_1573714 : Nat := 4983230072969 + 3 ^ 40 * 1573714 * 2
def baseEnd_1573714 : Nat := 808071694709761070437627

theorem tailTrace_1573714 : CollatzResearch.WordTrace tailWord_1573714 prefixEnd_1573714 808071694709761070437627 := by
  unfold tailWord_1573714
  simp only [CollatzResearch.WordTrace]
  refine ⟨14349516255177605449630049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 38265376680473614532346797 14349516255177605449630049)
  ·
    refine ⟨10762137191383204087222537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14349516255177605449630049 10762137191383204087222537)
    ·
      refine ⟨8071602893537403065416903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10762137191383204087222537 8071602893537403065416903)
      ·
        refine ⟨12107404340306104598125355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8071602893537403065416903 12107404340306104598125355)
        ·
          refine ⟨18161106510459156897188033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12107404340306104598125355 18161106510459156897188033)
          ·
            refine ⟨13620829882844367672891025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18161106510459156897188033 13620829882844367672891025)
            ·
              refine ⟨10215622412133275754668269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13620829882844367672891025 10215622412133275754668269)
              ·
                refine ⟨3830858404549978408000601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10215622412133275754668269 3830858404549978408000601)
                ·
                  refine ⟨2873143803412483806000451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3830858404549978408000601 2873143803412483806000451)
                  ·
                    refine ⟨4309715705118725709000677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2873143803412483806000451 4309715705118725709000677)
                    ·
                      refine ⟨808071694709761070437627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4309715705118725709000677 808071694709761070437627)
                      ·
                        rfl

theorem cell23_1573714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_1573714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573714 prefixEnd_1573714 := by exact prefixLift 1573714
  have htrace : WordTrace (prefixWord ++ tailWord_1573714) baseStart_1573714 baseEnd_1573714 := by
    simpa [prefixWord, tailWord_1573714, baseEnd_1573714] using wordTrace_append hprefix tailTrace_1573714
  have hstable : (prefixWord ++ tailWord_1573714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573714).length < 2 ^ (prefixWord ++ tailWord_1573714).sum := by decide
  have hdescent : baseEnd_1573714 < baseStart_1573714 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573757 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 6]
def baseStart_1573757 : Nat := 118140960795 + 1573757 * 2 ^ 59
def prefixEnd_1573757 : Nat := 4983230072969 + 3 ^ 40 * 1573757 * 2
def baseEnd_1573757 : Nat := 808093774377904402199929

theorem tailTrace_1573757 : CollatzResearch.WordTrace tailWord_1573757 prefixEnd_1573757 808093774377904402199929 := by
  unfold tailWord_1573757
  simp only [CollatzResearch.WordTrace]
  refine ⟨57399633359554640142335525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 38266422239703093428223683 57399633359554640142335525)
  ·
    refine ⟨10762431254916495026687911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 57399633359554640142335525 10762431254916495026687911)
    ·
      refine ⟨16143646882374742540031867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10762431254916495026687911 16143646882374742540031867)
      ·
        refine ⟨24215470323562113810047801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16143646882374742540031867 24215470323562113810047801)
        ·
          refine ⟨18161602742671585357535851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24215470323562113810047801 18161602742671585357535851)
          ·
            refine ⟨27242404114007378036303777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18161602742671585357535851 27242404114007378036303777)
            ·
              refine ⟨20431803085505533527227833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27242404114007378036303777 20431803085505533527227833)
              ·
                refine ⟨15323852314129150145420875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20431803085505533527227833 15323852314129150145420875)
                ·
                  refine ⟨22985778471193725218131313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15323852314129150145420875 22985778471193725218131313)
                  ·
                    refine ⟨17239333853395293913598485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 22985778471193725218131313 17239333853395293913598485)
                    ·
                      refine ⟨808093774377904402199929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 17239333853395293913598485 808093774377904402199929)
                      ·
                        rfl

theorem cell23_1573757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 1, 2, 6].length) (baseStart_1573757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573757 prefixEnd_1573757 := by exact prefixLift 1573757
  have htrace : WordTrace (prefixWord ++ tailWord_1573757) baseStart_1573757 baseEnd_1573757 := by
    simpa [prefixWord, tailWord_1573757, baseEnd_1573757] using wordTrace_append hprefix tailTrace_1573757
  have hstable : (prefixWord ++ tailWord_1573757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573757).length < 2 ^ (prefixWord ++ tailWord_1573757).sum := by decide
  have hdescent : baseEnd_1573757 < baseStart_1573757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1573838 : List Nat := [4, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4]
def baseStart_1573838 : Nat := 118140960795 + 1573838 * 2 ^ 59
def prefixEnd_1573838 : Nat := 4983230072969 + 3 ^ 40 * 1573838 * 2
def baseEnd_1573838 : Nat := 808135366310918585287057

theorem tailTrace_1573838 : CollatzResearch.WordTrace tailWord_1573838 prefixEnd_1573838 808135366310918585287057 := by
  unfold tailWord_1573838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7175323459032648872004271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 38268391781507460650689445 7175323459032648872004271)
  ·
    refine ⟨10762985188548973308006407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7175323459032648872004271 10762985188548973308006407)
    ·
      refine ⟨16144477782823459962009611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10762985188548973308006407 16144477782823459962009611)
      ·
        refine ⟨24216716674235189943014417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16144477782823459962009611 24216716674235189943014417)
        ·
          refine ⟨18162537505676392457260813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24216716674235189943014417 18162537505676392457260813)
          ·
            refine ⟨6810951564628647171472805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18162537505676392457260813 6810951564628647171472805)
            ·
              refine ⟨1277053418367871344651151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6810951564628647171472805 1277053418367871344651151)
              ·
                refine ⟨1915580127551807016976727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277053418367871344651151 1915580127551807016976727)
                ·
                  refine ⟨2873370191327710525465091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1915580127551807016976727 2873370191327710525465091)
                  ·
                    refine ⟨4310055286991565788197637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2873370191327710525465091 4310055286991565788197637)
                    ·
                      refine ⟨808135366310918585287057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4310055286991565788197637 808135366310918585287057)
                      ·
                        rfl

theorem cell23_1573838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 1, 1, 4].length) (baseStart_1573838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1573838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1573838 prefixEnd_1573838 := by exact prefixLift 1573838
  have htrace : WordTrace (prefixWord ++ tailWord_1573838) baseStart_1573838 baseEnd_1573838 := by
    simpa [prefixWord, tailWord_1573838, baseEnd_1573838] using wordTrace_append hprefix tailTrace_1573838
  have hstable : (prefixWord ++ tailWord_1573838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1573838).length < 2 ^ (prefixWord ++ tailWord_1573838).sum := by decide
  have hdescent : baseEnd_1573838 < baseStart_1573838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1573838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
