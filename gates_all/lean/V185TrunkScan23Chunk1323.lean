import V185TrunkScan23Chunk1322

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7836128 : List Nat := [2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 4]
def baseStart_7836128 : Nat := 118140960795 + 7836128 * 2 ^ 59
def prefixEnd_7836128 : Nat := 4983230072969 + 3 ^ 40 * 7836128 * 2
def baseEnd_7836128 : Nat := 4023700134155222346862309

theorem tailTrace_7836128 : CollatzResearch.WordTrace tailWord_7836128 prefixEnd_7836128 4023700134155222346862309 := by
  unfold tailWord_7836128
  simp only [CollatzResearch.WordTrace]
  refine ⟨142903534077527017479838519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190538045436702689973118025 142903534077527017479838519)
  ·
    refine ⟨214355301116290526219757779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142903534077527017479838519 214355301116290526219757779)
    ·
      refine ⟨321532951674435789329636669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214355301116290526219757779 321532951674435789329636669)
      ·
        refine ⟨120574856877913420998613751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321532951674435789329636669 120574856877913420998613751)
        ·
          refine ⟨180862285316870131497920627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120574856877913420998613751 180862285316870131497920627)
          ·
            refine ⟨271293427975305197246880941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180862285316870131497920627 271293427975305197246880941)
            ·
              refine ⟨101735035490739448967580353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271293427975305197246880941 101735035490739448967580353)
              ·
                refine ⟨76301276618054586725685265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101735035490739448967580353 76301276618054586725685265)
                ·
                  refine ⟨57225957463540940044263949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76301276618054586725685265 57225957463540940044263949)
                  ·
                    refine ⟨21459734048827852516598981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57225957463540940044263949 21459734048827852516598981)
                    ·
                      refine ⟨4023700134155222346862309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21459734048827852516598981 4023700134155222346862309)
                      ·
                        rfl

theorem cell23_7836128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 4].length) (baseStart_7836128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836128 prefixEnd_7836128 := by exact prefixLift 7836128
  have htrace : WordTrace (prefixWord ++ tailWord_7836128) baseStart_7836128 baseEnd_7836128 := by
    simpa [prefixWord, tailWord_7836128, baseEnd_7836128] using wordTrace_append hprefix tailTrace_7836128
  have hstable : (prefixWord ++ tailWord_7836128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836128).length < 2 ^ (prefixWord ++ tailWord_7836128).sum := by decide
  have hdescent : baseEnd_7836128 < baseStart_7836128 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836199 : List Nat := [1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 5]
def baseStart_7836199 : Nat := 118140960795 + 7836199 * 2 ^ 59
def prefixEnd_7836199 : Nat := 4983230072969 + 3 ^ 40 * 7836199 * 2
def baseEnd_7836199 : Nat := 4023736591281691569074483

theorem tailTrace_7836199 : CollatzResearch.WordTrace tailWord_7836199 prefixEnd_7836199 4023736591281691569074483 := by
  unfold tailWord_7836199
  simp only [CollatzResearch.WordTrace]
  refine ⟨285809657737796814085511651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190539771825197876057007767 285809657737796814085511651)
  ·
    refine ⟨428714486606695221128267477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285809657737796814085511651 428714486606695221128267477)
    ·
      refine ⟨10047995779844419245193769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 428714486606695221128267477 10047995779844419245193769)
      ·
        refine ⟨7535996834883314433895327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10047995779844419245193769 7535996834883314433895327)
        ·
          refine ⟨11303995252324971650842991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7535996834883314433895327 11303995252324971650842991)
          ·
            refine ⟨16955992878487457476264487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11303995252324971650842991 16955992878487457476264487)
            ·
              refine ⟨25433989317731186214396731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16955992878487457476264487 25433989317731186214396731)
              ·
                refine ⟨38150983976596779321595097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25433989317731186214396731 38150983976596779321595097)
                ·
                  refine ⟨28613237982447584491196323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38150983976596779321595097 28613237982447584491196323)
                  ·
                    refine ⟨42919856973671376736794485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28613237982447584491196323 42919856973671376736794485)
                    ·
                      refine ⟨4023736591281691569074483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42919856973671376736794485 4023736591281691569074483)
                      ·
                        rfl

theorem cell23_7836199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_7836199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836199 prefixEnd_7836199 := by exact prefixLift 7836199
  have htrace : WordTrace (prefixWord ++ tailWord_7836199) baseStart_7836199 baseEnd_7836199 := by
    simpa [prefixWord, tailWord_7836199, baseEnd_7836199] using wordTrace_append hprefix tailTrace_7836199
  have hstable : (prefixWord ++ tailWord_7836199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836199).length < 2 ^ (prefixWord ++ tailWord_7836199).sum := by decide
  have hdescent : baseEnd_7836199 < baseStart_7836199 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836215 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 2, 5]
def baseStart_7836215 : Nat := 118140960795 + 7836215 * 2 ^ 59
def prefixEnd_7836215 : Nat := 4983230072969 + 3 ^ 40 * 7836215 * 2
def baseEnd_7836215 : Nat := 1341248268990721168824803

theorem tailTrace_7836215 : CollatzResearch.WordTrace tailWord_7836215 prefixEnd_7836215 1341248268990721168824803 := by
  unfold tailWord_7836215
  simp only [CollatzResearch.WordTrace]
  refine ⟨285810241305738848818094099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190540160870492565878729399 285810241305738848818094099)
  ·
    refine ⟨428715361958608273227141149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285810241305738848818094099 428715361958608273227141149)
    ·
      refine ⟨160768260734478102460177931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428715361958608273227141149 160768260734478102460177931)
      ·
        refine ⟨241152391101717153690266897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160768260734478102460177931 241152391101717153690266897)
        ·
          refine ⟨180864293326287865267700173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241152391101717153690266897 180864293326287865267700173)
          ·
            refine ⟨67824109997357949475387565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180864293326287865267700173 67824109997357949475387565)
            ·
              refine ⟨25434041249009231053270337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67824109997357949475387565 25434041249009231053270337)
              ·
                refine ⟨19075530936756923289952753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25434041249009231053270337 19075530936756923289952753)
                ·
                  refine ⟨14306648202567692467464565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19075530936756923289952753 14306648202567692467464565)
                  ·
                    refine ⟨1341248268990721168824803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14306648202567692467464565 1341248268990721168824803)
                    ·
                      rfl

theorem cell23_7836215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 5].length) (baseStart_7836215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836215 prefixEnd_7836215 := by exact prefixLift 7836215
  have htrace : WordTrace (prefixWord ++ tailWord_7836215) baseStart_7836215 baseEnd_7836215 := by
    simpa [prefixWord, tailWord_7836215, baseEnd_7836215] using wordTrace_append hprefix tailTrace_7836215
  have hstable : (prefixWord ++ tailWord_7836215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836215).length < 2 ^ (prefixWord ++ tailWord_7836215).sum := by decide
  have hdescent : baseEnd_7836215 < baseStart_7836215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836225 : List Nat := [1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_7836225 : Nat := 118140960795 + 7836225 * 2 ^ 59
def prefixEnd_7836225 : Nat := 4983230072969 + 3 ^ 40 * 7836225 * 2
def baseEnd_7836225 : Nat := 4023749941778708467349363

theorem tailTrace_7836225 : CollatzResearch.WordTrace tailWord_7836225 prefixEnd_7836225 4023749941778708467349363 := by
  unfold tailWord_7836225
  simp only [CollatzResearch.WordTrace]
  refine ⟨285810606035702620525958129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190540404023801747017305419 285810606035702620525958129)
  ·
    refine ⟨214357954526776965394468597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285810606035702620525958129 214357954526776965394468597)
    ·
      refine ⟨20096058236885340505731431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214357954526776965394468597 20096058236885340505731431)
      ·
        refine ⟨30144087355328010758597147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20096058236885340505731431 30144087355328010758597147)
        ·
          refine ⟨45216131032992016137895721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30144087355328010758597147 45216131032992016137895721)
          ·
            refine ⟨33912098274744012103421791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45216131032992016137895721 33912098274744012103421791)
            ·
              refine ⟨50868147412116018155132687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33912098274744012103421791 50868147412116018155132687)
              ·
                refine ⟨76302221118174027232699031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50868147412116018155132687 76302221118174027232699031)
                ·
                  refine ⟨114453331677261040849048547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76302221118174027232699031 114453331677261040849048547)
                  ·
                    refine ⟨171679997515891561273572821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114453331677261040849048547 171679997515891561273572821)
                    ·
                      refine ⟨4023749941778708467349363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171679997515891561273572821 4023749941778708467349363)
                      ·
                        rfl

theorem cell23_7836225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_7836225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836225 prefixEnd_7836225 := by exact prefixLift 7836225
  have htrace : WordTrace (prefixWord ++ tailWord_7836225) baseStart_7836225 baseEnd_7836225 := by
    simpa [prefixWord, tailWord_7836225, baseEnd_7836225] using wordTrace_append hprefix tailTrace_7836225
  have hstable : (prefixWord ++ tailWord_7836225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836225).length < 2 ^ (prefixWord ++ tailWord_7836225).sum := by decide
  have hdescent : baseEnd_7836225 < baseStart_7836225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836230 : List Nat := [6, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_7836230 : Nat := 118140960795 + 7836230 * 2 ^ 59
def prefixEnd_7836230 : Nat := 4983230072969 + 3 ^ 40 * 7836230 * 2
def baseEnd_7836230 : Nat := 4023752509181980947786841

theorem tailTrace_7836230 : CollatzResearch.WordTrace tailWord_7836230 prefixEnd_7836230 4023752509181980947786841 := by
  unfold tailWord_7836230
  simp only [CollatzResearch.WordTrace]
  refine ⟨8931587137521390824371567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190540525600456337586593429 8931587137521390824371567)
  ·
    refine ⟨13397380706282086236557351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8931587137521390824371567 13397380706282086236557351)
    ·
      refine ⟨20096071059423129354836027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13397380706282086236557351 20096071059423129354836027)
      ·
        refine ⟨30144106589134694032254041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20096071059423129354836027 30144106589134694032254041)
        ·
          refine ⟨22608079941851020524190531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30144106589134694032254041 22608079941851020524190531)
          ·
            refine ⟨33912119912776530786285797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22608079941851020524190531 33912119912776530786285797)
            ·
              refine ⟨6358522483645599522428587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33912119912776530786285797 6358522483645599522428587)
              ·
                refine ⟨9537783725468399283642881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6358522483645599522428587 9537783725468399283642881)
                ·
                  refine ⟨7153337794101299462732161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9537783725468399283642881 7153337794101299462732161)
                  ·
                    refine ⟨5365003345575974597049121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7153337794101299462732161 5365003345575974597049121)
                    ·
                      refine ⟨4023752509181980947786841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365003345575974597049121 4023752509181980947786841)
                      ·
                        rfl

theorem cell23_7836230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_7836230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836230 prefixEnd_7836230 := by exact prefixLift 7836230
  have htrace : WordTrace (prefixWord ++ tailWord_7836230) baseStart_7836230 baseEnd_7836230 := by
    simpa [prefixWord, tailWord_7836230, baseEnd_7836230] using wordTrace_append hprefix tailTrace_7836230
  have hstable : (prefixWord ++ tailWord_7836230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836230).length < 2 ^ (prefixWord ++ tailWord_7836230).sum := by decide
  have hdescent : baseEnd_7836230 < baseStart_7836230 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836255 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 3]
def baseStart_7836255 : Nat := 118140960795 + 7836255 * 2 ^ 59
def prefixEnd_7836255 : Nat := 4983230072969 + 3 ^ 40 * 7836255 * 2
def baseEnd_7836255 : Nat := 4023765346198343349974225

theorem tailTrace_7836255 : CollatzResearch.WordTrace tailWord_7836255 prefixEnd_7836255 4023765346198343349974225 := by
  unfold tailWord_7836255
  simp only [CollatzResearch.WordTrace]
  refine ⟨285811700225593935649550219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190541133483729290433033479 285811700225593935649550219)
  ·
    refine ⟨428717550338390903474325329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285811700225593935649550219 428717550338390903474325329)
    ·
      refine ⟨321538162753793177605743997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428717550338390903474325329 321538162753793177605743997)
      ·
        refine ⟨120576811032672441602153999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321538162753793177605743997 120576811032672441602153999)
        ·
          refine ⟨180865216549008662403230999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120576811032672441602153999 180865216549008662403230999)
          ·
            refine ⟨271297824823512993604846499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180865216549008662403230999 271297824823512993604846499)
            ·
              refine ⟨406946737235269490407269749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271297824823512993604846499 406946737235269490407269749)
              ·
                refine ⟨38151256615806514725681539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 406946737235269490407269749 38151256615806514725681539)
                ·
                  refine ⟨57226884923709772088522309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38151256615806514725681539 57226884923709772088522309)
                  ·
                    refine ⟨10730040923195582266597933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57226884923709772088522309 10730040923195582266597933)
                    ·
                      refine ⟨4023765346198343349974225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10730040923195582266597933 4023765346198343349974225)
                      ·
                        rfl

theorem cell23_7836255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_7836255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836255 prefixEnd_7836255 := by exact prefixLift 7836255
  have htrace : WordTrace (prefixWord ++ tailWord_7836255) baseStart_7836255 baseEnd_7836255 := by
    simpa [prefixWord, tailWord_7836255, baseEnd_7836255] using wordTrace_append hprefix tailTrace_7836255
  have hstable : (prefixWord ++ tailWord_7836255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836255).length < 2 ^ (prefixWord ++ tailWord_7836255).sum := by decide
  have hdescent : baseEnd_7836255 < baseStart_7836255 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836292 : List Nat := [2, 3, 2, 1, 3, 1, 2, 3, 6]
def baseStart_7836292 : Nat := 118140960795 + 7836292 * 2 ^ 59
def prefixEnd_7836292 : Nat := 4983230072969 + 3 ^ 40 * 7836292 * 2
def baseEnd_7836292 : Nat := 447087149442506633912395

theorem tailTrace_7836292 : CollatzResearch.WordTrace tailWord_7836292 prefixEnd_7836292 447087149442506633912395 := by
  unfold tailWord_7836292
  simp only [CollatzResearch.WordTrace]
  refine ⟨142906524863229945484323565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190542033150973260645764753 142906524863229945484323565)
  ·
    refine ⟨53589946823711229556621337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142906524863229945484323565 53589946823711229556621337)
    ·
      refine ⟨40192460117783422167466003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53589946823711229556621337 40192460117783422167466003)
      ·
        refine ⟨60288690176675133251199005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40192460117783422167466003 60288690176675133251199005)
        ·
          refine ⟨22608258816253174969199627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60288690176675133251199005 22608258816253174969199627)
          ·
            refine ⟨33912388224379762453799441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22608258816253174969199627 33912388224379762453799441)
            ·
              refine ⟨25434291168284821840349581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33912388224379762453799441 25434291168284821840349581)
              ·
                refine ⟨9537859188106808190131093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25434291168284821840349581 9537859188106808190131093)
                ·
                  refine ⟨447087149442506633912395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9537859188106808190131093 447087149442506633912395)
                  ·
                    rfl

theorem cell23_7836292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3, 6].length) (baseStart_7836292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836292 prefixEnd_7836292 := by exact prefixLift 7836292
  have htrace : WordTrace (prefixWord ++ tailWord_7836292) baseStart_7836292 baseEnd_7836292 := by
    simpa [prefixWord, tailWord_7836292, baseEnd_7836292] using wordTrace_append hprefix tailTrace_7836292
  have hstable : (prefixWord ++ tailWord_7836292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836292).length < 2 ^ (prefixWord ++ tailWord_7836292).sum := by decide
  have hdescent : baseEnd_7836292 < baseStart_7836292 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836306 : List Nat := [3, 2, 3, 1, 2, 3, 1, 1, 2, 2, 3]
def baseStart_7836306 : Nat := 118140960795 + 7836306 * 2 ^ 59
def prefixEnd_7836306 : Nat := 4983230072969 + 3 ^ 40 * 7836306 * 2
def baseEnd_7836306 : Nat := 4023791533711722650436491

theorem tailTrace_7836306 : CollatzResearch.WordTrace tailWord_7836306 prefixEnd_7836306 4023791533711722650436491 := by
  unfold tailWord_7836306
  simp only [CollatzResearch.WordTrace]
  refine ⟨71453390087102292839914193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190542373565606114239771181 71453390087102292839914193)
  ·
    refine ⟨53590042565326719629935645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71453390087102292839914193 53590042565326719629935645)
    ·
      refine ⟨20096265961997519861225867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53590042565326719629935645 20096265961997519861225867)
      ·
        refine ⟨30144398942996279791838801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20096265961997519861225867 30144398942996279791838801)
        ·
          refine ⟨22608299207247209843879101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30144398942996279791838801 22608299207247209843879101)
          ·
            refine ⟨8478112202717703691454663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22608299207247209843879101 8478112202717703691454663)
            ·
              refine ⟨12717168304076555537181995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478112202717703691454663 12717168304076555537181995)
              ·
                refine ⟨19075752456114833305772993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12717168304076555537181995 19075752456114833305772993)
                ·
                  refine ⟨14306814342086124979329745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19075752456114833305772993 14306814342086124979329745)
                  ·
                    refine ⟨10730110756564593734497309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14306814342086124979329745 10730110756564593734497309)
                    ·
                      refine ⟨4023791533711722650436491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10730110756564593734497309 4023791533711722650436491)
                      ·
                        rfl

theorem cell23_7836306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 1, 2, 2, 3].length) (baseStart_7836306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836306 prefixEnd_7836306 := by exact prefixLift 7836306
  have htrace : WordTrace (prefixWord ++ tailWord_7836306) baseStart_7836306 baseEnd_7836306 := by
    simpa [prefixWord, tailWord_7836306, baseEnd_7836306] using wordTrace_append hprefix tailTrace_7836306
  have hstable : (prefixWord ++ tailWord_7836306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836306).length < 2 ^ (prefixWord ++ tailWord_7836306).sum := by decide
  have hdescent : baseEnd_7836306 < baseStart_7836306 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836352 : List Nat := [2, 1, 1, 2, 4, 2, 3, 1, 1, 6]
def baseStart_7836352 : Nat := 118140960795 + 7836352 * 2 ^ 59
def prefixEnd_7836352 : Nat := 4983230072969 + 3 ^ 40 * 7836352 * 2
def baseEnd_7836352 : Nat := 1341271717940609823487093

theorem tailTrace_7836352 : CollatzResearch.WordTrace tailWord_7836352 prefixEnd_7836352 1341271717940609823487093 := by
  unfold tailWord_7836352
  simp only [CollatzResearch.WordTrace]
  refine ⟨142907619053121260607915655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190543492070828347477220873 142907619053121260607915655)
  ·
    refine ⟨214361428579681890911873483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142907619053121260607915655 214361428579681890911873483)
    ·
      refine ⟨321542142869522836367810225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214361428579681890911873483 321542142869522836367810225)
      ·
        refine ⟨241156607152142127275857669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321542142869522836367810225 241156607152142127275857669)
        ·
          refine ⟨45216863841026648864223313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241156607152142127275857669 45216863841026648864223313)
          ·
            refine ⟨33912647880769986648167485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45216863841026648864223313 33912647880769986648167485)
            ·
              refine ⟨12717242955288744993062807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33912647880769986648167485 12717242955288744993062807)
              ·
                refine ⟨19075864432933117489594211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12717242955288744993062807 19075864432933117489594211)
                ·
                  refine ⟨28613796649399676234391317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19075864432933117489594211 28613796649399676234391317)
                  ·
                    refine ⟨1341271717940609823487093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28613796649399676234391317 1341271717940609823487093)
                    ·
                      rfl

theorem cell23_7836352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 3, 1, 1, 6].length) (baseStart_7836352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836352 prefixEnd_7836352 := by exact prefixLift 7836352
  have htrace : WordTrace (prefixWord ++ tailWord_7836352) baseStart_7836352 baseEnd_7836352 := by
    simpa [prefixWord, tailWord_7836352, baseEnd_7836352] using wordTrace_append hprefix tailTrace_7836352
  have hstable : (prefixWord ++ tailWord_7836352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836352).length < 2 ^ (prefixWord ++ tailWord_7836352).sum := by decide
  have hdescent : baseEnd_7836352 < baseStart_7836352 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836359 : List Nat := [1, 1, 4, 1, 1, 1, 2, 3, 5, 2, 2]
def baseStart_7836359 : Nat := 118140960795 + 7836359 * 2 ^ 59
def prefixEnd_7836359 : Nat := 4983230072969 + 3 ^ 40 * 7836359 * 2
def baseEnd_7836359 : Nat := 4023818748186410943073747

theorem tailTrace_7836359 : CollatzResearch.WordTrace tailWord_7836359 prefixEnd_7836359 4023818748186410943073747 := by
  unfold tailWord_7836359
  simp only [CollatzResearch.WordTrace]
  refine ⟨285815493417217161411336131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190543662278144774274224087 285815493417217161411336131)
  ·
    refine ⟨428723240125825742117004197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285815493417217161411336131 428723240125825742117004197)
    ·
      refine ⟨80385607523592326646938287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428723240125825742117004197 80385607523592326646938287)
      ·
        refine ⟨120578411285388489970407431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80385607523592326646938287 120578411285388489970407431)
        ·
          refine ⟨180867616928082734955611147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120578411285388489970407431 180867616928082734955611147)
          ·
            refine ⟨271301425392124102433416721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180867616928082734955611147 271301425392124102433416721)
            ·
              refine ⟨203476069044093076825062541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271301425392124102433416721 203476069044093076825062541)
              ·
                refine ⟨76303525891534903809398453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203476069044093076825062541 76303525891534903809398453)
                ·
                  refine ⟨7153455552331397232131105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76303525891534903809398453 7153455552331397232131105)
                  ·
                    refine ⟨5365091664248547924098329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7153455552331397232131105 5365091664248547924098329)
                    ·
                      refine ⟨4023818748186410943073747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365091664248547924098329 4023818748186410943073747)
                      ·
                        rfl

theorem cell23_7836359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 3, 5, 2, 2].length) (baseStart_7836359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836359 prefixEnd_7836359 := by exact prefixLift 7836359
  have htrace : WordTrace (prefixWord ++ tailWord_7836359) baseStart_7836359 baseEnd_7836359 := by
    simpa [prefixWord, tailWord_7836359, baseEnd_7836359] using wordTrace_append hprefix tailTrace_7836359
  have hstable : (prefixWord ++ tailWord_7836359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836359).length < 2 ^ (prefixWord ++ tailWord_7836359).sum := by decide
  have hdescent : baseEnd_7836359 < baseStart_7836359 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836370 : List Nat := [3, 2, 2, 2, 3, 2, 1, 3, 1, 1, 3]
def baseStart_7836370 : Nat := 118140960795 + 7836370 * 2 ^ 59
def prefixEnd_7836370 : Nat := 4983230072969 + 3 ^ 40 * 7836370 * 2
def baseEnd_7836370 : Nat := 4023824396473610400036197

theorem tailTrace_7836370 : CollatzResearch.WordTrace tailWord_7836370 prefixEnd_7836370 4023824396473610400036197 := by
  unfold tailWord_7836370
  simp only [CollatzResearch.WordTrace]
  refine ⟨71453973655044327572496641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190543929746784873526657709 71453973655044327572496641)
  ·
    refine ⟨53590480241283245679372481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71453973655044327572496641 53590480241283245679372481)
    ·
      refine ⟨40192860180962434259529361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53590480241283245679372481 40192860180962434259529361)
      ·
        refine ⟨30144645135721825694647021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40192860180962434259529361 30144645135721825694647021)
        ·
          refine ⟨11304241925895684635492633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30144645135721825694647021 11304241925895684635492633)
          ·
            refine ⟨8478181444421763476619475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11304241925895684635492633 8478181444421763476619475)
            ·
              refine ⟨12717272166632645214929213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478181444421763476619475 12717272166632645214929213)
              ·
                refine ⟨4768977062487241955598455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12717272166632645214929213 4768977062487241955598455)
                ·
                  refine ⟨7153465593730862933397683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4768977062487241955598455 7153465593730862933397683)
                  ·
                    refine ⟨10730198390596294400096525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7153465593730862933397683 10730198390596294400096525)
                    ·
                      refine ⟨4023824396473610400036197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10730198390596294400096525 4023824396473610400036197)
                      ·
                        rfl

theorem cell23_7836370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 3, 1, 1, 3].length) (baseStart_7836370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836370 prefixEnd_7836370 := by exact prefixLift 7836370
  have htrace : WordTrace (prefixWord ++ tailWord_7836370) baseStart_7836370 baseEnd_7836370 := by
    simpa [prefixWord, tailWord_7836370, baseEnd_7836370] using wordTrace_append hprefix tailTrace_7836370
  have hstable : (prefixWord ++ tailWord_7836370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836370).length < 2 ^ (prefixWord ++ tailWord_7836370).sum := by decide
  have hdescent : baseEnd_7836370 < baseStart_7836370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836395 : List Nat := [1, 1, 1, 1, 2, 4, 1, 3, 2, 7]
def baseStart_7836395 : Nat := 118140960795 + 7836395 * 2 ^ 59
def prefixEnd_7836395 : Nat := 4983230072969 + 3 ^ 40 * 7836395 * 2
def baseEnd_7836395 : Nat := 1341279077829990934074527

theorem tailTrace_7836395 : CollatzResearch.WordTrace tailWord_7836395 prefixEnd_7836395 1341279077829990934074527 := by
  unfold tailWord_7836395
  simp only [CollatzResearch.WordTrace]
  refine ⟨285816806445086739559646639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190544537630057826373097759 285816806445086739559646639)
  ·
    refine ⟨428725209667630109339469959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285816806445086739559646639 428725209667630109339469959)
    ·
      refine ⟨643087814501445164009204939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428725209667630109339469959 643087814501445164009204939)
      ·
        refine ⟨964631721752167746013807409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643087814501445164009204939 964631721752167746013807409)
        ·
          refine ⟨723473791314125809510355557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964631721752167746013807409 723473791314125809510355557)
          ·
            refine ⟨135651335871398589283191667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 723473791314125809510355557 135651335871398589283191667)
            ·
              refine ⟨203477003807097883924787501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135651335871398589283191667 203477003807097883924787501)
              ·
                refine ⟨76303876427661706471795313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203477003807097883924787501 76303876427661706471795313)
                ·
                  refine ⟨57227907320746279853846485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76303876427661706471795313 57227907320746279853846485)
                  ·
                    refine ⟨1341279077829990934074527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57227907320746279853846485 1341279077829990934074527)
                    ·
                      rfl

theorem cell23_7836395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 7].length) (baseStart_7836395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836395 prefixEnd_7836395 := by exact prefixLift 7836395
  have htrace : WordTrace (prefixWord ++ tailWord_7836395) baseStart_7836395 baseEnd_7836395 := by
    simpa [prefixWord, tailWord_7836395, baseEnd_7836395] using wordTrace_append hprefix tailTrace_7836395
  have hstable : (prefixWord ++ tailWord_7836395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836395).length < 2 ^ (prefixWord ++ tailWord_7836395).sum := by decide
  have hdescent : baseEnd_7836395 < baseStart_7836395 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836415 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 8]
def baseStart_7836415 : Nat := 118140960795 + 7836415 * 2 ^ 59
def prefixEnd_7836415 : Nat := 4983230072969 + 3 ^ 40 * 7836415 * 2
def baseEnd_7836415 : Nat := 4023847503103062723973489

theorem tailTrace_7836415 : CollatzResearch.WordTrace tailWord_7836415 prefixEnd_7836415 4023847503103062723973489 := by
  unfold tailWord_7836415
  simp only [CollatzResearch.WordTrace]
  refine ⟨285817535905014282975374699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190545023936676188650249799 285817535905014282975374699)
  ·
    refine ⟨428726303857521424463062049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285817535905014282975374699 428726303857521424463062049)
    ·
      refine ⟨321544727893141068347296537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428726303857521424463062049 321544727893141068347296537)
      ·
        refine ⟨241158545919855801260472403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321544727893141068347296537 241158545919855801260472403)
        ·
          refine ⟨361737818879783701890708605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241158545919855801260472403 361737818879783701890708605)
          ·
            refine ⟨135651682079918888209015727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361737818879783701890708605 135651682079918888209015727)
            ·
              refine ⟨203477523119878332313523591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135651682079918888209015727 203477523119878332313523591)
              ·
                refine ⟨305216284679817498470285387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203477523119878332313523591 305216284679817498470285387)
                ·
                  refine ⟨457824427019726247705428081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305216284679817498470285387 457824427019726247705428081)
                  ·
                    refine ⟨343368320264794685779071061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 457824427019726247705428081 343368320264794685779071061)
                    ·
                      refine ⟨4023847503103062723973489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 343368320264794685779071061 4023847503103062723973489)
                      ·
                        rfl

theorem cell23_7836415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_7836415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836415 prefixEnd_7836415 := by exact prefixLift 7836415
  have htrace : WordTrace (prefixWord ++ tailWord_7836415) baseStart_7836415 baseEnd_7836415 := by
    simpa [prefixWord, tailWord_7836415, baseEnd_7836415] using wordTrace_append hprefix tailTrace_7836415
  have hstable : (prefixWord ++ tailWord_7836415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836415).length < 2 ^ (prefixWord ++ tailWord_7836415).sum := by decide
  have hdescent : baseEnd_7836415 < baseStart_7836415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836442 : List Nat := [3, 1, 1, 3, 2, 1, 2, 2, 2, 6]
def baseStart_7836442 : Nat := 118140960795 + 7836442 * 2 ^ 59
def prefixEnd_7836442 : Nat := 4983230072969 + 3 ^ 40 * 7836442 * 2
def baseEnd_7836442 : Nat := 1341287122360244706111955

theorem tailTrace_7836442 : CollatzResearch.WordTrace tailWord_7836442 prefixEnd_7836442 1341287122360244706111955 := by
  unfold tailWord_7836442
  simp only [CollatzResearch.WordTrace]
  refine ⟨71454630168979116646651895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190545680450610977724405053 71454630168979116646651895)
  ·
    refine ⟨107181945253468674969977843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71454630168979116646651895 107181945253468674969977843)
    ·
      refine ⟨160772917880203012454966765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107181945253468674969977843 160772917880203012454966765)
      ·
        refine ⟨60289844205076129670612537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160772917880203012454966765 60289844205076129670612537)
        ·
          refine ⟨45217383153807097252959403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60289844205076129670612537 45217383153807097252959403)
          ·
            refine ⟨67826074730710645879439105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45217383153807097252959403 67826074730710645879439105)
            ·
              refine ⟨50869556048032984409579329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67826074730710645879439105 50869556048032984409579329)
              ·
                refine ⟨38152167036024738307184497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50869556048032984409579329 38152167036024738307184497)
                ·
                  refine ⟨28614125277018553730388373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38152167036024738307184497 28614125277018553730388373)
                  ·
                    refine ⟨1341287122360244706111955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28614125277018553730388373 1341287122360244706111955)
                    ·
                      rfl

theorem cell23_7836442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 2, 2, 6].length) (baseStart_7836442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836442 prefixEnd_7836442 := by exact prefixLift 7836442
  have htrace : WordTrace (prefixWord ++ tailWord_7836442) baseStart_7836442 baseEnd_7836442 := by
    simpa [prefixWord, tailWord_7836442, baseEnd_7836442] using wordTrace_append hprefix tailTrace_7836442
  have hstable : (prefixWord ++ tailWord_7836442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836442).length < 2 ^ (prefixWord ++ tailWord_7836442).sum := by decide
  have hdescent : baseEnd_7836442 < baseStart_7836442 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836449 : List Nat := [1, 2, 3, 2, 1, 2, 1, 2, 3, 4, 2]
def baseStart_7836449 : Nat := 118140960795 + 7836449 * 2 ^ 59
def prefixEnd_7836449 : Nat := 4983230072969 + 3 ^ 40 * 7836449 * 2
def baseEnd_7836449 : Nat := 4023864961445315590948333

theorem tailTrace_7836449 : CollatzResearch.WordTrace tailWord_7836449 prefixEnd_7836449 4023864961445315590948333 := by
  unfold tailWord_7836449
  simp only [CollatzResearch.WordTrace]
  refine ⟨285818775986891106782112401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190545850657927404521408267 285818775986891106782112401)
  ·
    refine ⟨214364081990168330086584301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285818775986891106782112401 214364081990168330086584301)
    ·
      refine ⟨80386530746313123782469113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214364081990168330086584301 80386530746313123782469113)
      ·
        refine ⟨60289898059734842836851835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80386530746313123782469113 60289898059734842836851835)
        ·
          refine ⟨90434847089602264255277753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60289898059734842836851835 90434847089602264255277753)
          ·
            refine ⟨67826135317201698191458315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90434847089602264255277753 67826135317201698191458315)
            ·
              refine ⟨101739202975802547287187473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67826135317201698191458315 101739202975802547287187473)
              ·
                refine ⟨76304402231851910465390605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101739202975802547287187473 76304402231851910465390605)
                ·
                  refine ⟨28614150836944466424521477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76304402231851910465390605 28614150836944466424521477)
                  ·
                    refine ⟨5365153281927087454597777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28614150836944466424521477 5365153281927087454597777)
                    ·
                      refine ⟨4023864961445315590948333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365153281927087454597777 4023864961445315590948333)
                      ·
                        rfl

theorem cell23_7836449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_7836449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836449 prefixEnd_7836449 := by exact prefixLift 7836449
  have htrace : WordTrace (prefixWord ++ tailWord_7836449) baseStart_7836449 baseEnd_7836449 := by
    simpa [prefixWord, tailWord_7836449, baseEnd_7836449] using wordTrace_append hprefix tailTrace_7836449
  have hstable : (prefixWord ++ tailWord_7836449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836449).length < 2 ^ (prefixWord ++ tailWord_7836449).sum := by decide
  have hdescent : baseEnd_7836449 < baseStart_7836449 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836466 : List Nat := [3, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2]
def baseStart_7836466 : Nat := 118140960795 + 7836466 * 2 ^ 59
def prefixEnd_7836466 : Nat := 4983230072969 + 3 ^ 40 * 7836466 * 2
def baseEnd_7836466 : Nat := 4023873690616442024435755

theorem tailTrace_7836466 : CollatzResearch.WordTrace tailWord_7836466 prefixEnd_7836466 4023873690616442024435755 := by
  unfold tailWord_7836466
  simp only [CollatzResearch.WordTrace]
  refine ⟨71454849006957379671370313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190546264018553012456987501 71454849006957379671370313)
  ·
    refine ⟨53591136755218034753527735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71454849006957379671370313 53591136755218034753527735)
    ·
      refine ⟨80386705132827052130291603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53591136755218034753527735 80386705132827052130291603)
      ·
        refine ⟨120580057699240578195437405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80386705132827052130291603 120580057699240578195437405)
        ·
          refine ⟨45217521637215216823289027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120580057699240578195437405 45217521637215216823289027)
          ·
            refine ⟨67826282455822825234933541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45217521637215216823289027 67826282455822825234933541)
            ·
              refine ⟨12717427960466779731550039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67826282455822825234933541 12717427960466779731550039)
              ·
                refine ⟨19076141940700169597325059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12717427960466779731550039 19076141940700169597325059)
                ·
                  refine ⟨28614212911050254395987589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19076141940700169597325059 28614212911050254395987589)
                  ·
                    refine ⟨5365164920821922699247673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28614212911050254395987589 5365164920821922699247673)
                    ·
                      refine ⟨4023873690616442024435755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365164920821922699247673 4023873690616442024435755)
                      ·
                        rfl

theorem cell23_7836466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 1, 4, 2].length) (baseStart_7836466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836466 prefixEnd_7836466 := by exact prefixLift 7836466
  have htrace : WordTrace (prefixWord ++ tailWord_7836466) baseStart_7836466 baseEnd_7836466 := by
    simpa [prefixWord, tailWord_7836466, baseEnd_7836466] using wordTrace_append hprefix tailTrace_7836466
  have hstable : (prefixWord ++ tailWord_7836466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836466).length < 2 ^ (prefixWord ++ tailWord_7836466).sum := by decide
  have hdescent : baseEnd_7836466 < baseStart_7836466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836472 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 7]
def baseStart_7836472 : Nat := 118140960795 + 7836472 * 2 ^ 59
def prefixEnd_7836472 : Nat := 4983230072969 + 3 ^ 40 * 7836472 * 2
def baseEnd_7836472 : Nat := 447097419055596555662303

theorem tailTrace_7836472 : CollatzResearch.WordTrace tailWord_7836472 prefixEnd_7836472 447097419055596555662303 := by
  unfold tailWord_7836472
  simp only [CollatzResearch.WordTrace]
  refine ⟨142909807432903890855099835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190546409910538521140133113 142909807432903890855099835)
  ·
    refine ⟨214364711149355836282649753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142909807432903890855099835 214364711149355836282649753)
    ·
      refine ⟨160773533362016877211987315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214364711149355836282649753 160773533362016877211987315)
      ·
        refine ⟨241160300043025315817980973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160773533362016877211987315 241160300043025315817980973)
        ·
          refine ⟨90435112516134493431742865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241160300043025315817980973 90435112516134493431742865)
          ·
            refine ⟨67826334387100870073807149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90435112516134493431742865 67826334387100870073807149)
            ·
              refine ⟨25434875395162826277677681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67826334387100870073807149 25434875395162826277677681)
              ·
                refine ⟨19076156546372119708258261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25434875395162826277677681 19076156546372119708258261)
                ·
                  refine ⟨447097419055596555662303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19076156546372119708258261 447097419055596555662303)
                  ·
                    rfl

theorem cell23_7836472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 7].length) (baseStart_7836472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836472 prefixEnd_7836472 := by exact prefixLift 7836472
  have htrace : WordTrace (prefixWord ++ tailWord_7836472) baseStart_7836472 baseEnd_7836472 := by
    simpa [prefixWord, tailWord_7836472, baseEnd_7836472] using wordTrace_append hprefix tailTrace_7836472
  have hstable : (prefixWord ++ tailWord_7836472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836472).length < 2 ^ (prefixWord ++ tailWord_7836472).sum := by decide
  have hdescent : baseEnd_7836472 < baseStart_7836472 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836489 : List Nat := [1, 2, 1, 1, 2, 5, 1, 5, 5]
def baseStart_7836489 : Nat := 118140960795 + 7836489 * 2 ^ 59
def prefixEnd_7836489 : Nat := 4983230072969 + 3 ^ 40 * 7836489 * 2
def baseEnd_7836489 : Nat := 447098388963499492716461

theorem tailTrace_7836489 : CollatzResearch.WordTrace tailWord_7836489 prefixEnd_7836489 447098388963499492716461 := by
  unfold tailWord_7836489
  simp only [CollatzResearch.WordTrace]
  refine ⟨285820234906746193613568521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190546823271164129075712347 285820234906746193613568521)
  ·
    refine ⟨214365176180059645210176391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285820234906746193613568521 214365176180059645210176391)
    ·
      refine ⟨321547764270089467815264587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214365176180059645210176391 321547764270089467815264587)
      ·
        refine ⟨482321646405134201722896881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321547764270089467815264587 482321646405134201722896881)
        ·
          refine ⟨361741234803850651292172661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482321646405134201722896881 361741234803850651292172661)
          ·
            refine ⟨33913240762860998558641187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 361741234803850651292172661 33913240762860998558641187)
            ·
              refine ⟨50869861144291497837961781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33913240762860998558641187 50869861144291497837961781)
              ·
                refine ⟨4769049482277327922308917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50869861144291497837961781 4769049482277327922308917)
                ·
                  refine ⟨447098388963499492716461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4769049482277327922308917 447098388963499492716461)
                  ·
                    rfl

theorem cell23_7836489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 5, 5].length) (baseStart_7836489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836489 prefixEnd_7836489 := by exact prefixLift 7836489
  have htrace : WordTrace (prefixWord ++ tailWord_7836489) baseStart_7836489 baseEnd_7836489 := by
    simpa [prefixWord, tailWord_7836489, baseEnd_7836489] using wordTrace_append hprefix tailTrace_7836489
  have hstable : (prefixWord ++ tailWord_7836489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836489).length < 2 ^ (prefixWord ++ tailWord_7836489).sum := by decide
  have hdescent : baseEnd_7836489 < baseStart_7836489 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836512 : List Nat := [2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 7]
def baseStart_7836512 : Nat := 118140960795 + 7836512 * 2 ^ 59
def prefixEnd_7836512 : Nat := 4983230072969 + 3 ^ 40 * 7836512 * 2
def baseEnd_7836512 : Nat := 4023897310726548844460543

theorem tailTrace_7836512 : CollatzResearch.WordTrace tailWord_7836512 prefixEnd_7836512 4023897310726548844460543 := by
  unfold tailWord_7836512
  simp only [CollatzResearch.WordTrace]
  refine ⟨142910536892831434270827895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190547382523775245694437193 142910536892831434270827895)
  ·
    refine ⟨214365805339247151406241843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142910536892831434270827895 214365805339247151406241843)
    ·
      refine ⟨321548708008870727109362765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214365805339247151406241843 321548708008870727109362765)
      ·
        refine ⟨120580765503326522666011037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321548708008870727109362765 120580765503326522666011037)
        ·
          refine ⟨45217787063747445999754139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120580765503326522666011037 45217787063747445999754139)
          ·
            refine ⟨67826680595621168999631209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45217787063747445999754139 67826680595621168999631209)
            ·
              refine ⟨50870010446715876749723407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67826680595621168999631209 50870010446715876749723407)
              ·
                refine ⟨76305015670073815124585111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50870010446715876749723407 76305015670073815124585111)
                ·
                  refine ⟨114457523505110722686877667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76305015670073815124585111 114457523505110722686877667)
                  ·
                    refine ⟨171686285257666084030316501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114457523505110722686877667 171686285257666084030316501)
                    ·
                      refine ⟨4023897310726548844460543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171686285257666084030316501 4023897310726548844460543)
                      ·
                        rfl

theorem cell23_7836512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 7].length) (baseStart_7836512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836512 prefixEnd_7836512 := by exact prefixLift 7836512
  have htrace : WordTrace (prefixWord ++ tailWord_7836512) baseStart_7836512 baseEnd_7836512 := by
    simpa [prefixWord, tailWord_7836512, baseEnd_7836512] using wordTrace_append hprefix tailTrace_7836512
  have hstable : (prefixWord ++ tailWord_7836512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836512).length < 2 ^ (prefixWord ++ tailWord_7836512).sum := by decide
  have hdescent : baseEnd_7836512 < baseStart_7836512 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836539 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 1, 6, 2]
def baseStart_7836539 : Nat := 118140960795 + 7836539 * 2 ^ 59
def prefixEnd_7836539 : Nat := 4983230072969 + 3 ^ 40 * 7836539 * 2
def baseEnd_7836539 : Nat := 4023911174704220238822919

theorem tailTrace_7836539 : CollatzResearch.WordTrace tailWord_7836539 prefixEnd_7836539 4023911174704220238822919 := by
  unfold tailWord_7836539
  simp only [CollatzResearch.WordTrace]
  refine ⟨285822058556565052152888671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190548039037710034768592447 285822058556565052152888671)
  ·
    refine ⟨428733087834847578229333007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285822058556565052152888671 428733087834847578229333007)
    ·
      refine ⟨643099631752271367343999511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428733087834847578229333007 643099631752271367343999511)
      ·
        refine ⟨964649447628407051015999267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643099631752271367343999511 964649447628407051015999267)
        ·
          refine ⟨1446974171442610576523998901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964649447628407051015999267 1446974171442610576523998901)
          ·
            refine ⟨135653828572744741549124897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1446974171442610576523998901 135653828572744741549124897)
            ·
              refine ⟨101740371429558556161843673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135653828572744741549124897 101740371429558556161843673)
              ·
                refine ⟨76305278572168917121382755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101740371429558556161843673 76305278572168917121382755)
                ·
                  refine ⟨114457917858253375682074133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76305278572168917121382755 114457917858253375682074133)
                  ·
                    refine ⟨5365214899605626985097225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114457917858253375682074133 5365214899605626985097225)
                    ·
                      refine ⟨4023911174704220238822919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365214899605626985097225 4023911174704220238822919)
                      ·
                        rfl

theorem cell23_7836539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 6, 2].length) (baseStart_7836539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836539 prefixEnd_7836539 := by exact prefixLift 7836539
  have htrace : WordTrace (prefixWord ++ tailWord_7836539) baseStart_7836539 baseEnd_7836539 := by
    simpa [prefixWord, tailWord_7836539, baseEnd_7836539] using wordTrace_append hprefix tailTrace_7836539
  have hstable : (prefixWord ++ tailWord_7836539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836539).length < 2 ^ (prefixWord ++ tailWord_7836539).sum := by decide
  have hdescent : baseEnd_7836539 < baseStart_7836539 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836593 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 2, 2, 3]
def baseStart_7836593 : Nat := 118140960795 + 7836593 * 2 ^ 59
def prefixEnd_7836593 : Nat := 4983230072969 + 3 ^ 40 * 7836593 * 2
def baseEnd_7836593 : Nat := 4023938902659563027547671

theorem tailTrace_7836593 : CollatzResearch.WordTrace tailWord_7836593 prefixEnd_7836593 4023938902659563027547671 := by
  unfold tailWord_7836593
  simp only [CollatzResearch.WordTrace]
  refine ⟨285824028098369419375354433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190549352065579612916902955 285824028098369419375354433)
  ·
    refine ⟨214368021073777064531515825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285824028098369419375354433 214368021073777064531515825)
    ·
      refine ⟨160776015805332798398636869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214368021073777064531515825 160776015805332798398636869)
      ·
        refine ⟨30145502963499899699744413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160776015805332798398636869 30145502963499899699744413)
        ·
          refine ⟨11304563611312462387404155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30145502963499899699744413 11304563611312462387404155)
          ·
            refine ⟨16956845416968693581106233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11304563611312462387404155 16956845416968693581106233)
            ·
              refine ⟨12717634062726520185829675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16956845416968693581106233 12717634062726520185829675)
              ·
                refine ⟨19076451094089780278744513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12717634062726520185829675 19076451094089780278744513)
                ·
                  refine ⟨14307338320567335209058385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19076451094089780278744513 14307338320567335209058385)
                  ·
                    refine ⟨10730503740425501406793789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14307338320567335209058385 10730503740425501406793789)
                    ·
                      refine ⟨4023938902659563027547671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10730503740425501406793789 4023938902659563027547671)
                      ·
                        rfl

theorem cell23_7836593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_7836593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836593 prefixEnd_7836593 := by exact prefixLift 7836593
  have htrace : WordTrace (prefixWord ++ tailWord_7836593) baseStart_7836593 baseEnd_7836593 := by
    simpa [prefixWord, tailWord_7836593, baseEnd_7836593] using wordTrace_append hprefix tailTrace_7836593
  have hstable : (prefixWord ++ tailWord_7836593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836593).length < 2 ^ (prefixWord ++ tailWord_7836593).sum := by decide
  have hdescent : baseEnd_7836593 < baseStart_7836593 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836626 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 3, 5]
def baseStart_7836626 : Nat := 118140960795 + 7836626 * 2 ^ 59
def prefixEnd_7836626 : Nat := 4983230072969 + 3 ^ 40 * 7836626 * 2
def baseEnd_7836626 : Nat := 1341318615840387132811673

theorem tailTrace_7836626 : CollatzResearch.WordTrace tailWord_7836626 prefixEnd_7836626 1341318615840387132811673 := by
  unfold tailWord_7836626
  simp only [CollatzResearch.WordTrace]
  refine ⟨71456307926812466502826433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190550154471499910674203821 71456307926812466502826433)
  ·
    refine ⟨53592230945109349877119825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71456307926812466502826433 53592230945109349877119825)
    ·
      refine ⟨40194173208832012407839869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53592230945109349877119825 40194173208832012407839869)
      ·
        refine ⟨15072814953312004652939951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40194173208832012407839869 15072814953312004652939951)
        ·
          refine ⟨22609222429968006979409927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15072814953312004652939951 22609222429968006979409927)
          ·
            refine ⟨33913833644952010469114891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22609222429968006979409927 33913833644952010469114891)
            ·
              refine ⟨50870750467428015703672337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33913833644952010469114891 50870750467428015703672337)
              ·
                refine ⟨38153062850571011777754253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50870750467428015703672337 38153062850571011777754253)
                ·
                  refine ⟨14307398568964129416657845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38153062850571011777754253 14307398568964129416657845)
                  ·
                    refine ⟨1341318615840387132811673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14307398568964129416657845 1341318615840387132811673)
                    ·
                      rfl

theorem cell23_7836626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 3, 5].length) (baseStart_7836626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836626 prefixEnd_7836626 := by exact prefixLift 7836626
  have htrace : WordTrace (prefixWord ++ tailWord_7836626) baseStart_7836626 baseEnd_7836626 := by
    simpa [prefixWord, tailWord_7836626, baseEnd_7836626] using wordTrace_append hprefix tailTrace_7836626
  have hstable : (prefixWord ++ tailWord_7836626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836626).length < 2 ^ (prefixWord ++ tailWord_7836626).sum := by decide
  have hdescent : baseEnd_7836626 < baseStart_7836626 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836650 : List Nat := [3, 1, 3, 1, 2, 4, 1, 1, 2, 3, 2]
def baseStart_7836650 : Nat := 118140960795 + 7836650 * 2 ^ 59
def prefixEnd_7836650 : Nat := 4983230072969 + 3 ^ 40 * 7836650 * 2
def baseEnd_7836650 : Nat := 4023968171056869304534909

theorem tailTrace_7836650 : CollatzResearch.WordTrace tailWord_7836650 prefixEnd_7836650 4023968171056869304534909 := by
  unfold tailWord_7836650
  simp only [CollatzResearch.WordTrace]
  refine ⟨71456526764790729527544851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190550738039441945406786269 71456526764790729527544851)
  ·
    refine ⟨107184790147186094291317277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71456526764790729527544851 107184790147186094291317277)
    ·
      refine ⟨40194296305194785359243979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107184790147186094291317277 40194296305194785359243979)
      ·
        refine ⟨60291444457792178038865969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40194296305194785359243979 60291444457792178038865969)
        ·
          refine ⟨45218583343344133529149477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60291444457792178038865969 45218583343344133529149477)
          ·
            refine ⟨8478484376877025036715527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45218583343344133529149477 8478484376877025036715527)
            ·
              refine ⟨12717726565315537555073291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478484376877025036715527 12717726565315537555073291)
              ·
                refine ⟨19076589847973306332609937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12717726565315537555073291 19076589847973306332609937)
                ·
                  refine ⟨14307442385979979749457453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19076589847973306332609937 14307442385979979749457453)
                  ·
                    refine ⟨5365290894742492406046545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14307442385979979749457453 5365290894742492406046545)
                    ·
                      refine ⟨4023968171056869304534909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365290894742492406046545 4023968171056869304534909)
                      ·
                        rfl

theorem cell23_7836650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 4, 1, 1, 2, 3, 2].length) (baseStart_7836650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836650 prefixEnd_7836650 := by exact prefixLift 7836650
  have htrace : WordTrace (prefixWord ++ tailWord_7836650) baseStart_7836650 baseEnd_7836650 := by
    simpa [prefixWord, tailWord_7836650, baseEnd_7836650] using wordTrace_append hprefix tailTrace_7836650
  have hstable : (prefixWord ++ tailWord_7836650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836650).length < 2 ^ (prefixWord ++ tailWord_7836650).sum := by decide
  have hdescent : baseEnd_7836650 < baseStart_7836650 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836673 : List Nat := [1, 2, 4, 1, 2, 2, 3, 2, 2, 4]
def baseStart_7836673 : Nat := 118140960795 + 7836673 * 2 ^ 59
def prefixEnd_7836673 : Nat := 4983230072969 + 3 ^ 40 * 7836673 * 2
def baseEnd_7836673 : Nat := 1341326660370640904849101

theorem tailTrace_7836673 : CollatzResearch.WordTrace tailWord_7836673 prefixEnd_7836673 1341326660370640904849101 := by
  unfold tailWord_7836673
  simp only [CollatzResearch.WordTrace]
  refine ⟨285826945938079593038266673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190551297292053062025511115 285826945938079593038266673)
  ·
    refine ⟨214370209453559694778700005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285826945938079593038266673 214370209453559694778700005)
    ·
      refine ⟨40194414272542442771006251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214370209453559694778700005 40194414272542442771006251)
      ·
        refine ⟨60291621408813664156509377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40194414272542442771006251 60291621408813664156509377)
        ·
          refine ⟨45218716056610248117382033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60291621408813664156509377 45218716056610248117382033)
          ·
            refine ⟨33914037042457686088036525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45218716056610248117382033 33914037042457686088036525)
            ·
              refine ⟨12717763890921632283013697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33914037042457686088036525 12717763890921632283013697)
              ·
                refine ⟨9538322918191224212260273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12717763890921632283013697 9538322918191224212260273)
                ·
                  refine ⟨7153742188643418159195205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9538322918191224212260273 7153742188643418159195205)
                  ·
                    refine ⟨1341326660370640904849101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7153742188643418159195205 1341326660370640904849101)
                    ·
                      rfl

theorem cell23_7836673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_7836673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836673 prefixEnd_7836673 := by exact prefixLift 7836673
  have htrace : WordTrace (prefixWord ++ tailWord_7836673) baseStart_7836673 baseEnd_7836673 := by
    simpa [prefixWord, tailWord_7836673, baseEnd_7836673] using wordTrace_append hprefix tailTrace_7836673
  have hstable : (prefixWord ++ tailWord_7836673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836673).length < 2 ^ (prefixWord ++ tailWord_7836673).sum := by decide
  have hdescent : baseEnd_7836673 < baseStart_7836673 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836680 : List Nat := [2, 1, 3, 2, 1, 4, 2, 1, 3, 2, 2]
def baseStart_7836680 : Nat := 118140960795 + 7836680 * 2 ^ 59
def prefixEnd_7836680 : Nat := 4983230072969 + 3 ^ 40 * 7836680 * 2
def baseEnd_7836680 : Nat := 4023983575476504187159771

theorem tailTrace_7836680 : CollatzResearch.WordTrace tailWord_7836680 prefixEnd_7836680 4023983575476504187159771 := by
  unfold tailWord_7836680
  simp only [CollatzResearch.WordTrace]
  refine ⟨142913600624527116616885747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190551467499369488822514329 142913600624527116616885747)
  ·
    refine ⟨214370400936790674925328621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142913600624527116616885747 214370400936790674925328621)
    ·
      refine ⟨80388900351296503096998233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214370400936790674925328621 80388900351296503096998233)
      ·
        refine ⟨60291675263472377322748675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80388900351296503096998233 60291675263472377322748675)
        ·
          refine ⟨90437512895208565984123013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60291675263472377322748675 90437512895208565984123013)
          ·
            refine ⟨16957033667851606122023065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90437512895208565984123013 16957033667851606122023065)
            ·
              refine ⟨12717775250888704591517299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16957033667851606122023065 12717775250888704591517299)
              ·
                refine ⟨19076662876333056887275949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12717775250888704591517299 19076662876333056887275949)
                ·
                  refine ⟨7153748578624896332728481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19076662876333056887275949 7153748578624896332728481)
                  ·
                    refine ⟨5365311433968672249546361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7153748578624896332728481 5365311433968672249546361)
                    ·
                      refine ⟨4023983575476504187159771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365311433968672249546361 4023983575476504187159771)
                      ·
                        rfl

theorem cell23_7836680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_7836680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836680 prefixEnd_7836680 := by exact prefixLift 7836680
  have htrace : WordTrace (prefixWord ++ tailWord_7836680) baseStart_7836680 baseEnd_7836680 := by
    simpa [prefixWord, tailWord_7836680, baseEnd_7836680] using wordTrace_append hprefix tailTrace_7836680
  have hstable : (prefixWord ++ tailWord_7836680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836680).length < 2 ^ (prefixWord ++ tailWord_7836680).sum := by decide
  have hdescent : baseEnd_7836680 < baseStart_7836680 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836693 : List Nat := [1, 3, 2, 1, 4, 3, 1, 1, 1, 2, 4]
def baseStart_7836693 : Nat := 118140960795 + 7836693 * 2 ^ 59
def prefixEnd_7836693 : Nat := 4983230072969 + 3 ^ 40 * 7836693 * 2
def baseEnd_7836693 : Nat := 4023990250725012636297211

theorem tailTrace_7836693 : CollatzResearch.WordTrace tailWord_7836693 prefixEnd_7836693 4023990250725012636297211 := by
  unfold tailWord_7836693
  simp only [CollatzResearch.WordTrace]
  refine ⟨285827675398007136453994733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190551783598671424302663155 285827675398007136453994733)
  ·
    refine ⟨107185378274252676170248025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285827675398007136453994733 107185378274252676170248025)
    ·
      refine ⟨80389033705689507127686019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107185378274252676170248025 80389033705689507127686019)
      ·
        refine ⟨120583550558534260691529029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80389033705689507127686019 120583550558534260691529029)
        ·
          refine ⟨22609415729725173879661693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120583550558534260691529029 22609415729725173879661693)
          ·
            refine ⟨8478530898646940204873135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22609415729725173879661693 8478530898646940204873135)
            ·
              refine ⟨12717796347970410307309703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478530898646940204873135 12717796347970410307309703)
              ·
                refine ⟨19076694521955615460964555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12717796347970410307309703 19076694521955615460964555)
                ·
                  refine ⟨28615041782933423191446833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19076694521955615460964555 28615041782933423191446833)
                  ·
                    refine ⟨21461281337200067393585125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28615041782933423191446833 21461281337200067393585125)
                    ·
                      refine ⟨4023990250725012636297211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21461281337200067393585125 4023990250725012636297211)
                      ·
                        rfl

theorem cell23_7836693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_7836693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836693 prefixEnd_7836693 := by exact prefixLift 7836693
  have htrace : WordTrace (prefixWord ++ tailWord_7836693) baseStart_7836693 baseEnd_7836693 := by
    simpa [prefixWord, tailWord_7836693, baseEnd_7836693] using wordTrace_append hprefix tailTrace_7836693
  have hstable : (prefixWord ++ tailWord_7836693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836693).length < 2 ^ (prefixWord ++ tailWord_7836693).sum := by decide
  have hdescent : baseEnd_7836693 < baseStart_7836693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836700 : List Nat := [2, 2, 3, 1, 4, 1, 2, 2, 1, 2, 3]
def baseStart_7836700 : Nat := 118140960795 + 7836700 * 2 ^ 59
def prefixEnd_7836700 : Nat := 4983230072969 + 3 ^ 40 * 7836700 * 2
def baseEnd_7836700 : Nat := 4023993845089594108909679

theorem tailTrace_7836700 : CollatzResearch.WordTrace tailWord_7836700 prefixEnd_7836700 4023993845089594108909679 := by
  unfold tailWord_7836700
  simp only [CollatzResearch.WordTrace]
  refine ⟨142913965354490888324749777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190551953805987851099666369 142913965354490888324749777)
  ·
    refine ⟨107185474015868166243562333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142913965354490888324749777 107185474015868166243562333)
    ·
      refine ⟨40194552755950562341335875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107185474015868166243562333 40194552755950562341335875)
      ·
        refine ⟨60291829133925843512003813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40194552755950562341335875 60291829133925843512003813)
        ·
          refine ⟨11304717962611095658500715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60291829133925843512003813 11304717962611095658500715)
          ·
            refine ⟨16957076943916643487751073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11304717962611095658500715 16957076943916643487751073)
            ·
              refine ⟨12717807707937482615813305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16957076943916643487751073 12717807707937482615813305)
              ·
                refine ⟨9538355780953111961859979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12717807707937482615813305 9538355780953111961859979)
                ·
                  refine ⟨14307533671429667942789969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9538355780953111961859979 14307533671429667942789969)
                  ·
                    refine ⟨10730650253572250957092477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14307533671429667942789969 10730650253572250957092477)
                    ·
                      refine ⟨4023993845089594108909679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10730650253572250957092477 4023993845089594108909679)
                      ·
                        rfl

theorem cell23_7836700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 1, 2, 3].length) (baseStart_7836700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836700 prefixEnd_7836700 := by exact prefixLift 7836700
  have htrace : WordTrace (prefixWord ++ tailWord_7836700) baseStart_7836700 baseEnd_7836700 := by
    simpa [prefixWord, tailWord_7836700, baseEnd_7836700] using wordTrace_append hprefix tailTrace_7836700
  have hstable : (prefixWord ++ tailWord_7836700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836700).length < 2 ^ (prefixWord ++ tailWord_7836700).sum := by decide
  have hdescent : baseEnd_7836700 < baseStart_7836700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836709 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_7836709 : Nat := 118140960795 + 7836709 * 2 ^ 59
def prefixEnd_7836709 : Nat := 4983230072969 + 3 ^ 40 * 7836709 * 2
def baseEnd_7836709 : Nat := 4023998466415484573697137

theorem tailTrace_7836709 : CollatzResearch.WordTrace tailWord_7836709 prefixEnd_7836709 4023998466415484573697137 := by
  unfold tailWord_7836709
  simp only [CollatzResearch.WordTrace]
  refine ⟨285828258965949171186577181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190552172643966114124384787 285828258965949171186577181)
  ·
    refine ⟨107185597112230939194966443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285828258965949171186577181 107185597112230939194966443)
    ·
      refine ⟨160778395668346408792449665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107185597112230939194966443 160778395668346408792449665)
      ·
        refine ⟨120583796751259806594337249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160778395668346408792449665 120583796751259806594337249)
        ·
          refine ⟨90437847563444854945752937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120583796751259806594337249 90437847563444854945752937)
          ·
            refine ⟨67828385672583641209314703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90437847563444854945752937 67828385672583641209314703)
            ·
              refine ⟨101742578508875461813972055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67828385672583641209314703 101742578508875461813972055)
              ·
                refine ⟨152613867763313192720958083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101742578508875461813972055 152613867763313192720958083)
                ·
                  refine ⟨228920801644969789081437125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152613867763313192720958083 228920801644969789081437125)
                  ·
                    refine ⟨42922650308431835452769461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 228920801644969789081437125 42922650308431835452769461)
                    ·
                      refine ⟨4023998466415484573697137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42922650308431835452769461 4023998466415484573697137)
                      ·
                        rfl

theorem cell23_7836709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_7836709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836709 prefixEnd_7836709 := by exact prefixLift 7836709
  have htrace : WordTrace (prefixWord ++ tailWord_7836709) baseStart_7836709 baseEnd_7836709 := by
    simpa [prefixWord, tailWord_7836709, baseEnd_7836709] using wordTrace_append hprefix tailTrace_7836709
  have hstable : (prefixWord ++ tailWord_7836709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836709).length < 2 ^ (prefixWord ++ tailWord_7836709).sum := by decide
  have hdescent : baseEnd_7836709 < baseStart_7836709 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836739 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 5]
def baseStart_7836739 : Nat := 118140960795 + 7836739 * 2 ^ 59
def prefixEnd_7836739 : Nat := 4983230072969 + 3 ^ 40 * 7836739 * 2
def baseEnd_7836739 : Nat := 4024013870835119456321999

theorem tailTrace_7836739 : CollatzResearch.WordTrace tailWord_7836739 prefixEnd_7836739 4024013870835119456321999 := by
  unfold tailWord_7836739
  simp only [CollatzResearch.WordTrace]
  refine ⟨285829353155840486310169271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190552902103893657540112847 285829353155840486310169271)
  ·
    refine ⟨428744029733760729465253907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285829353155840486310169271 428744029733760729465253907)
    ·
      refine ⟨643116044600641094197880861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428744029733760729465253907 643116044600641094197880861)
      ·
        refine ⟨241168516725240410324205323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 643116044600641094197880861 241168516725240410324205323)
        ·
          refine ⟨361752775087860615486307985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241168516725240410324205323 361752775087860615486307985)
          ·
            refine ⟨271314581315895461614730989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361752775087860615486307985 271314581315895461614730989)
            ·
              refine ⟨101742967993460798105524121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271314581315895461614730989 101742967993460798105524121)
              ·
                refine ⟨76307225995095598579143091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101742967993460798105524121 76307225995095598579143091)
                ·
                  refine ⟨114460838992643397868714637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76307225995095598579143091 114460838992643397868714637)
                  ·
                    refine ⟨42922814622241274200767989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114460838992643397868714637 42922814622241274200767989)
                    ·
                      refine ⟨4024013870835119456321999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42922814622241274200767989 4024013870835119456321999)
                      ·
                        rfl

theorem cell23_7836739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_7836739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836739 prefixEnd_7836739 := by exact prefixLift 7836739
  have htrace : WordTrace (prefixWord ++ tailWord_7836739) baseStart_7836739 baseEnd_7836739 := by
    simpa [prefixWord, tailWord_7836739, baseEnd_7836739] using wordTrace_append hprefix tailTrace_7836739
  have hstable : (prefixWord ++ tailWord_7836739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836739).length < 2 ^ (prefixWord ++ tailWord_7836739).sum := by decide
  have hdescent : baseEnd_7836739 < baseStart_7836739 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836756 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 2, 1, 5]
def baseStart_7836756 : Nat := 118140960795 + 7836756 * 2 ^ 59
def prefixEnd_7836756 : Nat := 4983230072969 + 3 ^ 40 * 7836756 * 2
def baseEnd_7836756 : Nat := 4024022600006245889809421

theorem tailTrace_7836756 : CollatzResearch.WordTrace tailWord_7836756 prefixEnd_7836756 4024022600006245889809421 := by
  unfold tailWord_7836756
  simp only [CollatzResearch.WordTrace]
  refine ⟨142914986598389449106769061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190553315464519265475692081 142914986598389449106769061)
  ·
    refine ⟨26796559987198021707519199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142914986598389449106769061 26796559987198021707519199)
    ·
      refine ⟨40194839980797032561278799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26796559987198021707519199 40194839980797032561278799)
      ·
        refine ⟨60292259971195548841918199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40194839980797032561278799 60292259971195548841918199)
        ·
          refine ⟨90438389956793323262877299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60292259971195548841918199 90438389956793323262877299)
          ·
            refine ⟨135657584935189984894315949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90438389956793323262877299 135657584935189984894315949)
            ·
              refine ⟨50871594350696244335368481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135657584935189984894315949 50871594350696244335368481)
              ·
                refine ⟨38153695763022183251526361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50871594350696244335368481 38153695763022183251526361)
                ·
                  refine ⟨28615271822266637438644771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38153695763022183251526361 28615271822266637438644771)
                  ·
                    refine ⟨42922907733399956157967157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28615271822266637438644771 42922907733399956157967157)
                    ·
                      refine ⟨4024022600006245889809421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42922907733399956157967157 4024022600006245889809421)
                      ·
                        rfl

theorem cell23_7836756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 1, 5].length) (baseStart_7836756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836756 prefixEnd_7836756 := by exact prefixLift 7836756
  have htrace : WordTrace (prefixWord ++ tailWord_7836756) baseStart_7836756 baseEnd_7836756 := by
    simpa [prefixWord, tailWord_7836756, baseEnd_7836756] using wordTrace_append hprefix tailTrace_7836756
  have hstable : (prefixWord ++ tailWord_7836756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836756).length < 2 ^ (prefixWord ++ tailWord_7836756).sum := by decide
  have hdescent : baseEnd_7836756 < baseStart_7836756 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836759 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 9]
def baseStart_7836759 : Nat := 118140960795 + 7836759 * 2 ^ 59
def prefixEnd_7836759 : Nat := 4983230072969 + 3 ^ 40 * 7836759 * 2
def baseEnd_7836759 : Nat := 447113793383134375341323

theorem tailTrace_7836759 : CollatzResearch.WordTrace tailWord_7836759 prefixEnd_7836759 447113793383134375341323 := by
  unfold tailWord_7836759
  simp only [CollatzResearch.WordTrace]
  refine ⟨285830082615768029725897331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190553388410512019817264887 285830082615768029725897331)
  ·
    refine ⟨428745123923652044588845997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285830082615768029725897331 428745123923652044588845997)
    ·
      refine ⟨160779421471369516720817249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428745123923652044588845997 160779421471369516720817249)
      ·
        refine ⟨120584566103527137540612937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160779421471369516720817249 120584566103527137540612937)
        ·
          refine ⟨90438424577645353155459703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120584566103527137540612937 90438424577645353155459703)
          ·
            refine ⟨135657636866468029733189555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90438424577645353155459703 135657636866468029733189555)
            ·
              refine ⟨203486455299702044599784333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135657636866468029733189555 203486455299702044599784333)
              ·
                refine ⟨76307420737388266724919125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203486455299702044599784333 76307420737388266724919125)
                ·
                  refine ⟨447113793383134375341323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76307420737388266724919125 447113793383134375341323)
                  ·
                    rfl

theorem cell23_7836759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 9].length) (baseStart_7836759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836759 prefixEnd_7836759 := by exact prefixLift 7836759
  have htrace : WordTrace (prefixWord ++ tailWord_7836759) baseStart_7836759 baseEnd_7836759 := by
    simpa [prefixWord, tailWord_7836759, baseEnd_7836759] using wordTrace_append hprefix tailTrace_7836759
  have hstable : (prefixWord ++ tailWord_7836759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836759).length < 2 ^ (prefixWord ++ tailWord_7836759).sum := by decide
  have hdescent : baseEnd_7836759 < baseStart_7836759 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836770 : List Nat := [3, 3, 2, 2, 1, 1, 1, 1, 3, 4, 2]
def baseStart_7836770 : Nat := 118140960795 + 7836770 * 2 ^ 59
def prefixEnd_7836770 : Nat := 4983230072969 + 3 ^ 40 * 7836770 * 2
def baseEnd_7836770 : Nat := 4024029788735408835034357

theorem tailTrace_7836770 : CollatzResearch.WordTrace tailWord_7836770 prefixEnd_7836770 4024029788735408835034357 := by
  unfold tailWord_7836770
  simp only [CollatzResearch.WordTrace]
  refine ⟨71457620954682044651136941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190553655879152119069698509 71457620954682044651136941)
  ·
    refine ⟨26796607858005766744176353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71457620954682044651136941 26796607858005766744176353)
    ·
      refine ⟨20097455893504325058132265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26796607858005766744176353 20097455893504325058132265)
      ·
        refine ⟨15073091920128243793599199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20097455893504325058132265 15073091920128243793599199)
        ·
          refine ⟨22609637880192365690398799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15073091920128243793599199 22609637880192365690398799)
          ·
            refine ⟨33914456820288548535598199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22609637880192365690398799 33914456820288548535598199)
            ·
              refine ⟨50871685230432822803397299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33914456820288548535598199 50871685230432822803397299)
              ·
                refine ⟨76307527845649234205095949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50871685230432822803397299 76307527845649234205095949)
                ·
                  refine ⟨28615322942118462826910981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76307527845649234205095949 28615322942118462826910981)
                  ·
                    refine ⟨5365373051647211780045809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28615322942118462826910981 5365373051647211780045809)
                    ·
                      refine ⟨4024029788735408835034357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365373051647211780045809 4024029788735408835034357)
                      ·
                        rfl

theorem cell23_7836770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_7836770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836770 prefixEnd_7836770 := by exact prefixLift 7836770
  have htrace : WordTrace (prefixWord ++ tailWord_7836770) baseStart_7836770 baseEnd_7836770 := by
    simpa [prefixWord, tailWord_7836770, baseEnd_7836770] using wordTrace_append hprefix tailTrace_7836770
  have hstable : (prefixWord ++ tailWord_7836770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836770).length < 2 ^ (prefixWord ++ tailWord_7836770).sum := by decide
  have hdescent : baseEnd_7836770 < baseStart_7836770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836823 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 2, 5]
def baseStart_7836823 : Nat := 118140960795 + 7836823 * 2 ^ 59
def prefixEnd_7836823 : Nat := 4983230072969 + 3 ^ 40 * 7836823 * 2
def baseEnd_7836823 : Nat := 1341352334403365709223871

theorem tailTrace_7836823 : CollatzResearch.WordTrace tailWord_7836823 prefixEnd_7836823 1341352334403365709223871 := by
  unfold tailWord_7836823
  simp only [CollatzResearch.WordTrace]
  refine ⟨285832416887536168656227123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190554944591690779104151415 285832416887536168656227123)
  ·
    refine ⟨428748625331304252984340685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285832416887536168656227123 428748625331304252984340685)
    ·
      refine ⟨160780734499239094869127757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428748625331304252984340685 160780734499239094869127757)
      ·
        refine ⟨60292775437214660575922909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160780734499239094869127757 60292775437214660575922909)
        ·
          refine ⟨22609790788955497715971091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60292775437214660575922909 22609790788955497715971091)
          ·
            refine ⟨33914686183433246573956637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22609790788955497715971091 33914686183433246573956637)
            ·
              refine ⟨12718007318787467465233739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33914686183433246573956637 12718007318787467465233739)
              ·
                refine ⟨19077010978181201197850609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12718007318787467465233739 19077010978181201197850609)
                ·
                  refine ⟨14307758233635900898387957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19077010978181201197850609 14307758233635900898387957)
                  ·
                    refine ⟨1341352334403365709223871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14307758233635900898387957 1341352334403365709223871)
                    ·
                      rfl

theorem cell23_7836823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 5].length) (baseStart_7836823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836823 prefixEnd_7836823 := by exact prefixLift 7836823
  have htrace : WordTrace (prefixWord ++ tailWord_7836823) baseStart_7836823 baseEnd_7836823 := by
    simpa [prefixWord, tailWord_7836823, baseEnd_7836823] using wordTrace_append hprefix tailTrace_7836823
  have hstable : (prefixWord ++ tailWord_7836823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836823).length < 2 ^ (prefixWord ++ tailWord_7836823).sum := by decide
  have hdescent : baseEnd_7836823 < baseStart_7836823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836860 : List Nat := [2, 2, 2, 3, 2, 1, 2, 1, 2, 4, 2]
def baseStart_7836860 : Nat := 118140960795 + 7836860 * 2 ^ 59
def prefixEnd_7836860 : Nat := 4983230072969 + 3 ^ 40 * 7836860 * 2
def baseEnd_7836860 : Nat := 4024076001994313482908943

theorem tailTrace_7836860 : CollatzResearch.WordTrace tailWord_7836860 prefixEnd_7836860 4024076001994313482908943 := by
  unfold tailWord_7836860
  simp only [CollatzResearch.WordTrace]
  refine ⟨142916883194201061987662017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190555844258934749316882689 142916883194201061987662017)
  ·
    refine ⟨107187662395650796490746513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142916883194201061987662017 107187662395650796490746513)
    ·
      refine ⟨80390746796738097368059885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107187662395650796490746513 80390746796738097368059885)
      ·
        refine ⟨30146530048776786513022457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80390746796738097368059885 30146530048776786513022457)
        ·
          refine ⟨22609897536582589884766843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30146530048776786513022457 22609897536582589884766843)
          ·
            refine ⟨33914846304873884827150265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22609897536582589884766843 33914846304873884827150265)
            ·
              refine ⟨25436134728655413620362699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33914846304873884827150265 25436134728655413620362699)
              ·
                refine ⟨38154202092983120430544049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25436134728655413620362699 38154202092983120430544049)
                ·
                  refine ⟨28615651569737340322908037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38154202092983120430544049 28615651569737340322908037)
                  ·
                    refine ⟨5365434669325751310545257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28615651569737340322908037 5365434669325751310545257)
                    ·
                      refine ⟨4024076001994313482908943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365434669325751310545257 4024076001994313482908943)
                      ·
                        rfl

theorem cell23_7836860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_7836860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836860 prefixEnd_7836860 := by exact prefixLift 7836860
  have htrace : WordTrace (prefixWord ++ tailWord_7836860) baseStart_7836860 baseEnd_7836860 := by
    simpa [prefixWord, tailWord_7836860, baseEnd_7836860] using wordTrace_append hprefix tailTrace_7836860
  have hstable : (prefixWord ++ tailWord_7836860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836860).length < 2 ^ (prefixWord ++ tailWord_7836860).sum := by decide
  have hdescent : baseEnd_7836860 < baseStart_7836860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836933 : List Nat := [1, 3, 1, 1, 2, 1, 5, 1, 3, 1, 4]
def baseStart_7836933 : Nat := 118140960795 + 7836933 * 2 ^ 59
def prefixEnd_7836933 : Nat := 4983230072969 + 3 ^ 40 * 7836933 * 2
def baseEnd_7836933 : Nat := 4024113486082091697296107

theorem tailTrace_7836933 : CollatzResearch.WordTrace tailWord_7836933 prefixEnd_7836933 4024113486082091697296107 := by
  unfold tailWord_7836933
  simp only [CollatzResearch.WordTrace]
  refine ⟨285836428917137657442731453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190557619278091771628487635 285836428917137657442731453)
  ·
    refine ⟨107188660843926621541024295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285836428917137657442731453 107188660843926621541024295)
    ·
      refine ⟨160782991265889932311536443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107188660843926621541024295 160782991265889932311536443)
      ·
        refine ⟨241174486898834898467304665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160782991265889932311536443 241174486898834898467304665)
        ·
          refine ⟨180880865174126173850478499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241174486898834898467304665 180880865174126173850478499)
          ·
            refine ⟨271321297761189260775717749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180880865174126173850478499 271321297761189260775717749)
            ·
              refine ⟨25436371665111493197723539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271321297761189260775717749 25436371665111493197723539)
              ·
                refine ⟨38154557497667239796585309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25436371665111493197723539 38154557497667239796585309)
                ·
                  refine ⟨14307959061625214923719491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38154557497667239796585309 14307959061625214923719491)
                  ·
                    refine ⟨21461938592437822385579237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14307959061625214923719491 21461938592437822385579237)
                    ·
                      refine ⟨4024113486082091697296107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21461938592437822385579237 4024113486082091697296107)
                      ·
                        rfl

theorem cell23_7836933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 5, 1, 3, 1, 4].length) (baseStart_7836933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836933 prefixEnd_7836933 := by exact prefixLift 7836933
  have htrace : WordTrace (prefixWord ++ tailWord_7836933) baseStart_7836933 baseEnd_7836933 := by
    simpa [prefixWord, tailWord_7836933, baseEnd_7836933] using wordTrace_append hprefix tailTrace_7836933
  have hstable : (prefixWord ++ tailWord_7836933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836933).length < 2 ^ (prefixWord ++ tailWord_7836933).sum := by decide
  have hdescent : baseEnd_7836933 < baseStart_7836933 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836990 : List Nat := [4, 2, 1, 2, 1, 1, 5, 7]
def baseStart_7836990 : Nat := 118140960795 + 7836990 * 2 ^ 59
def prefixEnd_7836990 : Nat := 4983230072969 + 3 ^ 40 * 7836990 * 2
def baseEnd_7836990 : Nat := 149042324239977702751235

theorem tailTrace_7836990 : CollatzResearch.WordTrace tailWord_7836990 prefixEnd_7836990 149042324239977702751235 := by
  unfold tailWord_7836990
  simp only [CollatzResearch.WordTrace]
  refine ⟨35729813484741394522194553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190559005251954104118370949 35729813484741394522194553)
  ·
    refine ⟨26797360113556045891645915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35729813484741394522194553 26797360113556045891645915)
    ·
      refine ⟨40196040170334068837468873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26797360113556045891645915 40196040170334068837468873)
      ·
        refine ⟨30147030127750551628101655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40196040170334068837468873 30147030127750551628101655)
        ·
          refine ⟨45220545191625827442152483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30147030127750551628101655 45220545191625827442152483)
          ·
            refine ⟨67830817787438741163228725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45220545191625827442152483 67830817787438741163228725)
            ·
              refine ⟨6359139167572381984052693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67830817787438741163228725 6359139167572381984052693)
              ·
                refine ⟨149042324239977702751235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6359139167572381984052693 149042324239977702751235)
                ·
                  rfl

theorem cell23_7836990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 7].length) (baseStart_7836990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836990 prefixEnd_7836990 := by exact prefixLift 7836990
  have htrace : WordTrace (prefixWord ++ tailWord_7836990) baseStart_7836990 baseEnd_7836990 := by
    simpa [prefixWord, tailWord_7836990, baseEnd_7836990] using wordTrace_append hprefix tailTrace_7836990
  have hstable : (prefixWord ++ tailWord_7836990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836990).length < 2 ^ (prefixWord ++ tailWord_7836990).sum := by decide
  have hdescent : baseEnd_7836990 < baseStart_7836990 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7836998 : List Nat := [6, 1, 1, 3, 1, 2, 2, 1, 1, 5]
def baseStart_7836998 : Nat := 118140960795 + 7836998 * 2 ^ 59
def prefixEnd_7836998 : Nat := 4983230072969 + 3 ^ 40 * 7836998 * 2
def baseEnd_7836998 : Nat := 1341382287441544647661103

theorem tailTrace_7836998 : CollatzResearch.WordTrace tailWord_7836998 prefixEnd_7836998 1341382287441544647661103 := by
  unfold tailWord_7836998
  simp only [CollatzResearch.WordTrace]
  refine ⟨8932462489434442923245239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190559199774601449029231765 8932462489434442923245239)
  ·
    refine ⟨13398693734151664384867859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8932462489434442923245239 13398693734151664384867859)
    ·
      refine ⟨20098040601227496577301789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13398693734151664384867859 20098040601227496577301789)
      ·
        refine ⟨7536765225460311216488171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20098040601227496577301789 7536765225460311216488171)
        ·
          refine ⟨11305147838190466824732257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7536765225460311216488171 11305147838190466824732257)
          ·
            refine ⟨8478860878642850118549193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11305147838190466824732257 8478860878642850118549193)
            ·
              refine ⟨6359145658982137588911895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8478860878642850118549193 6359145658982137588911895)
              ·
                refine ⟨9538718488473206383367843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6359145658982137588911895 9538718488473206383367843)
                ·
                  refine ⟨14308077732709809575051765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9538718488473206383367843 14308077732709809575051765)
                  ·
                    refine ⟨1341382287441544647661103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14308077732709809575051765 1341382287441544647661103)
                    ·
                      rfl

theorem cell23_7836998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_7836998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7836998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7836998 prefixEnd_7836998 := by exact prefixLift 7836998
  have htrace : WordTrace (prefixWord ++ tailWord_7836998) baseStart_7836998 baseEnd_7836998 := by
    simpa [prefixWord, tailWord_7836998, baseEnd_7836998] using wordTrace_append hprefix tailTrace_7836998
  have hstable : (prefixWord ++ tailWord_7836998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7836998).length < 2 ^ (prefixWord ++ tailWord_7836998).sum := by decide
  have hdescent : baseEnd_7836998 < baseStart_7836998 := by decide
  rcases family_descends (prefixWord ++ tailWord_7836998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837000 : List Nat := [2, 1, 3, 1, 1, 2, 1, 4, 4, 1, 3]
def baseStart_7837000 : Nat := 118140960795 + 7837000 * 2 ^ 59
def prefixEnd_7837000 : Nat := 4983230072969 + 3 ^ 40 * 7837000 * 2
def baseEnd_7837000 : Nat := 4024147889285942935158299

theorem tailTrace_7837000 : CollatzResearch.WordTrace tailWord_7837000 prefixEnd_7837000 4024147889285942935158299 := by
  unfold tailWord_7837000
  simp only [CollatzResearch.WordTrace]
  refine ⟨142919436303947463942710227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190559248405263285256946969 142919436303947463942710227)
  ·
    refine ⟨214379154455921195914065341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142919436303947463942710227 214379154455921195914065341)
    ·
      refine ⟨80392182920970448467774503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214379154455921195914065341 80392182920970448467774503)
      ·
        refine ⟨120588274381455672701661755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80392182920970448467774503 120588274381455672701661755)
        ·
          refine ⟨180882411572183509052492633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120588274381455672701661755 180882411572183509052492633)
          ·
            refine ⟨135661808679137631789369475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180882411572183509052492633 135661808679137631789369475)
            ·
              refine ⟨203492713018706447684054213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135661808679137631789369475 203492713018706447684054213)
              ·
                refine ⟨38154883691007458940760165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203492713018706447684054213 38154883691007458940760165)
                ·
                  refine ⟨7154040692063898551392531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38154883691007458940760165 7154040692063898551392531)
                  ·
                    refine ⟨10731061038095847827088797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7154040692063898551392531 10731061038095847827088797)
                    ·
                      refine ⟨4024147889285942935158299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10731061038095847827088797 4024147889285942935158299)
                      ·
                        rfl

theorem cell23_7837000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_7837000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837000 prefixEnd_7837000 := by exact prefixLift 7837000
  have htrace : WordTrace (prefixWord ++ tailWord_7837000) baseStart_7837000 baseEnd_7837000 := by
    simpa [prefixWord, tailWord_7837000, baseEnd_7837000] using wordTrace_append hprefix tailTrace_7837000
  have hstable : (prefixWord ++ tailWord_7837000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837000).length < 2 ^ (prefixWord ++ tailWord_7837000).sum := by decide
  have hdescent : baseEnd_7837000 < baseStart_7837000 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837004 : List Nat := [2, 2, 1, 3, 2, 4, 2, 1, 1, 2, 3]
def baseStart_7837004 : Nat := 118140960795 + 7837004 * 2 ^ 59
def prefixEnd_7837004 : Nat := 4983230072969 + 3 ^ 40 * 7837004 * 2
def baseEnd_7837004 : Nat := 4024149943208560919508281

theorem tailTrace_7837004 : CollatzResearch.WordTrace tailWord_7837004 prefixEnd_7837004 4024149943208560919508281 := by
  unfold tailWord_7837004
  simp only [CollatzResearch.WordTrace]
  refine ⟨142919509249940218284283033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190559345666586957712377377 142919509249940218284283033)
  ·
    refine ⟨107189631937455163713212275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142919509249940218284283033 107189631937455163713212275)
    ·
      refine ⟨160784447906182745569818413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107189631937455163713212275 160784447906182745569818413)
      ·
        refine ⟨60294167964818529588681905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160784447906182745569818413 60294167964818529588681905)
        ·
          refine ⟨45220625973613897191511429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60294167964818529588681905 45220625973613897191511429)
          ·
            refine ⟨8478867370052605723408393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45220625973613897191511429 8478867370052605723408393)
            ·
              refine ⟨6359150527539454292556295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8478867370052605723408393 6359150527539454292556295)
              ·
                refine ⟨9538725791309181438834443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6359150527539454292556295 9538725791309181438834443)
                ·
                  refine ⟨14308088686963772158251665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9538725791309181438834443 14308088686963772158251665)
                  ·
                    refine ⟨10731066515222829118688749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14308088686963772158251665 10731066515222829118688749)
                    ·
                      refine ⟨4024149943208560919508281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10731066515222829118688749 4024149943208560919508281)
                      ·
                        rfl

theorem cell23_7837004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_7837004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837004 prefixEnd_7837004 := by exact prefixLift 7837004
  have htrace : WordTrace (prefixWord ++ tailWord_7837004) baseStart_7837004 baseEnd_7837004 := by
    simpa [prefixWord, tailWord_7837004, baseEnd_7837004] using wordTrace_append hprefix tailTrace_7837004
  have hstable : (prefixWord ++ tailWord_7837004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837004).length < 2 ^ (prefixWord ++ tailWord_7837004).sum := by decide
  have hdescent : baseEnd_7837004 < baseStart_7837004 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837017 : List Nat := [1, 2, 1, 2, 2, 2, 5, 2, 2, 1, 3]
def baseStart_7837017 : Nat := 118140960795 + 7837017 * 2 ^ 59
def prefixEnd_7837017 : Nat := 4983230072969 + 3 ^ 40 * 7837017 * 2
def baseEnd_7837017 : Nat := 4024156618457069368645721

theorem tailTrace_7837017 : CollatzResearch.WordTrace tailWord_7837017 prefixEnd_7837017 4024156618457069368645721 := by
  unfold tailWord_7837017
  simp only [CollatzResearch.WordTrace]
  refine ⟨285839492648833339788789305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190559661765888893192526203 285839492648833339788789305)
  ·
    refine ⟨214379619486625004841591979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285839492648833339788789305 214379619486625004841591979)
    ·
      refine ⟨321569429229937507262387969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214379619486625004841591979 321569429229937507262387969)
      ·
        refine ⟨241177071922453130446790977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321569429229937507262387969 241177071922453130446790977)
        ·
          refine ⟨180882803941839847835093233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241177071922453130446790977 180882803941839847835093233)
          ·
            refine ⟨135662102956379885876319925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180882803941839847835093233 135662102956379885876319925)
            ·
              refine ⟨12718322152160614300904993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135662102956379885876319925 12718322152160614300904993)
              ·
                refine ⟨9538741614120460725678745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12718322152160614300904993 9538741614120460725678745)
                ·
                  refine ⟨7154056210590345544259059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9538741614120460725678745 7154056210590345544259059)
                  ·
                    refine ⟨10731084315885518316388589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7154056210590345544259059 10731084315885518316388589)
                    ·
                      refine ⟨4024156618457069368645721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10731084315885518316388589 4024156618457069368645721)
                      ·
                        rfl

theorem cell23_7837017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 2, 2, 1, 3].length) (baseStart_7837017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837017 prefixEnd_7837017 := by exact prefixLift 7837017
  have htrace : WordTrace (prefixWord ++ tailWord_7837017) baseStart_7837017 baseEnd_7837017 := by
    simpa [prefixWord, tailWord_7837017, baseEnd_7837017] using wordTrace_append hprefix tailTrace_7837017
  have hstable : (prefixWord ++ tailWord_7837017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837017).length < 2 ^ (prefixWord ++ tailWord_7837017).sum := by decide
  have hdescent : baseEnd_7837017 < baseStart_7837017 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837034 : List Nat := [3, 1, 3, 3, 2, 2, 1, 1, 1, 3, 3]
def baseStart_7837034 : Nat := 118140960795 + 7837034 * 2 ^ 59
def prefixEnd_7837034 : Nat := 4983230072969 + 3 ^ 40 * 7837034 * 2
def baseEnd_7837034 : Nat := 4024165347628195802133143

theorem tailTrace_7837034 : CollatzResearch.WordTrace tailWord_7837034 prefixEnd_7837034 4024165347628195802133143 := by
  unfold tailWord_7837034
  simp only [CollatzResearch.WordTrace]
  refine ⟨71460028172442937923039539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190560075126514501128105437 71460028172442937923039539)
  ·
    refine ⟨107190042258664406884559309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71460028172442937923039539 107190042258664406884559309)
    ·
      refine ⟨40196265846999152581709741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107190042258664406884559309 40196265846999152581709741)
      ·
        refine ⟨15073599692624682218141153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40196265846999152581709741 15073599692624682218141153)
        ·
          refine ⟨11305199769468511663605865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15073599692624682218141153 11305199769468511663605865)
          ·
            refine ⟨8478899827101383747704399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11305199769468511663605865 8478899827101383747704399)
            ·
              refine ⟨12718349740652075621556599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8478899827101383747704399 12718349740652075621556599)
              ·
                refine ⟨19077524610978113432334899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12718349740652075621556599 19077524610978113432334899)
                ·
                  refine ⟨28616286916467170148502349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19077524610978113432334899 28616286916467170148502349)
                  ·
                    refine ⟨10731107593675188805688381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28616286916467170148502349 10731107593675188805688381)
                    ·
                      refine ⟨4024165347628195802133143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10731107593675188805688381 4024165347628195802133143)
                      ·
                        rfl

theorem cell23_7837034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_7837034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837034 prefixEnd_7837034 := by exact prefixLift 7837034
  have htrace : WordTrace (prefixWord ++ tailWord_7837034) baseStart_7837034 baseEnd_7837034 := by
    simpa [prefixWord, tailWord_7837034, baseEnd_7837034] using wordTrace_append hprefix tailTrace_7837034
  have hstable : (prefixWord ++ tailWord_7837034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837034).length < 2 ^ (prefixWord ++ tailWord_7837034).sum := by decide
  have hdescent : baseEnd_7837034 < baseStart_7837034 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837060 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_7837060 : Nat := 118140960795 + 7837060 * 2 ^ 59
def prefixEnd_7837060 : Nat := 4983230072969 + 3 ^ 40 * 7837060 * 2
def baseEnd_7837060 : Nat := 4024178698125212700408023

theorem tailTrace_7837060 : CollatzResearch.WordTrace tailWord_7837060 prefixEnd_7837060 4024178698125212700408023 := by
  unfold tailWord_7837060
  simp only [CollatzResearch.WordTrace]
  refine ⟨142920530493838779066302317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190560707325118372088403089 142920530493838779066302317)
  ·
    refine ⟨53595198935189542149863369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142920530493838779066302317 53595198935189542149863369)
    ·
      refine ⟨40196399201392156612397527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53595198935189542149863369 40196399201392156612397527)
      ·
        refine ⟨60294598802088234918596291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40196399201392156612397527 60294598802088234918596291)
        ·
          refine ⟨90441898203132352377894437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60294598802088234918596291 90441898203132352377894437)
          ·
            refine ⟨16957855913087316070855207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90441898203132352377894437 16957855913087316070855207)
            ·
              refine ⟨25436783869630974106282811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16957855913087316070855207 25436783869630974106282811)
              ·
                refine ⟨38155175804446461159424217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25436783869630974106282811 38155175804446461159424217)
                ·
                  refine ⟨28616381853334845869568163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38155175804446461159424217 28616381853334845869568163)
                  ·
                    refine ⟨42924572780002268804352245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28616381853334845869568163 42924572780002268804352245)
                    ·
                      refine ⟨4024178698125212700408023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42924572780002268804352245 4024178698125212700408023)
                      ·
                        rfl

theorem cell23_7837060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_7837060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837060 prefixEnd_7837060 := by exact prefixLift 7837060
  have htrace : WordTrace (prefixWord ++ tailWord_7837060) baseStart_7837060 baseEnd_7837060 := by
    simpa [prefixWord, tailWord_7837060, baseEnd_7837060] using wordTrace_append hprefix tailTrace_7837060
  have hstable : (prefixWord ++ tailWord_7837060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837060).length < 2 ^ (prefixWord ++ tailWord_7837060).sum := by decide
  have hdescent : baseEnd_7837060 < baseStart_7837060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837093 : List Nat := [1, 3, 1, 2, 1, 1, 2, 4, 1, 7]
def baseStart_7837093 : Nat := 118140960795 + 7837093 * 2 ^ 59
def prefixEnd_7837093 : Nat := 4983230072969 + 3 ^ 40 * 7837093 * 2
def baseEnd_7837093 : Nat := 1341398547662270357098457

theorem tailTrace_7837093 : CollatzResearch.WordTrace tailWord_7837093 prefixEnd_7837093 1341398547662270357098457 := by
  unfold tailWord_7837093
  simp only [CollatzResearch.WordTrace]
  refine ⟨285842264596558004768555933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190561509731038669845703955 285842264596558004768555933)
  ·
    refine ⟨107190849223709251788208475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285842264596558004768555933 107190849223709251788208475)
    ·
      refine ⟨160786273835563877682312713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107190849223709251788208475 160786273835563877682312713)
      ·
        refine ⟨120589705376672908261734535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160786273835563877682312713 120589705376672908261734535)
        ·
          refine ⟨180884558065009362392601803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120589705376672908261734535 180884558065009362392601803)
          ·
            refine ⟨271326837097514043588902705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180884558065009362392601803 271326837097514043588902705)
            ·
              refine ⟨203495127823135532691677029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271326837097514043588902705 203495127823135532691677029)
              ·
                refine ⟨38155336466837912379689443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203495127823135532691677029 38155336466837912379689443)
                ·
                  refine ⟨57233004700256868569534165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38155336466837912379689443 57233004700256868569534165)
                  ·
                    refine ⟨1341398547662270357098457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57233004700256868569534165 1341398547662270357098457)
                    ·
                      rfl

theorem cell23_7837093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 7].length) (baseStart_7837093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837093 prefixEnd_7837093 := by exact prefixLift 7837093
  have htrace : WordTrace (prefixWord ++ tailWord_7837093) baseStart_7837093 baseEnd_7837093 := by
    simpa [prefixWord, tailWord_7837093, baseEnd_7837093] using wordTrace_append hprefix tailTrace_7837093
  have hstable : (prefixWord ++ tailWord_7837093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837093).length < 2 ^ (prefixWord ++ tailWord_7837093).sum := by decide
  have hdescent : baseEnd_7837093 < baseStart_7837093 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837157 : List Nat := [1, 3, 1, 5, 1, 1, 1, 1, 5, 4]
def baseStart_7837157 : Nat := 118140960795 + 7837157 * 2 ^ 59
def prefixEnd_7837157 : Nat := 4983230072969 + 3 ^ 40 * 7837157 * 2
def baseEnd_7837157 : Nat := 1341409501916232940298359

theorem tailTrace_7837157 : CollatzResearch.WordTrace tailWord_7837157 prefixEnd_7837157 1341409501916232940298359 := by
  unfold tailWord_7837157
  simp only [CollatzResearch.WordTrace]
  refine ⟨285844598868326143698885725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190563065912217429132590483 285844598868326143698885725)
  ·
    refine ⟨107191724575622303887082147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285844598868326143698885725 107191724575622303887082147)
    ·
      refine ⟨160787586863433455830623221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107191724575622303887082147 160787586863433455830623221)
      ·
        refine ⟨15073836268446886484120927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160787586863433455830623221 15073836268446886484120927)
        ·
          refine ⟨22610754402670329726181391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15073836268446886484120927 22610754402670329726181391)
          ·
            refine ⟨33916131604005494589272087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22610754402670329726181391 33916131604005494589272087)
            ·
              refine ⟨50874197406008241883908131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33916131604005494589272087 50874197406008241883908131)
              ·
                refine ⟨76311296109012362825862197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50874197406008241883908131 76311296109012362825862197)
                ·
                  refine ⟨7154184010219909014924581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76311296109012362825862197 7154184010219909014924581)
                  ·
                    refine ⟨1341409501916232940298359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7154184010219909014924581 1341409501916232940298359)
                    ·
                      rfl

theorem cell23_7837157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 5, 4].length) (baseStart_7837157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837157 prefixEnd_7837157 := by exact prefixLift 7837157
  have htrace : WordTrace (prefixWord ++ tailWord_7837157) baseStart_7837157 baseEnd_7837157 := by
    simpa [prefixWord, tailWord_7837157, baseEnd_7837157] using wordTrace_append hprefix tailTrace_7837157
  have hstable : (prefixWord ++ tailWord_7837157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837157).length < 2 ^ (prefixWord ++ tailWord_7837157).sum := by decide
  have hdescent : baseEnd_7837157 < baseStart_7837157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837167 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 3]
def baseStart_7837167 : Nat := 118140960795 + 7837167 * 2 ^ 59
def prefixEnd_7837167 : Nat := 4983230072969 + 3 ^ 40 * 7837167 * 2
def baseEnd_7837167 : Nat := 4024233640555243781770031

theorem tailTrace_7837167 : CollatzResearch.WordTrace tailWord_7837167 prefixEnd_7837167 4024233640555243781770031 := by
  unfold tailWord_7837167
  simp only [CollatzResearch.WordTrace]
  refine ⟨285844963598289915406749755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190563309065526610271166503 285844963598289915406749755)
  ·
    refine ⟨428767445397434873110124633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285844963598289915406749755 428767445397434873110124633)
    ·
      refine ⟨321575584048076154832593475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428767445397434873110124633 321575584048076154832593475)
      ·
        refine ⟨482363376072114232248890213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321575584048076154832593475 482363376072114232248890213)
        ·
          refine ⟨90443133013521418546666915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 482363376072114232248890213 90443133013521418546666915)
          ·
            refine ⟨135664699520282127820000373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90443133013521418546666915 135664699520282127820000373)
            ·
              refine ⟨12718565580026449483125035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135664699520282127820000373 12718565580026449483125035)
              ·
                refine ⟨19077848370039674224687553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12718565580026449483125035 19077848370039674224687553)
                ·
                  refine ⟨14308386277529755668515665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19077848370039674224687553 14308386277529755668515665)
                  ·
                    refine ⟨10731289708147316751386749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14308386277529755668515665 10731289708147316751386749)
                    ·
                      refine ⟨4024233640555243781770031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10731289708147316751386749 4024233640555243781770031)
                      ·
                        rfl

theorem cell23_7837167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 2, 2, 3].length) (baseStart_7837167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837167 prefixEnd_7837167 := by exact prefixLift 7837167
  have htrace : WordTrace (prefixWord ++ tailWord_7837167) baseStart_7837167 baseEnd_7837167 := by
    simpa [prefixWord, tailWord_7837167, baseEnd_7837167] using wordTrace_append hprefix tailTrace_7837167
  have hstable : (prefixWord ++ tailWord_7837167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837167).length < 2 ^ (prefixWord ++ tailWord_7837167).sum := by decide
  have hdescent : baseEnd_7837167 < baseStart_7837167 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837217 : List Nat := [1, 2, 3, 2, 2, 2, 1, 4, 1, 5]
def baseStart_7837217 : Nat := 118140960795 + 7837217 * 2 ^ 59
def prefixEnd_7837217 : Nat := 4983230072969 + 3 ^ 40 * 7837217 * 2
def baseEnd_7837217 : Nat := 1341419771529322862048267

theorem tailTrace_7837217 : CollatzResearch.WordTrace tailWord_7837217 prefixEnd_7837217 1341419771529322862048267 := by
  unfold tailWord_7837217
  simp only [CollatzResearch.WordTrace]
  refine ⟨285846787248108773946069905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190564524832072515964046603 285846787248108773946069905)
  ·
    refine ⟨214385090436081580459552429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285846787248108773946069905 214385090436081580459552429)
    ·
      refine ⟨80394408913530592672332161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214385090436081580459552429 80394408913530592672332161)
      ·
        refine ⟨60295806685147944504249121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80394408913530592672332161 60295806685147944504249121)
        ·
          refine ⟨45221855013860958378186841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60295806685147944504249121 45221855013860958378186841)
          ·
            refine ⟨33916391260395718783640131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45221855013860958378186841 33916391260395718783640131)
            ·
              refine ⟨50874586890593578175460197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33916391260395718783640131 50874586890593578175460197)
              ·
                refine ⟨9538985041986295907898787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50874586890593578175460197 9538985041986295907898787)
                ·
                  refine ⟨14308477562979443861848181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9538985041986295907898787 14308477562979443861848181)
                  ·
                    refine ⟨1341419771529322862048267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14308477562979443861848181 1341419771529322862048267)
                    ·
                      rfl

theorem cell23_7837217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 5].length) (baseStart_7837217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837217 prefixEnd_7837217 := by exact prefixLift 7837217
  have htrace : WordTrace (prefixWord ++ tailWord_7837217) baseStart_7837217 baseEnd_7837217 := by
    simpa [prefixWord, tailWord_7837217, baseEnd_7837217] using wordTrace_append hprefix tailTrace_7837217
  have hstable : (prefixWord ++ tailWord_7837217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837217).length < 2 ^ (prefixWord ++ tailWord_7837217).sum := by decide
  have hdescent : baseEnd_7837217 < baseStart_7837217 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837247 : List Nat := [1, 1, 2, 2, 3, 3, 2, 1, 4, 4]
def baseStart_7837247 : Nat := 118140960795 + 7837247 * 2 ^ 59
def prefixEnd_7837247 : Nat := 4983230072969 + 3 ^ 40 * 7837247 * 2
def baseEnd_7837247 : Nat := 1341424906335867822923221

theorem tailTrace_7837247 : CollatzResearch.WordTrace tailWord_7837247 prefixEnd_7837247 1341424906335867822923221 := by
  unfold tailWord_7837247
  simp only [CollatzResearch.WordTrace]
  refine ⟨285847881438000089069661995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190565254292000059379774663 285847881438000089069661995)
  ·
    refine ⟨428771822157000133604492993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285847881438000089069661995 428771822157000133604492993)
    ·
      refine ⟨321578866617750100203369745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428771822157000133604492993 321578866617750100203369745)
      ·
        refine ⟨241184149963312575152527309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321578866617750100203369745 241184149963312575152527309)
        ·
          refine ⟨90444056236242215682197741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241184149963312575152527309 90444056236242215682197741)
          ·
            refine ⟨33916521088590830880824153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90444056236242215682197741 33916521088590830880824153)
            ·
              refine ⟨25437390816443123160618115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33916521088590830880824153 25437390816443123160618115)
              ·
                refine ⟨38156086224664684740927173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25437390816443123160618115 38156086224664684740927173)
                ·
                  refine ⟨7154266167124628388923845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38156086224664684740927173 7154266167124628388923845)
                  ·
                    refine ⟨1341424906335867822923221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7154266167124628388923845 1341424906335867822923221)
                    ·
                      rfl

theorem cell23_7837247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 4, 4].length) (baseStart_7837247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837247 prefixEnd_7837247 := by exact prefixLift 7837247
  have htrace : WordTrace (prefixWord ++ tailWord_7837247) baseStart_7837247 baseEnd_7837247 := by
    simpa [prefixWord, tailWord_7837247, baseEnd_7837247] using wordTrace_append hprefix tailTrace_7837247
  have hstable : (prefixWord ++ tailWord_7837247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837247).length < 2 ^ (prefixWord ++ tailWord_7837247).sum := by decide
  have hdescent : baseEnd_7837247 < baseStart_7837247 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837260 : List Nat := [2, 2, 1, 3, 1, 3, 1, 10]
def baseStart_7837260 : Nat := 118140960795 + 7837260 * 2 ^ 59
def prefixEnd_7837260 : Nat := 4983230072969 + 3 ^ 40 * 7837260 * 2
def baseEnd_7837260 : Nat := 149047459046522663626189

theorem tailTrace_7837260 : CollatzResearch.WordTrace tailWord_7837260 prefixEnd_7837260 149047459046522663626189 := by
  unfold tailWord_7837260
  simp only [CollatzResearch.WordTrace]
  refine ⟨142924177793476496144942617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190565570391301994859923489 142924177793476496144942617)
  ·
    refine ⟨107193133345107372108706963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142924177793476496144942617 107193133345107372108706963)
    ·
      refine ⟨160789700017661058163060445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107193133345107372108706963 160789700017661058163060445)
      ·
        refine ⟨60296137506622896811147667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160789700017661058163060445 60296137506622896811147667)
        ·
          refine ⟨90444206259934345216721501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60296137506622896811147667 90444206259934345216721501)
          ·
            refine ⟨33916577347475379456270563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90444206259934345216721501 33916577347475379456270563)
            ·
              refine ⟨50874866021213069184405845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33916577347475379456270563 50874866021213069184405845)
              ·
                refine ⟨149047459046522663626189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50874866021213069184405845 149047459046522663626189)
                ·
                  rfl

theorem cell23_7837260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 10].length) (baseStart_7837260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837260 prefixEnd_7837260 := by exact prefixLift 7837260
  have htrace : WordTrace (prefixWord ++ tailWord_7837260) baseStart_7837260 baseEnd_7837260 := by
    simpa [prefixWord, tailWord_7837260, baseEnd_7837260] using wordTrace_append hprefix tailTrace_7837260
  have hstable : (prefixWord ++ tailWord_7837260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837260).length < 2 ^ (prefixWord ++ tailWord_7837260).sum := by decide
  have hdescent : baseEnd_7837260 < baseStart_7837260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837287 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 3]
def baseStart_7837287 : Nat := 118140960795 + 7837287 * 2 ^ 59
def prefixEnd_7837287 : Nat := 4983230072969 + 3 ^ 40 * 7837287 * 2
def baseEnd_7837287 : Nat := 4024295258233783312269479

theorem tailTrace_7837287 : CollatzResearch.WordTrace tailWord_7837287 prefixEnd_7837287 4024295258233783312269479 := by
  unfold tailWord_7837287
  simp only [CollatzResearch.WordTrace]
  refine ⟨285849340357855175901118115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190566226905236783934078743 285849340357855175901118115)
  ·
    refine ⟨428774010536782763851677173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285849340357855175901118115 428774010536782763851677173)
    ·
      refine ⟨40197563487823384111094735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 428774010536782763851677173 40197563487823384111094735)
      ·
        refine ⟨60296345231735076166642103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40197563487823384111094735 60296345231735076166642103)
        ·
          refine ⟨90444517847602614249963155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60296345231735076166642103 90444517847602614249963155)
          ·
            refine ⟨135666776771403921374944733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90444517847602614249963155 135666776771403921374944733)
            ·
              refine ⟨50875041289276470515604275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135666776771403921374944733 50875041289276470515604275)
              ·
                refine ⟨76312561933914705773406413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50875041289276470515604275 76312561933914705773406413)
                ·
                  refine ⟨28617210725218014665027405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76312561933914705773406413 28617210725218014665027405)
                  ·
                    refine ⟨10731454021956755499385277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28617210725218014665027405 10731454021956755499385277)
                    ·
                      refine ⟨4024295258233783312269479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10731454021956755499385277 4024295258233783312269479)
                      ·
                        rfl

theorem cell23_7837287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 3, 3, 3].length) (baseStart_7837287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837287 prefixEnd_7837287 := by exact prefixLift 7837287
  have htrace : WordTrace (prefixWord ++ tailWord_7837287) baseStart_7837287 baseEnd_7837287 := by
    simpa [prefixWord, tailWord_7837287, baseEnd_7837287] using wordTrace_append hprefix tailTrace_7837287
  have hstable : (prefixWord ++ tailWord_7837287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837287).length < 2 ^ (prefixWord ++ tailWord_7837287).sum := by decide
  have hdescent : baseEnd_7837287 < baseStart_7837287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837348 : List Nat := [2, 3, 1, 2, 2, 2, 4, 1, 1, 3, 2]
def baseStart_7837348 : Nat := 118140960795 + 7837348 * 2 ^ 59
def prefixEnd_7837348 : Nat := 4983230072969 + 3 ^ 40 * 7837348 * 2
def baseEnd_7837348 : Nat := 4024326580553707573606699

theorem tailTrace_7837348 : CollatzResearch.WordTrace tailWord_7837348 prefixEnd_7837348 4024326580553707573606699 := by
  unfold tailWord_7837348
  simp only [CollatzResearch.WordTrace]
  refine ⟨142925782605317091659544349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190567710140422788879392465 142925782605317091659544349)
  ·
    refine ⟨53597168476993909372329131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142925782605317091659544349 53597168476993909372329131)
    ·
      refine ⟨80395752715490864058493697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53597168476993909372329131 80395752715490864058493697)
      ·
        refine ⟨60296814536618148043870273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80395752715490864058493697 60296814536618148043870273)
        ·
          refine ⟨45222610902463611032902705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60296814536618148043870273 45222610902463611032902705)
          ·
            refine ⟨33916958176847708274677029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45222610902463611032902705 33916958176847708274677029)
            ·
              refine ⟨6359429658158945301501943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33916958176847708274677029 6359429658158945301501943)
              ·
                refine ⟨9539144487238417952252915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6359429658158945301501943 9539144487238417952252915)
                ·
                  refine ⟨14308716730857626928379373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9539144487238417952252915 14308716730857626928379373)
                  ·
                    refine ⟨5365768774071610098142265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14308716730857626928379373 5365768774071610098142265)
                    ·
                      refine ⟨4024326580553707573606699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365768774071610098142265 4024326580553707573606699)
                      ·
                        rfl

theorem cell23_7837348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_7837348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837348 prefixEnd_7837348 := by exact prefixLift 7837348
  have htrace : WordTrace (prefixWord ++ tailWord_7837348) baseStart_7837348 baseEnd_7837348 := by
    simpa [prefixWord, tailWord_7837348, baseEnd_7837348] using wordTrace_append hprefix tailTrace_7837348
  have hstable : (prefixWord ++ tailWord_7837348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837348).length < 2 ^ (prefixWord ++ tailWord_7837348).sum := by decide
  have hdescent : baseEnd_7837348 < baseStart_7837348 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837367 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 7]
def baseStart_7837367 : Nat := 118140960795 + 7837367 * 2 ^ 59
def prefixEnd_7837367 : Nat := 4983230072969 + 3 ^ 40 * 7837367 * 2
def baseEnd_7837367 : Nat := 447148481854015888807679

theorem tailTrace_7837367 : CollatzResearch.WordTrace tailWord_7837367 prefixEnd_7837367 447148481854015888807679 := by
  unfold tailWord_7837367
  simp only [CollatzResearch.WordTrace]
  refine ⟨285852258197565349564030355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190568172131710233042686903 285852258197565349564030355)
  ·
    refine ⟨428778387296348024346045533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285852258197565349564030355 428778387296348024346045533)
    ·
      refine ⟨160791895236130509129767075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428778387296348024346045533 160791895236130509129767075)
      ·
        refine ⟨241187842854195763694650613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160791895236130509129767075 241187842854195763694650613)
        ·
          refine ⟨22611360267580852846373495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241187842854195763694650613 22611360267580852846373495)
          ·
            refine ⟨33917040401371279269560243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22611360267580852846373495 33917040401371279269560243)
            ·
              refine ⟨50875560602056918904340365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33917040401371279269560243 50875560602056918904340365)
              ·
                refine ⟨19078335225771344589127637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50875560602056918904340365 19078335225771344589127637)
                ·
                  refine ⟨447148481854015888807679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19078335225771344589127637 447148481854015888807679)
                  ·
                    rfl

theorem cell23_7837367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 7].length) (baseStart_7837367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837367 prefixEnd_7837367 := by exact prefixLift 7837367
  have htrace : WordTrace (prefixWord ++ tailWord_7837367) baseStart_7837367 baseEnd_7837367 := by
    simpa [prefixWord, tailWord_7837367, baseEnd_7837367] using wordTrace_append hprefix tailTrace_7837367
  have hstable : (prefixWord ++ tailWord_7837367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837367).length < 2 ^ (prefixWord ++ tailWord_7837367).sum := by decide
  have hdescent : baseEnd_7837367 < baseStart_7837367 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837374 : List Nat := [4, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_7837374 : Nat := 118140960795 + 7837374 * 2 ^ 59
def prefixEnd_7837374 : Nat := 4983230072969 + 3 ^ 40 * 7837374 * 2
def baseEnd_7837374 : Nat := 4024339931050724471881579

theorem tailTrace_7837374 : CollatzResearch.WordTrace tailWord_7837374 prefixEnd_7837374 4024339931050724471881579 := by
  unfold tailWord_7837374
  simp only [CollatzResearch.WordTrace]
  refine ⟨35731564188567498719941897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190568342339026659839690117 35731564188567498719941897)
  ·
    refine ⟨26798673141425624039956423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35731564188567498719941897 26798673141425624039956423)
    ·
      refine ⟨40198009712138436059934635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26798673141425624039956423 40198009712138436059934635)
      ·
        refine ⟨60297014568207654089901953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40198009712138436059934635 60297014568207654089901953)
        ·
          refine ⟨45222760926155740567426465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60297014568207654089901953 45222760926155740567426465)
          ·
            refine ⟨33917070694616805425569849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45222760926155740567426465 33917070694616805425569849)
            ·
              refine ⟨25437803020962604069177387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33917070694616805425569849 25437803020962604069177387)
              ·
                refine ⟨38156704531443906103766081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25437803020962604069177387 38156704531443906103766081)
                ·
                  refine ⟨28617528398582929577824561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38156704531443906103766081 28617528398582929577824561)
                  ·
                    refine ⟨21463146298937197183368421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28617528398582929577824561 21463146298937197183368421)
                    ·
                      refine ⟨4024339931050724471881579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21463146298937197183368421 4024339931050724471881579)
                      ·
                        rfl

theorem cell23_7837374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_7837374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837374 prefixEnd_7837374 := by exact prefixLift 7837374
  have htrace : WordTrace (prefixWord ++ tailWord_7837374) baseStart_7837374 baseEnd_7837374 := by
    simpa [prefixWord, tailWord_7837374, baseEnd_7837374] using wordTrace_append hprefix tailTrace_7837374
  have hstable : (prefixWord ++ tailWord_7837374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837374).length < 2 ^ (prefixWord ++ tailWord_7837374).sum := by decide
  have hdescent : baseEnd_7837374 < baseStart_7837374 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837382 : List Nat := [6, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_7837382 : Nat := 118140960795 + 7837382 * 2 ^ 59
def prefixEnd_7837382 : Nat := 4983230072969 + 3 ^ 40 * 7837382 * 2
def baseEnd_7837382 : Nat := 4024344038895960440581543

theorem tailTrace_7837382 : CollatzResearch.WordTrace tailWord_7837382 prefixEnd_7837382 4024344038895960440581543 := by
  unfold tailWord_7837382
  simp only [CollatzResearch.WordTrace]
  refine ⟨8932900165390968972682075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190568536861674004750550933 8932900165390968972682075)
  ·
    refine ⟨13399350248086453459023113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8932900165390968972682075 13399350248086453459023113)
    ·
      refine ⟨10049512686064840094267335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13399350248086453459023113 10049512686064840094267335)
      ·
        refine ⟨15074269029097260141401003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10049512686064840094267335 15074269029097260141401003)
        ·
          refine ⟨22611403543645890212101505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15074269029097260141401003 22611403543645890212101505)
          ·
            refine ⟨16958552657734417659076129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22611403543645890212101505 16958552657734417659076129)
            ·
              refine ⟨12718914493300813244307097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16958552657734417659076129 12718914493300813244307097)
              ·
                refine ⟨9539185869975609933230323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12718914493300813244307097 9539185869975609933230323)
                ·
                  refine ⟨14308778804963414899845485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9539185869975609933230323 14308778804963414899845485)
                  ·
                    refine ⟨5365792051861280587442057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14308778804963414899845485 5365792051861280587442057)
                    ·
                      refine ⟨4024344038895960440581543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365792051861280587442057 4024344038895960440581543)
                      ·
                        rfl

theorem cell23_7837382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_7837382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837382 prefixEnd_7837382 := by exact prefixLift 7837382
  have htrace : WordTrace (prefixWord ++ tailWord_7837382) baseStart_7837382 baseEnd_7837382 := by
    simpa [prefixWord, tailWord_7837382, baseEnd_7837382] using wordTrace_append hprefix tailTrace_7837382
  have hstable : (prefixWord ++ tailWord_7837382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837382).length < 2 ^ (prefixWord ++ tailWord_7837382).sum := by decide
  have hdescent : baseEnd_7837382 < baseStart_7837382 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837398 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 2, 1, 5]
def baseStart_7837398 : Nat := 118140960795 + 7837398 * 2 ^ 59
def prefixEnd_7837398 : Nat := 4983230072969 + 3 ^ 40 * 7837398 * 2
def baseEnd_7837398 : Nat := 4024352254586432377981469

theorem tailTrace_7837398 : CollatzResearch.WordTrace tailWord_7837398 prefixEnd_7837398 4024352254586432377981469 := by
  unfold tailWord_7837398
  simp only [CollatzResearch.WordTrace]
  refine ⟨17865836803778315116150553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190568925906968694572272565 17865836803778315116150553)
  ·
    refine ⟨13399377602833736337112915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17865836803778315116150553 13399377602833736337112915)
    ·
      refine ⟨20099066404250604505669373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13399377602833736337112915 20099066404250604505669373)
      ·
        refine ⟨7537149901593976689626015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20099066404250604505669373 7537149901593976689626015)
        ·
          refine ⟨11305724852390965034439023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7537149901593976689626015 11305724852390965034439023)
          ·
            refine ⟨16958587278586447551658535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11305724852390965034439023 16958587278586447551658535)
            ·
              refine ⟨25437880917879671327487803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16958587278586447551658535 25437880917879671327487803)
              ·
                refine ⟨38156821376819506991231705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25437880917879671327487803 38156821376819506991231705)
                ·
                  refine ⟨28617616032614630243423779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38156821376819506991231705 28617616032614630243423779)
                  ·
                    refine ⟨42926424048921945365135669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28617616032614630243423779 42926424048921945365135669)
                    ·
                      refine ⟨4024352254586432377981469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42926424048921945365135669 4024352254586432377981469)
                      ·
                        rfl

theorem cell23_7837398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_7837398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837398 prefixEnd_7837398 := by exact prefixLift 7837398
  have htrace : WordTrace (prefixWord ++ tailWord_7837398) baseStart_7837398 baseEnd_7837398 := by
    simpa [prefixWord, tailWord_7837398, baseEnd_7837398] using wordTrace_append hprefix tailTrace_7837398
  have hstable : (prefixWord ++ tailWord_7837398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837398).length < 2 ^ (prefixWord ++ tailWord_7837398).sum := by decide
  have hdescent : baseEnd_7837398 < baseStart_7837398 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837401 : List Nat := [1, 2, 1, 2, 3, 5, 1, 3, 5]
def baseStart_7837401 : Nat := 118140960795 + 7837401 * 2 ^ 59
def prefixEnd_7837401 : Nat := 4983230072969 + 3 ^ 40 * 7837401 * 2
def baseEnd_7837401 : Nat := 447150421669821762915995

theorem tailTrace_7837401 : CollatzResearch.WordTrace tailWord_7837401 prefixEnd_7837401 447150421669821762915995 := by
  unfold tailWord_7837401
  simp only [CollatzResearch.WordTrace]
  refine ⟨285853498279442173370768057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190568998852961448913845371 285853498279442173370768057)
  ·
    refine ⟨214390123709581630028076043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285853498279442173370768057 214390123709581630028076043)
    ·
      refine ⟨321585185564372445042114065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214390123709581630028076043 321585185564372445042114065)
      ·
        refine ⟨241188889173279333781585549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321585185564372445042114065 241188889173279333781585549)
        ·
          refine ⟨90445833439979750168094581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241188889173279333781585549 90445833439979750168094581)
          ·
            refine ⟨8479296884998101578258867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90445833439979750168094581 8479296884998101578258867)
            ·
              refine ⟨12718945327497152367388301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8479296884998101578258867 12718945327497152367388301)
              ·
                refine ⟨4769604497811432137770613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12718945327497152367388301 4769604497811432137770613)
                ·
                  refine ⟨447150421669821762915995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4769604497811432137770613 447150421669821762915995)
                  ·
                    rfl

theorem cell23_7837401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 5, 1, 3, 5].length) (baseStart_7837401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837401 prefixEnd_7837401 := by exact prefixLift 7837401
  have htrace : WordTrace (prefixWord ++ tailWord_7837401) baseStart_7837401 baseEnd_7837401 := by
    simpa [prefixWord, tailWord_7837401, baseEnd_7837401] using wordTrace_append hprefix tailTrace_7837401
  have hstable : (prefixWord ++ tailWord_7837401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837401).length < 2 ^ (prefixWord ++ tailWord_7837401).sum := by decide
  have hdescent : baseEnd_7837401 < baseStart_7837401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837407 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 5]
def baseStart_7837407 : Nat := 118140960795 + 7837407 * 2 ^ 59
def prefixEnd_7837407 : Nat := 4983230072969 + 3 ^ 40 * 7837407 * 2
def baseEnd_7837407 : Nat := 4024356875912322842768927

theorem tailTrace_7837407 : CollatzResearch.WordTrace tailWord_7837407 prefixEnd_7837407 4024356875912322842768927 := by
  unfold tailWord_7837407
  simp only [CollatzResearch.WordTrace]
  refine ⟨285853717117420436395486475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190569144744946957596990983 285853717117420436395486475)
  ·
    refine ⟨428780575676130654593229713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285853717117420436395486475 428780575676130654593229713)
    ·
      refine ⟨321585431757097990944922285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428780575676130654593229713 321585431757097990944922285)
      ·
        refine ⟨120594536908911746604345857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321585431757097990944922285 120594536908911746604345857)
        ·
          refine ⟨90445902681683809953259393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120594536908911746604345857 90445902681683809953259393)
          ·
            refine ⟨67834427011262857464944545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90445902681683809953259393 67834427011262857464944545)
            ·
              refine ⟨50875820258447143098708409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67834427011262857464944545 50875820258447143098708409)
              ·
                refine ⟨38156865193835357324031307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50875820258447143098708409 38156865193835357324031307)
                ·
                  refine ⟨57235297790753035986046961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38156865193835357324031307 57235297790753035986046961)
                  ·
                    refine ⟨42926473343064776989535221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57235297790753035986046961 42926473343064776989535221)
                    ·
                      refine ⟨4024356875912322842768927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42926473343064776989535221 4024356875912322842768927)
                      ·
                        rfl

theorem cell23_7837407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_7837407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837407 prefixEnd_7837407 := by exact prefixLift 7837407
  have htrace : WordTrace (prefixWord ++ tailWord_7837407) baseStart_7837407 baseEnd_7837407 := by
    simpa [prefixWord, tailWord_7837407, baseEnd_7837407] using wordTrace_append hprefix tailTrace_7837407
  have hstable : (prefixWord ++ tailWord_7837407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837407).length < 2 ^ (prefixWord ++ tailWord_7837407).sum := by decide
  have hdescent : baseEnd_7837407 < baseStart_7837407 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837434 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2]
def baseStart_7837434 : Nat := 118140960795 + 7837434 * 2 ^ 59
def prefixEnd_7837434 : Nat := 4983230072969 + 3 ^ 40 * 7837434 * 2
def baseEnd_7837434 : Nat := 4024370739889994237131303

theorem tailTrace_7837434 : CollatzResearch.WordTrace tailWord_7837434 prefixEnd_7837434 4024370739889994237131303 := by
  unfold tailWord_7837434
  simp only [CollatzResearch.WordTrace]
  refine ⟨71463675472080655001679839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190569801258881746671146237 71463675472080655001679839)
  ·
    refine ⟨107195513208120982502519759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71463675472080655001679839 107195513208120982502519759)
    ·
      refine ⟨160793269812181473753779639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107195513208120982502519759 160793269812181473753779639)
      ·
        refine ⟨241189904718272210630669459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160793269812181473753779639 241189904718272210630669459)
        ·
          refine ⟨361784857077408315946004189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241189904718272210630669459 361784857077408315946004189)
          ·
            refine ⟨135669321404028118479751571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361784857077408315946004189 135669321404028118479751571)
            ·
              refine ⟨203503982106042177719627357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135669321404028118479751571 203503982106042177719627357)
              ·
                refine ⟨76313993289765816644860259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203503982106042177719627357 76313993289765816644860259)
                ·
                  refine ⟨114470989934648724967290389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76313993289765816644860259 114470989934648724967290389)
                  ·
                    refine ⟨5365827653186658982841737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114470989934648724967290389 5365827653186658982841737)
                    ·
                      refine ⟨4024370739889994237131303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365827653186658982841737 4024370739889994237131303)
                      ·
                        rfl

theorem cell23_7837434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 1, 6, 2].length) (baseStart_7837434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837434 prefixEnd_7837434 := by exact prefixLift 7837434
  have htrace : WordTrace (prefixWord ++ tailWord_7837434) baseStart_7837434 baseEnd_7837434 := by
    simpa [prefixWord, tailWord_7837434, baseEnd_7837434] using wordTrace_append hprefix tailTrace_7837434
  have hstable : (prefixWord ++ tailWord_7837434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837434).length < 2 ^ (prefixWord ++ tailWord_7837434).sum := by decide
  have hdescent : baseEnd_7837434 < baseStart_7837434 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837454 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_7837454 : Nat := 118140960795 + 7837454 * 2 ^ 59
def prefixEnd_7837454 : Nat := 4983230072969 + 3 ^ 40 * 7837454 * 2
def baseEnd_7837454 : Nat := 4024381009503084158881211

theorem tailTrace_7837454 : CollatzResearch.WordTrace tailWord_7837454 prefixEnd_7837454 4024381009503084158881211 := by
  unfold tailWord_7837454
  simp only [CollatzResearch.WordTrace]
  refine ⟨35731928918531270427805927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190570287565500108948298277 35731928918531270427805927)
  ·
    refine ⟨53597893377796905641708891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35731928918531270427805927 53597893377796905641708891)
    ·
      refine ⟨80396840066695358462563337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53597893377796905641708891 80396840066695358462563337)
      ·
        refine ⟨60297630050021518846922503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80396840066695358462563337 60297630050021518846922503)
        ·
          refine ⟨90446445075032278270383755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60297630050021518846922503 90446445075032278270383755)
          ·
            refine ⟨135669667612548417405575633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90446445075032278270383755 135669667612548417405575633)
            ·
              refine ⟨101752250709411313054181725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135669667612548417405575633 101752250709411313054181725)
              ·
                refine ⟨38157094016029242395318147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101752250709411313054181725 38157094016029242395318147)
                ·
                  refine ⟨57235641024043863592977221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38157094016029242395318147 57235641024043863592977221)
                  ·
                    refine ⟨10731682692008224423683229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57235641024043863592977221 10731682692008224423683229)
                    ·
                      refine ⟨4024381009503084158881211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10731682692008224423683229 4024381009503084158881211)
                      ·
                        rfl

theorem cell23_7837454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_7837454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837454 prefixEnd_7837454 := by exact prefixLift 7837454
  have htrace : WordTrace (prefixWord ++ tailWord_7837454) baseStart_7837454 baseEnd_7837454 := by
    simpa [prefixWord, tailWord_7837454, baseEnd_7837454] using wordTrace_append hprefix tailTrace_7837454
  have hstable : (prefixWord ++ tailWord_7837454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837454).length < 2 ^ (prefixWord ++ tailWord_7837454).sum := by decide
  have hdescent : baseEnd_7837454 < baseStart_7837454 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837521 : List Nat := [1, 2, 2, 1, 5, 2, 1, 3, 1, 5]
def baseStart_7837521 : Nat := 118140960795 + 7837521 * 2 ^ 59
def prefixEnd_7837521 : Nat := 4983230072969 + 3 ^ 40 * 7837521 * 2
def baseEnd_7837521 : Nat := 1341471804235645132247801

theorem tailTrace_7837521 : CollatzResearch.WordTrace tailWord_7837521 prefixEnd_7837521 1341471804235645132247801 := by
  unfold tailWord_7837521
  simp only [CollatzResearch.WordTrace]
  refine ⟨285857875039007433865136417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190571916692671622576757611 285857875039007433865136417)
  ·
    refine ⟨214393406279255575398852313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285857875039007433865136417 214393406279255575398852313)
    ·
      refine ⟨160795054709441681549139235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214393406279255575398852313 160795054709441681549139235)
      ·
        refine ⟨241192582064162522323708853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160795054709441681549139235 241192582064162522323708853)
        ·
          refine ⟨22611804568515236467847705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241192582064162522323708853 22611804568515236467847705)
          ·
            refine ⟨16958853426386427350885779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22611804568515236467847705 16958853426386427350885779)
            ·
              refine ⟨25438280139579641026328669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16958853426386427350885779 25438280139579641026328669)
              ·
                refine ⟨9539355052342365384873251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25438280139579641026328669 9539355052342365384873251)
                ·
                  refine ⟨14309032578513548077309877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9539355052342365384873251 14309032578513548077309877)
                  ·
                    refine ⟨1341471804235645132247801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14309032578513548077309877 1341471804235645132247801)
                    ·
                      rfl

theorem cell23_7837521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 1, 5].length) (baseStart_7837521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837521 prefixEnd_7837521 := by exact prefixLift 7837521
  have htrace : WordTrace (prefixWord ++ tailWord_7837521) baseStart_7837521 baseEnd_7837521 := by
    simpa [prefixWord, tailWord_7837521, baseEnd_7837521] using wordTrace_append hprefix tailTrace_7837521
  have hstable : (prefixWord ++ tailWord_7837521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837521).length < 2 ^ (prefixWord ++ tailWord_7837521).sum := by decide
  have hdescent : baseEnd_7837521 < baseStart_7837521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837547 : List Nat := [1, 1, 1, 1, 2, 2, 3, 12]
def baseStart_7837547 : Nat := 118140960795 + 7837547 * 2 ^ 59
def prefixEnd_7837547 : Nat := 4983230072969 + 3 ^ 40 * 7837547 * 2
def baseEnd_7837547 : Nat := 149052917155701936852529

theorem tailTrace_7837547 : CollatzResearch.WordTrace tailWord_7837547 prefixEnd_7837547 149052917155701936852529 := by
  unfold tailWord_7837547
  simp only [CollatzResearch.WordTrace]
  refine ⟨285858823336913240305582895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190572548891275493537055263 285858823336913240305582895)
  ·
    refine ⟨428788235005369860458374343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285858823336913240305582895 428788235005369860458374343)
    ·
      refine ⟨643182352508054790687561515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428788235005369860458374343 643182352508054790687561515)
      ·
        refine ⟨964773528762082186031342273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643182352508054790687561515 964773528762082186031342273)
        ·
          refine ⟨723580146571561639523506705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 964773528762082186031342273 723580146571561639523506705)
          ·
            refine ⟨542685109928671229642630029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723580146571561639523506705 542685109928671229642630029)
            ·
              refine ⟨203506916223251711115986261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 542685109928671229642630029 203506916223251711115986261)
              ·
                refine ⟨149052917155701936852529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 203506916223251711115986261 149052917155701936852529)
                ·
                  rfl

theorem cell23_7837547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 12].length) (baseStart_7837547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837547 prefixEnd_7837547 := by exact prefixLift 7837547
  have htrace : WordTrace (prefixWord ++ tailWord_7837547) baseStart_7837547 baseEnd_7837547 := by
    simpa [prefixWord, tailWord_7837547, baseEnd_7837547] using wordTrace_append hprefix tailTrace_7837547
  have hstable : (prefixWord ++ tailWord_7837547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837547).length < 2 ^ (prefixWord ++ tailWord_7837547).sum := by decide
  have hdescent : baseEnd_7837547 < baseStart_7837547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837569 : List Nat := [1, 2, 4, 4, 1, 2, 1, 3, 1, 1, 3]
def baseStart_7837569 : Nat := 118140960795 + 7837569 * 2 ^ 59
def prefixEnd_7837569 : Nat := 4983230072969 + 3 ^ 40 * 7837569 * 2
def baseEnd_7837569 : Nat := 4024440059778351208943183

theorem tailTrace_7837569 : CollatzResearch.WordTrace tailWord_7837569 prefixEnd_7837569 4024440059778351208943183 := by
  unfold tailWord_7837569
  simp only [CollatzResearch.WordTrace]
  refine ⟨285859625742833538062883761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190573083828555692041922507 285859625742833538062883761)
  ·
    refine ⟨214394719307125153547162821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285859625742833538062883761 214394719307125153547162821)
    ·
      refine ⟨40199009870085966290093029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214394719307125153547162821 40199009870085966290093029)
      ·
        refine ⟨7537314350641118679392443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 40199009870085966290093029 7537314350641118679392443)
        ·
          refine ⟨11305971525961678019088665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7537314350641118679392443 11305971525961678019088665)
          ·
            refine ⟨8479478644471258514316499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11305971525961678019088665 8479478644471258514316499)
            ·
              refine ⟨12719217966706887771474749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8479478644471258514316499 12719217966706887771474749)
              ·
                refine ⟨4769706737515082914303031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12719217966706887771474749 4769706737515082914303031)
                ·
                  refine ⟨7154560106272624371454547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4769706737515082914303031 7154560106272624371454547)
                  ·
                    refine ⟨10731840159408936557181821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7154560106272624371454547 10731840159408936557181821)
                    ·
                      refine ⟨4024440059778351208943183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10731840159408936557181821 4024440059778351208943183)
                      ·
                        rfl

theorem cell23_7837569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_7837569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837569 prefixEnd_7837569 := by exact prefixLift 7837569
  have htrace : WordTrace (prefixWord ++ tailWord_7837569) baseStart_7837569 baseEnd_7837569 := by
    simpa [prefixWord, tailWord_7837569, baseEnd_7837569] using wordTrace_append hprefix tailTrace_7837569
  have hstable : (prefixWord ++ tailWord_7837569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837569).length < 2 ^ (prefixWord ++ tailWord_7837569).sum := by decide
  have hdescent : baseEnd_7837569 < baseStart_7837569 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837578 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 1, 1, 5]
def baseStart_7837578 : Nat := 118140960795 + 7837578 * 2 ^ 59
def prefixEnd_7837578 : Nat := 4983230072969 + 3 ^ 40 * 7837578 * 2
def baseEnd_7837578 : Nat := 4024444681104241673730641

theorem tailTrace_7837578 : CollatzResearch.WordTrace tailWord_7837578 prefixEnd_7837578 4024444681104241673730641 := by
  unfold tailWord_7837578
  simp only [CollatzResearch.WordTrace]
  refine ⟨71464988499950233149990347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190573302666533955066640925 71464988499950233149990347)
  ·
    refine ⟨107197482749925349724985521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71464988499950233149990347 107197482749925349724985521)
    ·
      refine ⟨80398112062444012293739141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107197482749925349724985521 80398112062444012293739141)
      ·
        refine ⟨15074646011708252305076089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 80398112062444012293739141 15074646011708252305076089)
        ·
          refine ⟨11305984508781189228807067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15074646011708252305076089 11305984508781189228807067)
          ·
            refine ⟨16958976763171783843210601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11305984508781189228807067 16958976763171783843210601)
            ·
              refine ⟨12719232572378837882407951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16958976763171783843210601 12719232572378837882407951)
              ·
                refine ⟨19078848858568256823611927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12719232572378837882407951 19078848858568256823611927)
                ·
                  refine ⟨28618273287852385235417891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19078848858568256823611927 28618273287852385235417891)
                  ·
                    refine ⟨42927409931778577853126837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28618273287852385235417891 42927409931778577853126837)
                    ·
                      refine ⟨4024444681104241673730641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42927409931778577853126837 4024444681104241673730641)
                      ·
                        rfl

theorem cell23_7837578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_7837578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837578 prefixEnd_7837578 := by exact prefixLift 7837578
  have htrace : WordTrace (prefixWord ++ tailWord_7837578) baseStart_7837578 baseEnd_7837578 := by
    simpa [prefixWord, tailWord_7837578, baseEnd_7837578] using wordTrace_append hprefix tailTrace_7837578
  have hstable : (prefixWord ++ tailWord_7837578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837578).length < 2 ^ (prefixWord ++ tailWord_7837578).sum := by decide
  have hdescent : baseEnd_7837578 < baseStart_7837578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837602 : List Nat := [3, 3, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_7837602 : Nat := 118140960795 + 7837602 * 2 ^ 59
def prefixEnd_7837602 : Nat := 4983230072969 + 3 ^ 40 * 7837602 * 2
def baseEnd_7837602 : Nat := 1341485668213316526610177

theorem tailTrace_7837602 : CollatzResearch.WordTrace tailWord_7837602 prefixEnd_7837602 1341485668213316526610177 := by
  unfold tailWord_7837602
  simp only [CollatzResearch.WordTrace]
  refine ⟨71465207337928496174708765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190573886234475989799223373 71465207337928496174708765)
  ·
    refine ⟨26799452751723186065515787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71465207337928496174708765 26799452751723186065515787)
    ·
      refine ⟨40199179127584779098273681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26799452751723186065515787 40199179127584779098273681)
      ·
        refine ⟨30149384345688584323705261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40199179127584779098273681 30149384345688584323705261)
        ·
          refine ⟨11306019129633219121389473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30149384345688584323705261 11306019129633219121389473)
          ·
            refine ⟨8479514347224914341042105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11306019129633219121389473 8479514347224914341042105)
            ·
              refine ⟨6359635760418685755781579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8479514347224914341042105 6359635760418685755781579)
              ·
                refine ⟨9539453640628028633672369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6359635760418685755781579 9539453640628028633672369)
                ·
                  refine ⟨7154590230471021475254277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9539453640628028633672369 7154590230471021475254277)
                  ·
                    refine ⟨1341485668213316526610177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7154590230471021475254277 1341485668213316526610177)
                    ·
                      rfl

theorem cell23_7837602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_7837602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837602 prefixEnd_7837602 := by exact prefixLift 7837602
  have htrace : WordTrace (prefixWord ++ tailWord_7837602) baseStart_7837602 baseEnd_7837602 := by
    simpa [prefixWord, tailWord_7837602, baseEnd_7837602] using wordTrace_append hprefix tailTrace_7837602
  have hstable : (prefixWord ++ tailWord_7837602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837602).length < 2 ^ (prefixWord ++ tailWord_7837602).sum := by decide
  have hdescent : baseEnd_7837602 < baseStart_7837602 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837648 : List Nat := [2, 1, 1, 1, 1, 2, 4, 3, 4, 2, 2]
def baseStart_7837648 : Nat := 118140960795 + 7837648 * 2 ^ 59
def prefixEnd_7837648 : Nat := 4983230072969 + 3 ^ 40 * 7837648 * 2
def baseEnd_7837648 : Nat := 4024480624750056399855319

theorem tailTrace_7837648 : CollatzResearch.WordTrace tailWord_7837648 prefixEnd_7837648 4024480624750056399855319 := by
  unfold tailWord_7837648
  simp only [CollatzResearch.WordTrace]
  refine ⟨142931253554773667277504799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190575004739698223036673065 142931253554773667277504799)
  ·
    refine ⟨214396880332160500916257199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142931253554773667277504799 214396880332160500916257199)
    ·
      refine ⟨321595320498240751374385799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214396880332160500916257199 321595320498240751374385799)
      ·
        refine ⟨482392980747361127061578699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321595320498240751374385799 482392980747361127061578699)
        ·
          refine ⟨723589471121041690592368049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482392980747361127061578699 723589471121041690592368049)
          ·
            refine ⟨542692103340781267944276037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 723589471121041690592368049 542692103340781267944276037)
            ·
              refine ⟨101754769376396487739551757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 542692103340781267944276037 101754769376396487739551757)
              ·
                refine ⟨38158038516148682902331909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101754769376396487739551757 38158038516148682902331909)
                ·
                  refine ⟨7154632221777878044187233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38158038516148682902331909 7154632221777878044187233)
                  ·
                    refine ⟨5365974166333408533140425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7154632221777878044187233 5365974166333408533140425)
                    ·
                      refine ⟨4024480624750056399855319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365974166333408533140425 4024480624750056399855319)
                      ·
                        rfl

theorem cell23_7837648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 3, 4, 2, 2].length) (baseStart_7837648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837648 prefixEnd_7837648 := by exact prefixLift 7837648
  have htrace : WordTrace (prefixWord ++ tailWord_7837648) baseStart_7837648 baseEnd_7837648 := by
    simpa [prefixWord, tailWord_7837648, baseEnd_7837648] using wordTrace_append hprefix tailTrace_7837648
  have hstable : (prefixWord ++ tailWord_7837648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837648).length < 2 ^ (prefixWord ++ tailWord_7837648).sum := by decide
  have hdescent : baseEnd_7837648 < baseStart_7837648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837665 : List Nat := [1, 2, 3, 1, 2, 1, 4, 3, 2, 2, 2]
def baseStart_7837665 : Nat := 118140960795 + 7837665 * 2 ^ 59
def prefixEnd_7837665 : Nat := 4983230072969 + 3 ^ 40 * 7837665 * 2
def baseEnd_7837665 : Nat := 4024489353921182833342741

theorem tailTrace_7837665 : CollatzResearch.WordTrace tailWord_7837665 prefixEnd_7837665 4024489353921182833342741 := by
  unfold tailWord_7837665
  simp only [CollatzResearch.WordTrace]
  refine ⟨285863127150485746458378449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190575418100323830972252299 285863127150485746458378449)
  ·
    refine ⟨214397345362864309843783837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285863127150485746458378449 214397345362864309843783837)
    ·
      refine ⟨80399004511074116191418939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214397345362864309843783837 80399004511074116191418939)
      ·
        refine ⟨120598506766611174287128409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80399004511074116191418939 120598506766611174287128409)
        ·
          refine ⟨90448880074958380715346307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120598506766611174287128409 90448880074958380715346307)
          ·
            refine ⟨135673320112437571073019461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90448880074958380715346307 135673320112437571073019461)
            ·
              refine ⟨25438747521082044576191149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135673320112437571073019461 25438747521082044576191149)
              ·
                refine ⟨9539530320405766716071681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25438747521082044576191149 9539530320405766716071681)
                ·
                  refine ⟨7154647740304325037053761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9539530320405766716071681 7154647740304325037053761)
                  ·
                    refine ⟨5365985805228243777790321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7154647740304325037053761 5365985805228243777790321)
                    ·
                      refine ⟨4024489353921182833342741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5365985805228243777790321 4024489353921182833342741)
                      ·
                        rfl

theorem cell23_7837665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_7837665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837665 prefixEnd_7837665 := by exact prefixLift 7837665
  have htrace : WordTrace (prefixWord ++ tailWord_7837665) baseStart_7837665 baseEnd_7837665 := by
    simpa [prefixWord, tailWord_7837665, baseEnd_7837665] using wordTrace_append hprefix tailTrace_7837665
  have hstable : (prefixWord ++ tailWord_7837665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837665).length < 2 ^ (prefixWord ++ tailWord_7837665).sum := by decide
  have hdescent : baseEnd_7837665 < baseStart_7837665 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837686 : List Nat := [5, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2]
def baseStart_7837686 : Nat := 118140960795 + 7837686 * 2 ^ 59
def prefixEnd_7837686 : Nat := 4983230072969 + 3 ^ 40 * 7837686 * 2
def baseEnd_7837686 : Nat := 4024500137014927251180145

theorem tailTrace_7837686 : CollatzResearch.WordTrace tailWord_7837686 prefixEnd_7837686 4024500137014927251180145 := by
  unfold tailWord_7837686
  simp only [CollatzResearch.WordTrace]
  refine ⟨17866493317713104190305807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190575928722273111363261941 17866493317713104190305807)
  ·
    refine ⟨26799739976569656285458711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17866493317713104190305807 26799739976569656285458711)
    ·
      refine ⟨40199609964854484428188067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26799739976569656285458711 40199609964854484428188067)
      ·
        refine ⟨60299414947281726642282101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40199609964854484428188067 60299414947281726642282101)
        ·
          refine ⟨5653070151307661872713947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 60299414947281726642282101 5653070151307661872713947)
          ·
            refine ⟨8479605226961492809070921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5653070151307661872713947 8479605226961492809070921)
            ·
              refine ⟨6359703920221119606803191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8479605226961492809070921 6359703920221119606803191)
              ·
                refine ⟨9539555880331679410204787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6359703920221119606803191 9539555880331679410204787)
                ·
                  refine ⟨14309333820497519115307181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9539555880331679410204787 14309333820497519115307181)
                  ·
                    refine ⟨5366000182686569668240193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14309333820497519115307181 5366000182686569668240193)
                    ·
                      refine ⟨4024500137014927251180145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5366000182686569668240193 4024500137014927251180145)
                      ·
                        rfl

theorem cell23_7837686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_7837686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837686 prefixEnd_7837686 := by exact prefixLift 7837686
  have htrace : WordTrace (prefixWord ++ tailWord_7837686) baseStart_7837686 baseEnd_7837686 := by
    simpa [prefixWord, tailWord_7837686, baseEnd_7837686] using wordTrace_append hprefix tailTrace_7837686
  have hstable : (prefixWord ++ tailWord_7837686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837686).length < 2 ^ (prefixWord ++ tailWord_7837686).sum := by decide
  have hdescent : baseEnd_7837686 < baseStart_7837686 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837716 : List Nat := [2, 4, 3, 2, 2, 1, 1, 1, 1, 4, 2]
def baseStart_7837716 : Nat := 118140960795 + 7837716 * 2 ^ 59
def prefixEnd_7837716 : Nat := 4983230072969 + 3 ^ 40 * 7837716 * 2
def baseEnd_7837716 : Nat := 4024515541434562133805007

theorem tailTrace_7837716 : CollatzResearch.WordTrace tailWord_7837716 prefixEnd_7837716 4024515541434562133805007 := by
  unfold tailWord_7837716
  simp only [CollatzResearch.WordTrace]
  refine ⟨142932493636650491084242501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190576658182200654778990001 142932493636650491084242501)
  ·
    refine ⟨26799842556871967078295469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142932493636650491084242501 26799842556871967078295469)
    ·
      refine ⟨10049940958826987654360801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26799842556871967078295469 10049940958826987654360801)
      ·
        refine ⟨7537455719120240740770601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10049940958826987654360801 7537455719120240740770601)
        ·
          refine ⟨5653091789340180555577951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7537455719120240740770601 5653091789340180555577951)
          ·
            refine ⟨8479637684010270833366927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5653091789340180555577951 8479637684010270833366927)
            ·
              refine ⟨12719456526015406250050391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8479637684010270833366927 12719456526015406250050391)
              ·
                refine ⟨19079184789023109375075587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12719456526015406250050391 19079184789023109375075587)
                ·
                  refine ⟨28618777183534664062613381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19079184789023109375075587 28618777183534664062613381)
                  ·
                    refine ⟨5366020721912749511740009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28618777183534664062613381 5366020721912749511740009)
                    ·
                      refine ⟨4024515541434562133805007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5366020721912749511740009 4024515541434562133805007)
                      ·
                        rfl

theorem cell23_7837716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 1, 1, 1, 4, 2].length) (baseStart_7837716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837716 prefixEnd_7837716 := by exact prefixLift 7837716
  have htrace : WordTrace (prefixWord ++ tailWord_7837716) baseStart_7837716 baseEnd_7837716 := by
    simpa [prefixWord, tailWord_7837716, baseEnd_7837716] using wordTrace_append hprefix tailTrace_7837716
  have hstable : (prefixWord ++ tailWord_7837716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837716).length < 2 ^ (prefixWord ++ tailWord_7837716).sum := by decide
  have hdescent : baseEnd_7837716 < baseStart_7837716 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837738 : List Nat := [3, 1, 4, 1, 2, 1, 2, 1, 1, 3, 4]
def baseStart_7837738 : Nat := 118140960795 + 7837738 * 2 ^ 59
def prefixEnd_7837738 : Nat := 4983230072969 + 3 ^ 40 * 7837738 * 2
def baseEnd_7837738 : Nat := 4024526838008961047729905

theorem tailTrace_7837738 : CollatzResearch.WordTrace tailWord_7837738 prefixEnd_7837738 4024526838008961047729905 := by
  unfold tailWord_7837738
  simp only [CollatzResearch.WordTrace]
  refine ⟨71466447419805319981446467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190577193119480853283857245 71466447419805319981446467)
  ·
    refine ⟨107199671129707979972169701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71466447419805319981446467 107199671129707979972169701)
    ·
      refine ⟨20099938336820246244781819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107199671129707979972169701 20099938336820246244781819)
      ·
        refine ⟨30149907505230369367172729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20099938336820246244781819 30149907505230369367172729)
        ·
          refine ⟨22612430628922777025379547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30149907505230369367172729 22612430628922777025379547)
          ·
            refine ⟨33918645943384165538069321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22612430628922777025379547 33918645943384165538069321)
            ·
              refine ⟨25438984457538124153551991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33918645943384165538069321 25438984457538124153551991)
              ·
                refine ⟨38158476686307186230327987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25438984457538124153551991 38158476686307186230327987)
                ·
                  refine ⟨57237715029460779345491981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38158476686307186230327987 57237715029460779345491981)
                  ·
                    refine ⟨21464143136047792254559493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 57237715029460779345491981 21464143136047792254559493)
                    ·
                      refine ⟨4024526838008961047729905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21464143136047792254559493 4024526838008961047729905)
                      ·
                        rfl

theorem cell23_7837738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_7837738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837738 prefixEnd_7837738 := by exact prefixLift 7837738
  have htrace : WordTrace (prefixWord ++ tailWord_7837738) baseStart_7837738 baseEnd_7837738 := by
    simpa [prefixWord, tailWord_7837738, baseEnd_7837738] using wordTrace_append hprefix tailTrace_7837738
  have hstable : (prefixWord ++ tailWord_7837738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837738).length < 2 ^ (prefixWord ++ tailWord_7837738).sum := by decide
  have hdescent : baseEnd_7837738 < baseStart_7837738 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837815 : List Nat := [1, 1, 3, 1, 1, 5, 2, 2, 2, 3, 2]
def baseStart_7837815 : Nat := 118140960795 + 7837815 * 2 ^ 59
def prefixEnd_7837815 : Nat := 4983230072969 + 3 ^ 40 * 7837815 * 2
def baseEnd_7837815 : Nat := 4024566376019357246467051

theorem tailTrace_7837815 : CollatzResearch.WordTrace tailWord_7837815 prefixEnd_7837815 4024566376019357246467051 := by
  unfold tailWord_7837815
  simp only [CollatzResearch.WordTrace]
  refine ⟨285868598099942322076338899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190579065399961548050892599 285868598099942322076338899)
  ·
    refine ⟨428802897149913483114508349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285868598099942322076338899 428802897149913483114508349)
    ·
      refine ⟨160801086431217556167940631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428802897149913483114508349 160801086431217556167940631)
      ·
        refine ⟨241201629646826334251910947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160801086431217556167940631 241201629646826334251910947)
        ·
          refine ⟨361802444470239501377866421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241201629646826334251910947 361802444470239501377866421)
          ·
            refine ⟨33918979169084953254174977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 361802444470239501377866421 33918979169084953254174977)
            ·
              refine ⟨25439234376813714940631233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33918979169084953254174977 25439234376813714940631233)
              ·
                refine ⟨19079425782610286205473425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25439234376813714940631233 19079425782610286205473425)
                ·
                  refine ⟨14309569336957714654105069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19079425782610286205473425 14309569336957714654105069)
                  ·
                    refine ⟨5366088501359142995289401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14309569336957714654105069 5366088501359142995289401)
                    ·
                      refine ⟨4024566376019357246467051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5366088501359142995289401 4024566376019357246467051)
                      ·
                        rfl

theorem cell23_7837815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 2, 2, 2, 3, 2].length) (baseStart_7837815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837815 prefixEnd_7837815 := by exact prefixLift 7837815
  have htrace : WordTrace (prefixWord ++ tailWord_7837815) baseStart_7837815 baseEnd_7837815 := by
    simpa [prefixWord, tailWord_7837815, baseEnd_7837815] using wordTrace_append hprefix tailTrace_7837815
  have hstable : (prefixWord ++ tailWord_7837815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837815).length < 2 ^ (prefixWord ++ tailWord_7837815).sum := by decide
  have hdescent : baseEnd_7837815 < baseStart_7837815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837828 : List Nat := [2, 3, 2, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_7837828 : Nat := 118140960795 + 7837828 * 2 ^ 59
def prefixEnd_7837828 : Nat := 4983230072969 + 3 ^ 40 * 7837828 * 2
def baseEnd_7837828 : Nat := 4024573051267865695604491

theorem tailTrace_7837828 : CollatzResearch.WordTrace tailWord_7837828 prefixEnd_7837828 4024573051267865695604491 := by
  unfold tailWord_7837828
  simp only [CollatzResearch.WordTrace]
  refine ⟨142934536124447612648281069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190579381499263483531041425 142934536124447612648281069)
  ·
    refine ⟨53600451046667854743105401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142934536124447612648281069 53600451046667854743105401)
    ·
      refine ⟨40200338285000891057329051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53600451046667854743105401 40200338285000891057329051)
      ·
        refine ⟨60300507427501336585993577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40200338285000891057329051 60300507427501336585993577)
        ·
          refine ⟨45225380570626002439495183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60300507427501336585993577 45225380570626002439495183)
          ·
            refine ⟨67838070855939003659242775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45225380570626002439495183 67838070855939003659242775)
            ·
              refine ⟨101757106283908505488864163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67838070855939003659242775 101757106283908505488864163)
              ·
                refine ⟨152635659425862758233296245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101757106283908505488864163 152635659425862758233296245)
                ·
                  refine ⟨14309593071174633584371523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152635659425862758233296245 14309593071174633584371523)
                  ·
                    refine ⟨21464389606761950376557285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14309593071174633584371523 21464389606761950376557285)
                    ·
                      refine ⟨4024573051267865695604491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21464389606761950376557285 4024573051267865695604491)
                      ·
                        rfl

theorem cell23_7837828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_7837828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837828 prefixEnd_7837828 := by exact prefixLift 7837828
  have htrace : WordTrace (prefixWord ++ tailWord_7837828) baseStart_7837828 baseEnd_7837828 := by
    simpa [prefixWord, tailWord_7837828, baseEnd_7837828] using wordTrace_append hprefix tailTrace_7837828
  have hstable : (prefixWord ++ tailWord_7837828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837828).length < 2 ^ (prefixWord ++ tailWord_7837828).sum := by decide
  have hdescent : baseEnd_7837828 < baseStart_7837828 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837871 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 6]
def baseStart_7837871 : Nat := 118140960795 + 7837871 * 2 ^ 59
def prefixEnd_7837871 : Nat := 4983230072969 + 3 ^ 40 * 7837871 * 2
def baseEnd_7837871 : Nat := 4024595130936009027366793

theorem tailTrace_7837871 : CollatzResearch.WordTrace tailWord_7837871 prefixEnd_7837871 4024595130936009027366793 := by
  unfold tailWord_7837871
  simp only [CollatzResearch.WordTrace]
  refine ⟨285870640587739443640377467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190580427058492962426918311 285870640587739443640377467)
  ·
    refine ⟨428805960881609165460566201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285870640587739443640377467 428805960881609165460566201)
    ·
      refine ⟨321604470661206874095424651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428805960881609165460566201 321604470661206874095424651)
      ·
        refine ⟨482406705991810311143136977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321604470661206874095424651 482406705991810311143136977)
        ·
          refine ⟨361805029493857733357352733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482406705991810311143136977 361805029493857733357352733)
          ·
            refine ⟨135676886060196650009007275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361805029493857733357352733 135676886060196650009007275)
            ·
              refine ⟨203515329090294975013510913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135676886060196650009007275 203515329090294975013510913)
              ·
                refine ⟨152636496817721231260133185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203515329090294975013510913 152636496817721231260133185)
                ·
                  refine ⟨114477372613290923445099889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152636496817721231260133185 114477372613290923445099889)
                  ·
                    refine ⟨85858029459968192583824917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114477372613290923445099889 85858029459968192583824917)
                    ·
                      refine ⟨4024595130936009027366793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85858029459968192583824917 4024595130936009027366793)
                      ·
                        rfl

theorem cell23_7837871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_7837871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837871 prefixEnd_7837871 := by exact prefixLift 7837871
  have htrace : WordTrace (prefixWord ++ tailWord_7837871) baseStart_7837871 baseEnd_7837871 := by
    simpa [prefixWord, tailWord_7837871, baseEnd_7837871] using wordTrace_append hprefix tailTrace_7837871
  have hstable : (prefixWord ++ tailWord_7837871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837871).length < 2 ^ (prefixWord ++ tailWord_7837871).sum := by decide
  have hdescent : baseEnd_7837871 < baseStart_7837871 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837879 : List Nat := [1, 1, 3, 1, 4, 2, 2, 4, 1, 2, 2]
def baseStart_7837879 : Nat := 118140960795 + 7837879 * 2 ^ 59
def prefixEnd_7837879 : Nat := 4983230072969 + 3 ^ 40 * 7837879 * 2
def baseEnd_7837879 : Nat := 4024599238781244996066757

theorem tailTrace_7837879 : CollatzResearch.WordTrace tailWord_7837879 prefixEnd_7837879 4024599238781244996066757 := by
  unfold tailWord_7837879
  simp only [CollatzResearch.WordTrace]
  refine ⟨285870932371710461006668691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190580621581140307337779127 285870932371710461006668691)
  ·
    refine ⟨428806398557565691510003037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285870932371710461006668691 428806398557565691510003037)
    ·
      refine ⟨160802399459087134316251139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428806398557565691510003037 160802399459087134316251139)
      ·
        refine ⟨241203599188630701474376709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160802399459087134316251139 241203599188630701474376709)
        ·
          refine ⟨45225674847868256526445633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241203599188630701474376709 45225674847868256526445633)
          ·
            refine ⟨33919256135901192394834225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45225674847868256526445633 33919256135901192394834225)
            ·
              refine ⟨25439442101925894296125669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33919256135901192394834225 25439442101925894296125669)
              ·
                refine ⟨4769895394111105180523563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25439442101925894296125669 4769895394111105180523563)
                ·
                  refine ⟨7154843091166657770785345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4769895394111105180523563 7154843091166657770785345)
                  ·
                    refine ⟨5366132318374993328089009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7154843091166657770785345 5366132318374993328089009)
                    ·
                      refine ⟨4024599238781244996066757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5366132318374993328089009 4024599238781244996066757)
                      ·
                        rfl

theorem cell23_7837879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 4, 1, 2, 2].length) (baseStart_7837879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837879 prefixEnd_7837879 := by exact prefixLift 7837879
  have htrace : WordTrace (prefixWord ++ tailWord_7837879) baseStart_7837879 baseEnd_7837879 := by
    simpa [prefixWord, tailWord_7837879, baseEnd_7837879] using wordTrace_append hprefix tailTrace_7837879
  have hstable : (prefixWord ++ tailWord_7837879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837879).length < 2 ^ (prefixWord ++ tailWord_7837879).sum := by decide
  have hdescent : baseEnd_7837879 < baseStart_7837879 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837889 : List Nat := [1, 2, 6, 1, 3, 1, 1, 1, 1, 6]
def baseStart_7837889 : Nat := 118140960795 + 7837889 * 2 ^ 59
def prefixEnd_7837889 : Nat := 4983230072969 + 3 ^ 40 * 7837889 * 2
def baseEnd_7837889 : Nat := 1341534791195929985647237

theorem tailTrace_7837889 : CollatzResearch.WordTrace tailWord_7837889 prefixEnd_7837889 1341534791195929985647237 := by
  unfold tailWord_7837889
  simp only [CollatzResearch.WordTrace]
  refine ⟨285871297101674232714532721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190580864734449488476355147 285871297101674232714532721)
  ·
    refine ⟨214403472826255674535899541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285871297101674232714532721 214403472826255674535899541)
    ·
      refine ⟨10050162788730734743870291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 214403472826255674535899541 10050162788730734743870291)
      ·
        refine ⟨15075244183096102115805437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10050162788730734743870291 15075244183096102115805437)
        ·
          refine ⟨5653216568661038293427039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15075244183096102115805437 5653216568661038293427039)
          ·
            refine ⟨8479824852991557440140559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5653216568661038293427039 8479824852991557440140559)
            ·
              refine ⟨12719737279487336160210839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8479824852991557440140559 12719737279487336160210839)
              ·
                refine ⟨19079605919231004240316259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12719737279487336160210839 19079605919231004240316259)
                ·
                  refine ⟨28619408878846506360474389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19079605919231004240316259 28619408878846506360474389)
                  ·
                    refine ⟨1341534791195929985647237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28619408878846506360474389 1341534791195929985647237)
                    ·
                      rfl

theorem cell23_7837889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_7837889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837889 prefixEnd_7837889 := by exact prefixLift 7837889
  have htrace : WordTrace (prefixWord ++ tailWord_7837889) baseStart_7837889 baseEnd_7837889 := by
    simpa [prefixWord, tailWord_7837889, baseEnd_7837889] using wordTrace_append hprefix tailTrace_7837889
  have hstable : (prefixWord ++ tailWord_7837889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837889).length < 2 ^ (prefixWord ++ tailWord_7837889).sum := by decide
  have hdescent : baseEnd_7837889 < baseStart_7837889 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837892 : List Nat := [2, 3, 3, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_7837892 : Nat := 118140960795 + 7837892 * 2 ^ 59
def prefixEnd_7837892 : Nat := 4983230072969 + 3 ^ 40 * 7837892 * 2
def baseEnd_7837892 : Nat := 4024605914029753445204197

theorem tailTrace_7837892 : CollatzResearch.WordTrace tailWord_7837892 prefixEnd_7837892 4024605914029753445204197 := by
  unfold tailWord_7837892
  simp only [CollatzResearch.WordTrace]
  refine ⟨142935703260331682113445965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190580937680442242817927953 142935703260331682113445965)
  ·
    refine ⟨53600888722624380792542237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142935703260331682113445965 53600888722624380792542237)
    ·
      refine ⟨20100333270984142797203339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53600888722624380792542237 20100333270984142797203339)
      ·
        refine ⟨30150499906476214195805009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20100333270984142797203339 30150499906476214195805009)
        ·
          refine ⟨22612874929857160646853757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30150499906476214195805009 22612874929857160646853757)
          ·
            refine ⟨8479828098696435242570159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22612874929857160646853757 8479828098696435242570159)
            ·
              refine ⟨12719742148044652863855239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8479828098696435242570159 12719742148044652863855239)
              ·
                refine ⟨19079613222066979295782859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12719742148044652863855239 19079613222066979295782859)
                ·
                  refine ⟨28619419833100468943674289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19079613222066979295782859 28619419833100468943674289)
                  ·
                    refine ⟨21464564874825351707755717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28619419833100468943674289 21464564874825351707755717)
                    ·
                      refine ⟨4024605914029753445204197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21464564874825351707755717 4024605914029753445204197)
                      ·
                        rfl

theorem cell23_7837892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_7837892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837892 prefixEnd_7837892 := by exact prefixLift 7837892
  have htrace : WordTrace (prefixWord ++ tailWord_7837892) baseStart_7837892 baseEnd_7837892 := by
    simpa [prefixWord, tailWord_7837892, baseEnd_7837892] using wordTrace_append hprefix tailTrace_7837892
  have hstable : (prefixWord ++ tailWord_7837892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837892).length < 2 ^ (prefixWord ++ tailWord_7837892).sum := by decide
  have hdescent : baseEnd_7837892 < baseStart_7837892 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837905 : List Nat := [1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2]
def baseStart_7837905 : Nat := 118140960795 + 7837905 * 2 ^ 59
def prefixEnd_7837905 : Nat := 4983230072969 + 3 ^ 40 * 7837905 * 2
def baseEnd_7837905 : Nat := 4024612589278261894341637

theorem tailTrace_7837905 : CollatzResearch.WordTrace tailWord_7837905 prefixEnd_7837905 4024612589278261894341637 := by
  unfold tailWord_7837905
  simp only [CollatzResearch.WordTrace]
  refine ⟨285871880669616267447115169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190581253779744178298076779 285871880669616267447115169)
  ·
    refine ⟨214403910502212200585336377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285871880669616267447115169 214403910502212200585336377)
    ·
      refine ⟨160802932876659150439002283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214403910502212200585336377 160802932876659150439002283)
      ·
        refine ⟨241204399314988725658503425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160802932876659150439002283 241204399314988725658503425)
        ·
          refine ⟨180903299486241544243877569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241204399314988725658503425 180903299486241544243877569)
          ·
            refine ⟨135677474614681158182908177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180903299486241544243877569 135677474614681158182908177)
            ·
              refine ⟨101758105961010868637181133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135677474614681158182908177 101758105961010868637181133)
              ·
                refine ⟨38159289735379075738942925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101758105961010868637181133 38159289735379075738942925)
                ·
                  refine ⟨14309733650767153402103597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38159289735379075738942925 14309733650767153402103597)
                  ·
                    refine ⟨5366150119037682525788849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14309733650767153402103597 5366150119037682525788849)
                    ·
                      refine ⟨4024612589278261894341637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5366150119037682525788849 4024612589278261894341637)
                      ·
                        rfl

theorem cell23_7837905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 3, 3, 3, 2].length) (baseStart_7837905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837905 prefixEnd_7837905 := by exact prefixLift 7837905
  have htrace : WordTrace (prefixWord ++ tailWord_7837905) baseStart_7837905 baseEnd_7837905 := by
    simpa [prefixWord, tailWord_7837905, baseEnd_7837905] using wordTrace_append hprefix tailTrace_7837905
  have hstable : (prefixWord ++ tailWord_7837905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837905).length < 2 ^ (prefixWord ++ tailWord_7837905).sum := by decide
  have hdescent : baseEnd_7837905 < baseStart_7837905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837956 : List Nat := [2, 3, 2, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_7837956 : Nat := 118140960795 + 7837956 * 2 ^ 59
def prefixEnd_7837956 : Nat := 4983230072969 + 3 ^ 40 * 7837956 * 2
def baseEnd_7837956 : Nat := 4024638776791641194803903

theorem tailTrace_7837956 : CollatzResearch.WordTrace tailWord_7837956 prefixEnd_7837956 4024638776791641194803903 := by
  unfold tailWord_7837956
  simp only [CollatzResearch.WordTrace]
  refine ⟨142936870396215751578610861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190582493861621002104814481 142936870396215751578610861)
  ·
    refine ⟨53601326398580906841979073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142936870396215751578610861 53601326398580906841979073)
    ·
      refine ⟨40200994798935680131484305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53601326398580906841979073 40200994798935680131484305)
      ·
        refine ⟨30150746099201760098613229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40200994798935680131484305 30150746099201760098613229)
        ·
          refine ⟨11306529787200660036979961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30150746099201760098613229 11306529787200660036979961)
          ·
            refine ⟨8479897340400495027734971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11306529787200660036979961 8479897340400495027734971)
            ·
              refine ⟨12719846010600742541602457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8479897340400495027734971 12719846010600742541602457)
              ·
                refine ⟨9539884507950556906201843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12719846010600742541602457 9539884507950556906201843)
                ·
                  refine ⟨14309826761925835359302765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9539884507950556906201843 14309826761925835359302765)
                  ·
                    refine ⟨5366185035722188259738537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14309826761925835359302765 5366185035722188259738537)
                    ·
                      refine ⟨4024638776791641194803903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5366185035722188259738537 4024638776791641194803903)
                      ·
                        rfl

theorem cell23_7837956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_7837956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837956 prefixEnd_7837956 := by exact prefixLift 7837956
  have htrace : WordTrace (prefixWord ++ tailWord_7837956) baseStart_7837956 baseEnd_7837956 := by
    simpa [prefixWord, tailWord_7837956, baseEnd_7837956] using wordTrace_append hprefix tailTrace_7837956
  have hstable : (prefixWord ++ tailWord_7837956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837956).length < 2 ^ (prefixWord ++ tailWord_7837956).sum := by decide
  have hdescent : baseEnd_7837956 < baseStart_7837956 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7837986 : List Nat := [3, 3, 1, 1, 3, 2, 2, 2, 2, 2, 2]
def baseStart_7837986 : Nat := 118140960795 + 7837986 * 2 ^ 59
def prefixEnd_7837986 : Nat := 4983230072969 + 3 ^ 40 * 7837986 * 2
def baseEnd_7837986 : Nat := 4024654181211276077428765

theorem tailTrace_7837986 : CollatzResearch.WordTrace tailWord_7837986 prefixEnd_7837986 4024654181211276077428765 := by
  unfold tailWord_7837986
  simp only [CollatzResearch.WordTrace]
  refine ⟨71468708745580704570203453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190583223321548545520542541 71468708745580704570203453)
  ·
    refine ⟨26800765779592764213826295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71468708745580704570203453 26800765779592764213826295)
    ·
      refine ⟨40201148669389146320739443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26800765779592764213826295 40201148669389146320739443)
      ·
        refine ⟨60301723004083719481109165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40201148669389146320739443 60301723004083719481109165)
        ·
          refine ⟨22613146126531394805415937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60301723004083719481109165 22613146126531394805415937)
          ·
            refine ⟨16959859594898546104061953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22613146126531394805415937 16959859594898546104061953)
            ·
              refine ⟨12719894696173909578046465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16959859594898546104061953 12719894696173909578046465)
              ·
                refine ⟨9539921022130432183534849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12719894696173909578046465 9539921022130432183534849)
                ·
                  refine ⟨7154940766597824137651137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9539921022130432183534849 7154940766597824137651137)
                  ·
                    refine ⟨5366205574948368103238353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7154940766597824137651137 5366205574948368103238353)
                    ·
                      refine ⟨4024654181211276077428765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5366205574948368103238353 4024654181211276077428765)
                      ·
                        rfl

theorem cell23_7837986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_7837986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7837986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7837986 prefixEnd_7837986 := by exact prefixLift 7837986
  have htrace : WordTrace (prefixWord ++ tailWord_7837986) baseStart_7837986 baseEnd_7837986 := by
    simpa [prefixWord, tailWord_7837986, baseEnd_7837986] using wordTrace_append hprefix tailTrace_7837986
  have hstable : (prefixWord ++ tailWord_7837986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7837986).length < 2 ^ (prefixWord ++ tailWord_7837986).sum := by decide
  have hdescent : baseEnd_7837986 < baseStart_7837986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7837986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838002 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3]
def baseStart_7838002 : Nat := 118140960795 + 7838002 * 2 ^ 59
def prefixEnd_7838002 : Nat := 4983230072969 + 3 ^ 40 * 7838002 * 2
def baseEnd_7838002 : Nat := 4024662396901748014828691

theorem tailTrace_7838002 : CollatzResearch.WordTrace tailWord_7838002 prefixEnd_7838002 4024662396901748014828691 := by
  unfold tailWord_7838002
  simp only [CollatzResearch.WordTrace]
  refine ⟨71468854637566213253349065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190583612366843235342264173 71468854637566213253349065)
  ·
    refine ⟨53601640978174659940011799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71468854637566213253349065 53601640978174659940011799)
    ·
      refine ⟨80402461467261989910017699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53601640978174659940011799 80402461467261989910017699)
      ·
        refine ⟨120603692200892984865026549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80402461467261989910017699 120603692200892984865026549)
        ·
          refine ⟨11306596143833717331096239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120603692200892984865026549 11306596143833717331096239)
          ·
            refine ⟨16959894215750575996644359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11306596143833717331096239 16959894215750575996644359)
            ·
              refine ⟨25439841323625863994966539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16959894215750575996644359 25439841323625863994966539)
              ·
                refine ⟨38159761985438795992449809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25439841323625863994966539 38159761985438795992449809)
                ·
                  refine ⟨28619821489079096994337357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38159761985438795992449809 28619821489079096994337357)
                  ·
                    refine ⟨10732433058404661372876509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28619821489079096994337357 10732433058404661372876509)
                    ·
                      refine ⟨4024662396901748014828691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10732433058404661372876509 4024662396901748014828691)
                      ·
                        rfl

theorem cell23_7838002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 2, 3, 3].length) (baseStart_7838002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838002 prefixEnd_7838002 := by exact prefixLift 7838002
  have htrace : WordTrace (prefixWord ++ tailWord_7838002) baseStart_7838002 baseEnd_7838002 := by
    simpa [prefixWord, tailWord_7838002, baseEnd_7838002] using wordTrace_append hprefix tailTrace_7838002
  have hstable : (prefixWord ++ tailWord_7838002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838002).length < 2 ^ (prefixWord ++ tailWord_7838002).sum := by decide
  have hdescent : baseEnd_7838002 < baseStart_7838002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838025 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 3, 6, 2]
def baseStart_7838025 : Nat := 118140960795 + 7838025 * 2 ^ 59
def prefixEnd_7838025 : Nat := 4983230072969 + 3 ^ 40 * 7838025 * 2
def baseEnd_7838025 : Nat := 4024674206956801424841085

theorem tailTrace_7838025 : CollatzResearch.WordTrace tailWord_7838025 prefixEnd_7838025 4024674206956801424841085 := by
  unfold tailWord_7838025
  simp only [CollatzResearch.WordTrace]
  refine ⟨285876257429181527941483529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190584171619454351960989019 285876257429181527941483529)
  ·
    refine ⟨214407193071886145956112647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285876257429181527941483529 214407193071886145956112647)
    ·
      refine ⟨321610789607829218934168971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214407193071886145956112647 321610789607829218934168971)
      ·
        refine ⟨482416184411743828401253457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321610789607829218934168971 482416184411743828401253457)
        ·
          refine ⟨361812138308807871300940093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482416184411743828401253457 361812138308807871300940093)
          ·
            refine ⟨135679551865802951737852535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361812138308807871300940093 135679551865802951737852535)
            ·
              refine ⟨203519327798704427606778803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135679551865802951737852535 203519327798704427606778803)
              ·
                refine ⟨305278991698056641410168205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203519327798704427606778803 305278991698056641410168205)
                ·
                  refine ⟨114479621886771240528813077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305278991698056641410168205 114479621886771240528813077)
                  ·
                    refine ⟨5366232275942401899788113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 114479621886771240528813077 5366232275942401899788113)
                    ·
                      refine ⟨4024674206956801424841085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5366232275942401899788113 4024674206956801424841085)
                      ·
                        rfl

theorem cell23_7838025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 3, 6, 2].length) (baseStart_7838025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838025 prefixEnd_7838025 := by exact prefixLift 7838025
  have htrace : WordTrace (prefixWord ++ tailWord_7838025) baseStart_7838025 baseEnd_7838025 := by
    simpa [prefixWord, tailWord_7838025, baseEnd_7838025] using wordTrace_append hprefix tailTrace_7838025
  have hstable : (prefixWord ++ tailWord_7838025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838025).length < 2 ^ (prefixWord ++ tailWord_7838025).sum := by decide
  have hdescent : baseEnd_7838025 < baseStart_7838025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838052 : List Nat := [2, 3, 1, 1, 3, 1, 4, 1, 3, 4]
def baseStart_7838052 : Nat := 118140960795 + 7838052 * 2 ^ 59
def prefixEnd_7838052 : Nat := 4983230072969 + 3 ^ 40 * 7838052 * 2
def baseEnd_7838052 : Nat := 1341562690311490939734487

theorem tailTrace_7838052 : CollatzResearch.WordTrace tailWord_7838052 prefixEnd_7838052 1341562690311490939734487 := by
  unfold tailWord_7838052
  simp only [CollatzResearch.WordTrace]
  refine ⟨142938621100041855776358205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190584828133389141035144273 142938621100041855776358205)
  ·
    refine ⟨53601982912515695916134327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142938621100041855776358205 53601982912515695916134327)
    ·
      refine ⟨80402974368773543874201491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53601982912515695916134327 80402974368773543874201491)
      ·
        refine ⟨120604461553160315811302237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80402974368773543874201491 120604461553160315811302237)
        ·
          refine ⟨45226673082435118429238339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120604461553160315811302237 45226673082435118429238339)
          ·
            refine ⟨67840009623652677643857509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45226673082435118429238339 67840009623652677643857509)
            ·
              refine ⟨12720001804434877058223283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67840009623652677643857509 12720001804434877058223283)
              ·
                refine ⟨19080002706652315587334925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12720001804434877058223283 19080002706652315587334925)
                ·
                  refine ⟨7155001014994618345250597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19080002706652315587334925 7155001014994618345250597)
                  ·
                    refine ⟨1341562690311490939734487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7155001014994618345250597 1341562690311490939734487)
                    ·
                      rfl

theorem cell23_7838052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_7838052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838052 prefixEnd_7838052 := by exact prefixLift 7838052
  have htrace : WordTrace (prefixWord ++ tailWord_7838052) baseStart_7838052 baseEnd_7838052 := by
    simpa [prefixWord, tailWord_7838052, baseEnd_7838052] using wordTrace_append hprefix tailTrace_7838052
  have hstable : (prefixWord ++ tailWord_7838052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838052).length < 2 ^ (prefixWord ++ tailWord_7838052).sum := by decide
  have hdescent : baseEnd_7838052 < baseStart_7838052 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838129 : List Nat := [1, 2, 2, 4, 1, 4, 1, 2, 1, 5]
def baseStart_7838129 : Nat := 118140960795 + 7838129 * 2 ^ 59
def prefixEnd_7838129 : Nat := 4983230072969 + 3 ^ 40 * 7838129 * 2
def baseEnd_7838129 : Nat := 1341575869648289672646869

theorem tailTrace_7838129 : CollatzResearch.WordTrace tailWord_7838129 prefixEnd_7838129 1341575869648289672646869 := by
  unfold tailWord_7838129
  simp only [CollatzResearch.WordTrace]
  refine ⟨285880050620804753703269441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190586700413869835802179627 285880050620804753703269441)
  ·
    refine ⟨214410037965603565277452081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285880050620804753703269441 214410037965603565277452081)
    ·
      refine ⟨160807528474202673958089061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214410037965603565277452081 160807528474202673958089061)
      ·
        refine ⟨30151411588913001367141699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160807528474202673958089061 30151411588913001367141699)
        ·
          refine ⟨45227117383369502050712549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30151411588913001367141699 45227117383369502050712549)
          ·
            refine ⟨8480084509381781634508603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 45227117383369502050712549 8480084509381781634508603)
            ·
              refine ⟨12720126764072672451762905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8480084509381781634508603 12720126764072672451762905)
              ·
                refine ⟨9540095073054504338822179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12720126764072672451762905 9540095073054504338822179)
                ·
                  refine ⟨14310142609581756508233269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9540095073054504338822179 14310142609581756508233269)
                  ·
                    refine ⟨1341575869648289672646869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14310142609581756508233269 1341575869648289672646869)
                    ·
                      rfl

theorem cell23_7838129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 1, 5].length) (baseStart_7838129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838129 prefixEnd_7838129 := by exact prefixLift 7838129
  have htrace : WordTrace (prefixWord ++ tailWord_7838129) baseStart_7838129 baseEnd_7838129 := by
    simpa [prefixWord, tailWord_7838129, baseEnd_7838129] using wordTrace_append hprefix tailTrace_7838129
  have hstable : (prefixWord ++ tailWord_7838129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838129).length < 2 ^ (prefixWord ++ tailWord_7838129).sum := by decide
  have hdescent : baseEnd_7838129 < baseStart_7838129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838142 : List Nat := [4, 2, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_7838142 : Nat := 118140960795 + 7838142 * 2 ^ 59
def prefixEnd_7838142 : Nat := 4983230072969 + 3 ^ 40 * 7838142 * 2
def baseEnd_7838142 : Nat := 1341578094731125822359349

theorem tailTrace_7838142 : CollatzResearch.WordTrace tailWord_7838142 prefixEnd_7838142 1341578094731125822359349 := by
  unfold tailWord_7838142
  simp only [CollatzResearch.WordTrace]
  refine ⟨35735065596219707115436585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190587016513171771282328453 35735065596219707115436585)
  ·
    refine ⟨26801299197164780336577439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35735065596219707115436585 26801299197164780336577439)
    ·
      refine ⟨40201948795747170504866159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26801299197164780336577439 40201948795747170504866159)
      ·
        refine ⟨60302923193620755757299239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40201948795747170504866159 60302923193620755757299239)
        ·
          refine ⟨90454384790431133635948859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60302923193620755757299239 90454384790431133635948859)
          ·
            refine ⟨135681577185646700453923289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90454384790431133635948859 135681577185646700453923289)
            ·
              refine ⟨101761182889235025340442467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135681577185646700453923289 101761182889235025340442467)
              ·
                refine ⟨152641774333852538010663701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101761182889235025340442467 152641774333852538010663701)
                ·
                  refine ⟨7155083171899337719249861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 152641774333852538010663701 7155083171899337719249861)
                  ·
                    refine ⟨1341578094731125822359349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7155083171899337719249861 1341578094731125822359349)
                    ·
                      rfl

theorem cell23_7838142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_7838142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838142 prefixEnd_7838142 := by exact prefixLift 7838142
  have htrace : WordTrace (prefixWord ++ tailWord_7838142) baseStart_7838142 baseEnd_7838142 := by
    simpa [prefixWord, tailWord_7838142, baseEnd_7838142] using wordTrace_append hprefix tailTrace_7838142
  have hstable : (prefixWord ++ tailWord_7838142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838142).length < 2 ^ (prefixWord ++ tailWord_7838142).sum := by decide
  have hdescent : baseEnd_7838142 < baseStart_7838142 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838152 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 1, 1, 5]
def baseStart_7838152 : Nat := 118140960795 + 7838152 * 2 ^ 59
def prefixEnd_7838152 : Nat := 4983230072969 + 3 ^ 40 * 7838152 * 2
def baseEnd_7838152 : Nat := 4024739418999922427953001

theorem tailTrace_7838152 : CollatzResearch.WordTrace tailWord_7838152 prefixEnd_7838152 4024739418999922427953001 := by
  unfold tailWord_7838152
  simp only [CollatzResearch.WordTrace]
  refine ⟨142940444749860714315678355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190587259666480952420904473 142940444749860714315678355)
  ·
    refine ⟨214410667124791071473517533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142940444749860714315678355 214410667124791071473517533)
    ·
      refine ⟨80404000171796651802569075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214410667124791071473517533 80404000171796651802569075)
      ·
        refine ⟨120606000257694977703853613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80404000171796651802569075 120606000257694977703853613)
        ·
          refine ⟨45227250096635616638945105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120606000257694977703853613 45227250096635616638945105)
          ·
            refine ⟨33920437572476712479208829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45227250096635616638945105 33920437572476712479208829)
            ·
              refine ⟨12720164089678767179703311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33920437572476712479208829 12720164089678767179703311)
              ·
                refine ⟨19080246134518150769554967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12720164089678767179703311 19080246134518150769554967)
                ·
                  refine ⟨28620369201777226154332451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19080246134518150769554967 28620369201777226154332451)
                  ·
                    refine ⟨42930553802665839231498677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28620369201777226154332451 42930553802665839231498677)
                    ·
                      refine ⟨4024739418999922427953001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42930553802665839231498677 4024739418999922427953001)
                      ·
                        rfl

theorem cell23_7838152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_7838152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838152 prefixEnd_7838152 := by exact prefixLift 7838152
  have htrace : WordTrace (prefixWord ++ tailWord_7838152) baseStart_7838152 baseEnd_7838152 := by
    simpa [prefixWord, tailWord_7838152, baseEnd_7838152] using wordTrace_append hprefix tailTrace_7838152
  have hstable : (prefixWord ++ tailWord_7838152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838152).length < 2 ^ (prefixWord ++ tailWord_7838152).sum := by decide
  have hdescent : baseEnd_7838152 < baseStart_7838152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838179 : List Nat := [1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 4]
def baseStart_7838179 : Nat := 118140960795 + 7838179 * 2 ^ 59
def prefixEnd_7838179 : Nat := 4983230072969 + 3 ^ 40 * 7838179 * 2
def baseEnd_7838179 : Nat := 4024753282977593822315377

theorem tailTrace_7838179 : CollatzResearch.WordTrace tailWord_7838179 prefixEnd_7838179 4024753282977593822315377 := by
  unfold tailWord_7838179
  simp only [CollatzResearch.WordTrace]
  refine ⟨285881874270623612242589591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190587916180415741495059727 285881874270623612242589591)
  ·
    refine ⟨428822811405935418363884387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285881874270623612242589591 428822811405935418363884387)
    ·
      refine ⟨643234217108903127545826581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428822811405935418363884387 643234217108903127545826581)
      ·
        refine ⟨30151603926979834103710621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 643234217108903127545826581 30151603926979834103710621)
        ·
          refine ⟨11306851472617437788891483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30151603926979834103710621 11306851472617437788891483)
          ·
            refine ⟨16960277208926156683337225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11306851472617437788891483 16960277208926156683337225)
            ·
              refine ⟨12720207906694617512502919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16960277208926156683337225 12720207906694617512502919)
              ·
                refine ⟨19080311860041926268754379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12720207906694617512502919 19080311860041926268754379)
                ·
                  refine ⟨28620467790062889403131569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19080311860041926268754379 28620467790062889403131569)
                  ·
                    refine ⟨21465350842547167052348677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28620467790062889403131569 21465350842547167052348677)
                    ·
                      refine ⟨4024753282977593822315377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21465350842547167052348677 4024753282977593822315377)
                      ·
                        rfl

theorem cell23_7838179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_7838179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838179 prefixEnd_7838179 := by exact prefixLift 7838179
  have htrace : WordTrace (prefixWord ++ tailWord_7838179) baseStart_7838179 baseEnd_7838179 := by
    simpa [prefixWord, tailWord_7838179, baseEnd_7838179] using wordTrace_append hprefix tailTrace_7838179
  have hstable : (prefixWord ++ tailWord_7838179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838179).length < 2 ^ (prefixWord ++ tailWord_7838179).sum := by decide
  have hdescent : baseEnd_7838179 < baseStart_7838179 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838189 : List Nat := [1, 5, 1, 3, 1, 2, 3, 7]
def baseStart_7838189 : Nat := 118140960795 + 7838189 * 2 ^ 59
def prefixEnd_7838189 : Nat := 4983230072969 + 3 ^ 40 * 7838189 * 2
def baseEnd_7838189 : Nat := 149065126584597732710753

theorem tailTrace_7838189 : CollatzResearch.WordTrace tailWord_7838189 prefixEnd_7838189 149065126584597732710753 := by
  unfold tailWord_7838189
  simp only [CollatzResearch.WordTrace]
  refine ⟨285882239000587383950453621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190588159333724922633635747 285882239000587383950453621)
  ·
    refine ⟨26801459906305067245355027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285882239000587383950453621 26801459906305067245355027)
    ·
      refine ⟨40202189859457600868032541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26801459906305067245355027 40202189859457600868032541)
      ·
        refine ⟨15075821197296600325512203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40202189859457600868032541 15075821197296600325512203)
        ·
          refine ⟨22613731795944900488268305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15075821197296600325512203 22613731795944900488268305)
          ·
            refine ⟨16960298846958675366201229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22613731795944900488268305 16960298846958675366201229)
            ·
              refine ⟨6360112067609503262325461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16960298846958675366201229 6360112067609503262325461)
              ·
                refine ⟨149065126584597732710753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6360112067609503262325461 149065126584597732710753)
                ·
                  rfl

theorem cell23_7838189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 7].length) (baseStart_7838189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838189 prefixEnd_7838189 := by exact prefixLift 7838189
  have htrace : WordTrace (prefixWord ++ tailWord_7838189) baseStart_7838189 baseEnd_7838189 := by
    simpa [prefixWord, tailWord_7838189, baseEnd_7838189] using wordTrace_append hprefix tailTrace_7838189
  have hstable : (prefixWord ++ tailWord_7838189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838189).length < 2 ^ (prefixWord ++ tailWord_7838189).sum := by decide
  have hdescent : baseEnd_7838189 < baseStart_7838189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838195 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 5]
def baseStart_7838195 : Nat := 118140960795 + 7838195 * 2 ^ 59
def prefixEnd_7838195 : Nat := 4983230072969 + 3 ^ 40 * 7838195 * 2
def baseEnd_7838195 : Nat := 4024761498668065759715303

theorem tailTrace_7838195 : CollatzResearch.WordTrace tailWord_7838195 prefixEnd_7838195 4024761498668065759715303 := by
  unfold tailWord_7838195
  simp only [CollatzResearch.WordTrace]
  refine ⟨285882457838565646975172039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190588305225710431316781359 285882457838565646975172039)
  ·
    refine ⟨428823686757848470462758059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285882457838565646975172039 428823686757848470462758059)
    ·
      refine ⟨643235530136772705694137089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428823686757848470462758059 643235530136772705694137089)
      ·
        refine ⟨482426647602579529270602817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643235530136772705694137089 482426647602579529270602817)
        ·
          refine ⟨361819985701934646952952113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482426647602579529270602817 361819985701934646952952113)
          ·
            refine ⟨271364989276450985214714085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361819985701934646952952113 271364989276450985214714085)
            ·
              refine ⟨50880935489334559727758891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271364989276450985214714085 50880935489334559727758891)
              ·
                refine ⟨76321403234001839591638337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50880935489334559727758891 76321403234001839591638337)
                ·
                  refine ⟨57241052425501379693728753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76321403234001839591638337 57241052425501379693728753)
                  ·
                    refine ⟨42930789319126034770296565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57241052425501379693728753 42930789319126034770296565)
                    ·
                      refine ⟨4024761498668065759715303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42930789319126034770296565 4024761498668065759715303)
                      ·
                        rfl

theorem cell23_7838195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 2, 5].length) (baseStart_7838195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838195 prefixEnd_7838195 := by exact prefixLift 7838195
  have htrace : WordTrace (prefixWord ++ tailWord_7838195) baseStart_7838195 baseEnd_7838195 := by
    simpa [prefixWord, tailWord_7838195, baseEnd_7838195] using wordTrace_append hprefix tailTrace_7838195
  have hstable : (prefixWord ++ tailWord_7838195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838195).length < 2 ^ (prefixWord ++ tailWord_7838195).sum := by decide
  have hdescent : baseEnd_7838195 < baseStart_7838195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838210 : List Nat := [3, 4, 1, 2, 3, 1, 1, 2, 2, 4]
def baseStart_7838210 : Nat := 118140960795 + 7838210 * 2 ^ 59
def prefixEnd_7838210 : Nat := 4983230072969 + 3 ^ 40 * 7838210 * 2
def baseEnd_7838210 : Nat := 1341589733625961067009245

theorem tailTrace_7838210 : CollatzResearch.WordTrace tailWord_7838210 prefixEnd_7838210 1341589733625961067009245 := by
  unfold tailWord_7838210
  simp only [CollatzResearch.WordTrace]
  refine ⟨71470751233377826134242021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190588669955674203024645389 71470751233377826134242021)
  ·
    refine ⟨13400765856258342400170379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71470751233377826134242021 13400765856258342400170379)
    ·
      refine ⟨20101148784387513600255569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13400765856258342400170379 20101148784387513600255569)
      ·
        refine ⟨15075861588290635200191677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20101148784387513600255569 15075861588290635200191677)
        ·
          refine ⟨5653448095608988200071879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15075861588290635200191677 5653448095608988200071879)
          ·
            refine ⟨8480172143413482300107819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5653448095608988200071879 8480172143413482300107819)
            ·
              refine ⟨12720258215120223450161729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8480172143413482300107819 12720258215120223450161729)
              ·
                refine ⟨9540193661340167587621297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12720258215120223450161729 9540193661340167587621297)
                ·
                  refine ⟨7155145246005125690715973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9540193661340167587621297 7155145246005125690715973)
                  ·
                    refine ⟨1341589733625961067009245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7155145246005125690715973 1341589733625961067009245)
                    ·
                      rfl

theorem cell23_7838210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_7838210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838210 prefixEnd_7838210 := by exact prefixLift 7838210
  have htrace : WordTrace (prefixWord ++ tailWord_7838210) baseStart_7838210 baseEnd_7838210 := by
    simpa [prefixWord, tailWord_7838210, baseEnd_7838210] using wordTrace_append hprefix tailTrace_7838210
  have hstable : (prefixWord ++ tailWord_7838210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838210).length < 2 ^ (prefixWord ++ tailWord_7838210).sum := by decide
  have hdescent : baseEnd_7838210 < baseStart_7838210 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838225 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 5]
def baseStart_7838225 : Nat := 118140960795 + 7838225 * 2 ^ 59
def prefixEnd_7838225 : Nat := 4983230072969 + 3 ^ 40 * 7838225 * 2
def baseEnd_7838225 : Nat := 4024776903087700642340165

theorem tailTrace_7838225 : CollatzResearch.WordTrace tailWord_7838225 prefixEnd_7838225 4024776903087700642340165 := by
  unfold tailWord_7838225
  simp only [CollatzResearch.WordTrace]
  refine ⟨285883552028456962098764129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190589034685637974732509419 285883552028456962098764129)
  ·
    refine ⟨214412664021342721574073097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285883552028456962098764129 214412664021342721574073097)
    ·
      refine ⟨160809498016007041180554823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214412664021342721574073097 160809498016007041180554823)
      ·
        refine ⟨241214247024010561770832235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160809498016007041180554823 241214247024010561770832235)
        ·
          refine ⟨361821370536015842656248353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241214247024010561770832235 361821370536015842656248353)
          ·
            refine ⟨271366027902011881992186265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361821370536015842656248353 271366027902011881992186265)
            ·
              refine ⟨203524520926508911494139699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271366027902011881992186265 203524520926508911494139699)
              ·
                refine ⟨305286781389763367241209549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203524520926508911494139699 305286781389763367241209549)
                ·
                  refine ⟨114482543021161262715453581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 305286781389763367241209549 114482543021161262715453581)
                  ·
                    refine ⟨42930953632935473518295093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 114482543021161262715453581 42930953632935473518295093)
                    ·
                      refine ⟨4024776903087700642340165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42930953632935473518295093 4024776903087700642340165)
                      ·
                        rfl

theorem cell23_7838225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_7838225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838225 prefixEnd_7838225 := by exact prefixLift 7838225
  have htrace : WordTrace (prefixWord ++ tailWord_7838225) baseStart_7838225 baseEnd_7838225 := by
    simpa [prefixWord, tailWord_7838225, baseEnd_7838225] using wordTrace_append hprefix tailTrace_7838225
  have hstable : (prefixWord ++ tailWord_7838225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838225).length < 2 ^ (prefixWord ++ tailWord_7838225).sum := by decide
  have hdescent : baseEnd_7838225 < baseStart_7838225 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838232 : List Nat := [2, 1, 2, 3, 3, 1, 2, 1, 2, 6]
def baseStart_7838232 : Nat := 118140960795 + 7838232 * 2 ^ 59
def prefixEnd_7838232 : Nat := 4983230072969 + 3 ^ 40 * 7838232 * 2
def baseEnd_7838232 : Nat := 1341593499150760704984211

theorem tailTrace_7838232 : CollatzResearch.WordTrace tailWord_7838232 prefixEnd_7838232 1341593499150760704984211 := by
  unfold tailWord_7838232
  simp only [CollatzResearch.WordTrace]
  refine ⟨142941903669715801147134475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190589204892954401529512633 142941903669715801147134475)
  ·
    refine ⟨214412855504573701720701713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142941903669715801147134475 214412855504573701720701713)
    ·
      refine ⟨160809641628430276290526285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214412855504573701720701713 160809641628430276290526285)
      ·
        refine ⟨60303615610661353608947357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160809641628430276290526285 60303615610661353608947357)
        ·
          refine ⟨22613855853998007603355259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60303615610661353608947357 22613855853998007603355259)
          ·
            refine ⟨33920783780997011405032889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22613855853998007603355259 33920783780997011405032889)
            ·
              refine ⟨25440587835747758553774667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33920783780997011405032889 25440587835747758553774667)
              ·
                refine ⟨38160881753621637830662001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25440587835747758553774667 38160881753621637830662001)
                ·
                  refine ⟨28620661315216228372996501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38160881753621637830662001 28620661315216228372996501)
                  ·
                    refine ⟨1341593499150760704984211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28620661315216228372996501 1341593499150760704984211)
                    ·
                      rfl

theorem cell23_7838232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 1, 2, 6].length) (baseStart_7838232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838232 prefixEnd_7838232 := by exact prefixLift 7838232
  have htrace : WordTrace (prefixWord ++ tailWord_7838232) baseStart_7838232 baseEnd_7838232 := by
    simpa [prefixWord, tailWord_7838232, baseEnd_7838232] using wordTrace_append hprefix tailTrace_7838232
  have hstable : (prefixWord ++ tailWord_7838232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838232).length < 2 ^ (prefixWord ++ tailWord_7838232).sum := by decide
  have hdescent : baseEnd_7838232 < baseStart_7838232 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838242 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 2, 1, 5]
def baseStart_7838242 : Nat := 118140960795 + 7838242 * 2 ^ 59
def prefixEnd_7838242 : Nat := 4983230072969 + 3 ^ 40 * 7838242 * 2
def baseEnd_7838242 : Nat := 4024785632258827075827587

theorem tailTrace_7838242 : CollatzResearch.WordTrace tailWord_7838242 prefixEnd_7838242 4024785632258827075827587 := by
  unfold tailWord_7838242
  simp only [CollatzResearch.WordTrace]
  refine ⟨71471043017348843500533245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190589448046263582668088653 71471043017348843500533245)
  ·
    refine ⟨26801641131505816312699967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71471043017348843500533245 26801641131505816312699967)
    ·
      refine ⟨40202461697258724469049951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26801641131505816312699967 40202461697258724469049951)
      ·
        refine ⟨60303692545888086703574927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40202461697258724469049951 60303692545888086703574927)
        ·
          refine ⟨90455538818832130055362391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60303692545888086703574927 90455538818832130055362391)
          ·
            refine ⟨135683308228248195083043587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90455538818832130055362391 135683308228248195083043587)
            ·
              refine ⟨203524962342372292624565381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135683308228248195083043587 203524962342372292624565381)
              ·
                refine ⟨38160930439194804867106009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203524962342372292624565381 38160930439194804867106009)
                ·
                  refine ⟨28620697829396103650329507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38160930439194804867106009 28620697829396103650329507)
                  ·
                    refine ⟨42931046744094155475494261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28620697829396103650329507 42931046744094155475494261)
                    ·
                      refine ⟨4024785632258827075827587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42931046744094155475494261 4024785632258827075827587)
                      ·
                        rfl

theorem cell23_7838242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_7838242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838242 prefixEnd_7838242 := by exact prefixLift 7838242
  have htrace : WordTrace (prefixWord ++ tailWord_7838242) baseStart_7838242 baseEnd_7838242 := by
    simpa [prefixWord, tailWord_7838242, baseEnd_7838242] using wordTrace_append hprefix tailTrace_7838242
  have hstable : (prefixWord ++ tailWord_7838242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838242).length < 2 ^ (prefixWord ++ tailWord_7838242).sum := by decide
  have hdescent : baseEnd_7838242 < baseStart_7838242 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838272 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 3]
def baseStart_7838272 : Nat := 118140960795 + 7838272 * 2 ^ 59
def prefixEnd_7838272 : Nat := 4983230072969 + 3 ^ 40 * 7838272 * 2
def baseEnd_7838272 : Nat := 4024801036678461958452449

theorem tailTrace_7838272 : CollatzResearch.WordTrace tailWord_7838272 prefixEnd_7838272 4024801036678461958452449 := by
  unfold tailWord_7838272
  simp only [CollatzResearch.WordTrace]
  refine ⟨142942633129643344562862535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190590177506191126083816713 142942633129643344562862535)
  ·
    refine ⟨214413949694465016844293803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142942633129643344562862535 214413949694465016844293803)
    ·
      refine ⟨321620924541697525266440705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214413949694465016844293803 321620924541697525266440705)
      ·
        refine ⟨241215693406273143949830529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321620924541697525266440705 241215693406273143949830529)
        ·
          refine ⟨180911770054704857962372897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241215693406273143949830529 180911770054704857962372897)
          ·
            refine ⟨135683827541028643471779673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180911770054704857962372897 135683827541028643471779673)
            ·
              refine ⟨101762870655771482603834755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135683827541028643471779673 101762870655771482603834755)
              ·
                refine ⟨152644305983657223905752133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101762870655771482603834755 152644305983657223905752133)
                ·
                  refine ⟨28620807371935729482328525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152644305983657223905752133 28620807371935729482328525)
                  ·
                    refine ⟨10732802764475898555873197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28620807371935729482328525 10732802764475898555873197)
                    ·
                      refine ⟨4024801036678461958452449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10732802764475898555873197 4024801036678461958452449)
                      ·
                        rfl

theorem cell23_7838272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 3].length) (baseStart_7838272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838272 prefixEnd_7838272 := by exact prefixLift 7838272
  have htrace : WordTrace (prefixWord ++ tailWord_7838272) baseStart_7838272 baseEnd_7838272 := by
    simpa [prefixWord, tailWord_7838272, baseEnd_7838272] using wordTrace_append hprefix tailTrace_7838272
  have hstable : (prefixWord ++ tailWord_7838272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838272).length < 2 ^ (prefixWord ++ tailWord_7838272).sum := by decide
  have hdescent : baseEnd_7838272 < baseStart_7838272 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838279 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 7]
def baseStart_7838279 : Nat := 118140960795 + 7838279 * 2 ^ 59
def prefixEnd_7838279 : Nat := 4983230072969 + 3 ^ 40 * 7838279 * 2
def baseEnd_7838279 : Nat := 447200514560338159007213

theorem tailTrace_7838279 : CollatzResearch.WordTrace tailWord_7838279 prefixEnd_7838279 447200514560338159007213 := by
  unfold tailWord_7838279
  simp only [CollatzResearch.WordTrace]
  refine ⟨285885521570261329321229891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190590347713507552880819927 285885521570261329321229891)
  ·
    refine ⟨428828282355391993981844837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285885521570261329321229891 428828282355391993981844837)
    ·
      refine ⟨80405302941635998871595907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428828282355391993981844837 80405302941635998871595907)
      ·
        refine ⟨120607954412453998307393861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80405302941635998871595907 120607954412453998307393861)
        ·
          refine ⟨22613991452335124682636349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120607954412453998307393861 22613991452335124682636349)
          ·
            refine ⟨8480246794625671755988631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22613991452335124682636349 8480246794625671755988631)
            ·
              refine ⟨12720370191938507633982947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8480246794625671755988631 12720370191938507633982947)
              ·
                refine ⟨19080555287907761450974421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12720370191938507633982947 19080555287907761450974421)
                ·
                  refine ⟨447200514560338159007213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19080555287907761450974421 447200514560338159007213)
                  ·
                    rfl

theorem cell23_7838279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 7].length) (baseStart_7838279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838279 prefixEnd_7838279 := by exact prefixLift 7838279
  have htrace : WordTrace (prefixWord ++ tailWord_7838279) baseStart_7838279 baseEnd_7838279 := by
    simpa [prefixWord, tailWord_7838279, baseEnd_7838279] using wordTrace_append hprefix tailTrace_7838279
  have hstable : (prefixWord ++ tailWord_7838279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838279).length < 2 ^ (prefixWord ++ tailWord_7838279).sum := by decide
  have hdescent : baseEnd_7838279 < baseStart_7838279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838329 : List Nat := [1, 2, 1, 3, 3, 2, 2, 2, 2, 1, 4]
def baseStart_7838329 : Nat := 118140960795 + 7838329 * 2 ^ 59
def prefixEnd_7838329 : Nat := 4983230072969 + 3 ^ 40 * 7838329 * 2
def baseEnd_7838329 : Nat := 4024830305075768235439687

theorem tailTrace_7838329 : CollatzResearch.WordTrace tailWord_7838329 prefixEnd_7838329 4024830305075768235439687 := by
  unfold tailWord_7838329
  simp only [CollatzResearch.WordTrace]
  refine ⟨285887345220080187860550041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190591563480053458573700027 285887345220080187860550041)
  ·
    refine ⟨214415508915060140895412531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285887345220080187860550041 214415508915060140895412531)
    ·
      refine ⟨321623263372590211343118797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214415508915060140895412531 321623263372590211343118797)
      ·
        refine ⟨120608723764721329253669549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321623263372590211343118797 120608723764721329253669549)
        ·
          refine ⟨45228271411770498470126081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120608723764721329253669549 45228271411770498470126081)
          ·
            refine ⟨33921203558827873852594561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45228271411770498470126081 33921203558827873852594561)
            ·
              refine ⟨25440902669120905389445921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33921203558827873852594561 25440902669120905389445921)
              ·
                refine ⟨19080677001840679042084441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25440902669120905389445921 19080677001840679042084441)
                ·
                  refine ⟨14310507751380509281563331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19080677001840679042084441 14310507751380509281563331)
                  ·
                    refine ⟨21465761627070763922344997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14310507751380509281563331 21465761627070763922344997)
                    ·
                      refine ⟨4024830305075768235439687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21465761627070763922344997 4024830305075768235439687)
                      ·
                        rfl

theorem cell23_7838329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 2, 2, 2, 1, 4].length) (baseStart_7838329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838329 prefixEnd_7838329 := by exact prefixLift 7838329
  have htrace : WordTrace (prefixWord ++ tailWord_7838329) baseStart_7838329 baseEnd_7838329 := by
    simpa [prefixWord, tailWord_7838329, baseEnd_7838329] using wordTrace_append hprefix tailTrace_7838329
  have hstable : (prefixWord ++ tailWord_7838329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838329).length < 2 ^ (prefixWord ++ tailWord_7838329).sum := by decide
  have hdescent : baseEnd_7838329 < baseStart_7838329 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838356 : List Nat := [2, 4, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_7838356 : Nat := 118140960795 + 7838356 * 2 ^ 59
def prefixEnd_7838356 : Nat := 4983230072969 + 3 ^ 40 * 7838356 * 2
def baseEnd_7838356 : Nat := 1341614723017813209934021

theorem tailTrace_7838356 : CollatzResearch.WordTrace tailWord_7838356 prefixEnd_7838356 1341614723017813209934021 := by
  unfold tailWord_7838356
  simp only [CollatzResearch.WordTrace]
  refine ⟨142944164995491185735891461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190592219993988247647855281 142944164995491185735891461)
  ·
    refine ⟨26802030936654597325479649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142944164995491185735891461 26802030936654597325479649)
    ·
      refine ⟨20101523202490947994109737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26802030936654597325479649 20101523202490947994109737)
      ·
        refine ⟨15076142401868210995582303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20101523202490947994109737 15076142401868210995582303)
        ·
          refine ⟨22614213602802316493373455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15076142401868210995582303 22614213602802316493373455)
          ·
            refine ⟨33921320404203474740060183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22614213602802316493373455 33921320404203474740060183)
            ·
              refine ⟨50881980606305212110090275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33921320404203474740060183 50881980606305212110090275)
              ·
                refine ⟨76322970909457818165135413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50881980606305212110090275 76322970909457818165135413)
                ·
                  refine ⟨7155278522761670452981445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76322970909457818165135413 7155278522761670452981445)
                  ·
                    refine ⟨1341614723017813209934021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7155278522761670452981445 1341614723017813209934021)
                    ·
                      rfl

theorem cell23_7838356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_7838356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838356 prefixEnd_7838356 := by exact prefixLift 7838356
  have htrace : WordTrace (prefixWord ++ tailWord_7838356) baseStart_7838356 baseEnd_7838356 := by
    simpa [prefixWord, tailWord_7838356, baseEnd_7838356] using wordTrace_append hprefix tailTrace_7838356
  have hstable : (prefixWord ++ tailWord_7838356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838356).length < 2 ^ (prefixWord ++ tailWord_7838356).sum := by decide
  have hdescent : baseEnd_7838356 < baseStart_7838356 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838366 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_7838366 : Nat := 118140960795 + 7838366 * 2 ^ 59
def prefixEnd_7838366 : Nat := 4983230072969 + 3 ^ 40 * 7838366 * 2
def baseEnd_7838366 : Nat := 4024849303859984590677017

theorem tailTrace_7838366 : CollatzResearch.WordTrace tailWord_7838366 prefixEnd_7838366 4024849303859984590677017 := by
  unfold tailWord_7838366
  simp only [CollatzResearch.WordTrace]
  refine ⟨35736086840118267897455869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190592463147297428786431301 35736086840118267897455869)
  ·
    refine ⟨13401032565044350461545951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35736086840118267897455869 13401032565044350461545951)
    ·
      refine ⟨20101548847566525692318927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13401032565044350461545951 20101548847566525692318927)
      ·
        refine ⟨30152323271349788538478391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20101548847566525692318927 30152323271349788538478391)
        ·
          refine ⟨45228484907024682807717587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30152323271349788538478391 45228484907024682807717587)
          ·
            refine ⟨67842727360537024211576381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45228484907024682807717587 67842727360537024211576381)
            ·
              refine ⟨25441022760201384079341143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67842727360537024211576381 25441022760201384079341143)
              ·
                refine ⟨38161534140302076119011715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25441022760201384079341143 38161534140302076119011715)
                ·
                  refine ⟨57242301210453114178517573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38161534140302076119011715 57242301210453114178517573)
                  ·
                    refine ⟨10732931476959958908472045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57242301210453114178517573 10732931476959958908472045)
                    ·
                      refine ⟨4024849303859984590677017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10732931476959958908472045 4024849303859984590677017)
                      ·
                        rfl

theorem cell23_7838366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_7838366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838366 prefixEnd_7838366 := by exact prefixLift 7838366
  have htrace : WordTrace (prefixWord ++ tailWord_7838366) baseStart_7838366 baseEnd_7838366 := by
    simpa [prefixWord, tailWord_7838366, baseEnd_7838366] using wordTrace_append hprefix tailTrace_7838366
  have hstable : (prefixWord ++ tailWord_7838366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838366).length < 2 ^ (prefixWord ++ tailWord_7838366).sum := by decide
  have hdescent : baseEnd_7838366 < baseStart_7838366 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838389 : List Nat := [1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_7838389 : Nat := 118140960795 + 7838389 * 2 ^ 59
def prefixEnd_7838389 : Nat := 4983230072969 + 3 ^ 40 * 7838389 * 2
def baseEnd_7838389 : Nat := 4024861113915038000689411

theorem tailTrace_7838389 : CollatzResearch.WordTrace tailWord_7838389 prefixEnd_7838389 4024861113915038000689411 := by
  unfold tailWord_7838389
  simp only [CollatzResearch.WordTrace]
  refine ⟨285889533599862818107734221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190593022399908545405156147 285889533599862818107734221)
  ·
    refine ⟨107208575099948556790400333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285889533599862818107734221 107208575099948556790400333)
    ·
      refine ⟨40203215662480708796400125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107208575099948556790400333 40203215662480708796400125)
      ·
        refine ⟨15076205873430265798650047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40203215662480708796400125 15076205873430265798650047)
        ·
          refine ⟨22614308810145398697975071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15076205873430265798650047 22614308810145398697975071)
          ·
            refine ⟨33921463215218098046962607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22614308810145398697975071 33921463215218098046962607)
            ·
              refine ⟨50882194822827147070443911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33921463215218098046962607 50882194822827147070443911)
              ·
                refine ⟨76323292234240720605665867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50882194822827147070443911 76323292234240720605665867)
                ·
                  refine ⟨114484938351361080908498801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76323292234240720605665867 114484938351361080908498801)
                  ·
                    refine ⟨85863703763520810681374101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114484938351361080908498801 85863703763520810681374101)
                    ·
                      refine ⟨4024861113915038000689411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85863703763520810681374101 4024861113915038000689411)
                      ·
                        rfl

theorem cell23_7838389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_7838389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838389 prefixEnd_7838389 := by exact prefixLift 7838389
  have htrace : WordTrace (prefixWord ++ tailWord_7838389) baseStart_7838389 baseEnd_7838389 := by
    simpa [prefixWord, tailWord_7838389, baseEnd_7838389] using wordTrace_append hprefix tailTrace_7838389
  have hstable : (prefixWord ++ tailWord_7838389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838389).length < 2 ^ (prefixWord ++ tailWord_7838389).sum := by decide
  have hdescent : baseEnd_7838389 < baseStart_7838389 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838390 : List Nat := [5, 1, 3, 1, 2, 1, 2, 1, 3, 4]
def baseStart_7838390 : Nat := 118140960795 + 7838390 * 2 ^ 59
def prefixEnd_7838390 : Nat := 4983230072969 + 3 ^ 40 * 7838390 * 2
def baseEnd_7838390 : Nat := 1341620542465230832258969

theorem tailTrace_7838390 : CollatzResearch.WordTrace tailWord_7838390 prefixEnd_7838390 1341620542465230832258969 := by
  unfold tailWord_7838390
  simp only [CollatzResearch.WordTrace]
  refine ⟨17868098129553699704907539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190593046715239463519013749 17868098129553699704907539)
  ·
    refine ⟨26802147194330549557361309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17868098129553699704907539 26802147194330549557361309)
    ·
      refine ⟨10050805197873956084010491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26802147194330549557361309 10050805197873956084010491)
      ·
        refine ⟨15076207796810934126015737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10050805197873956084010491 15076207796810934126015737)
        ·
          refine ⟨11307155847608200594511803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15076207796810934126015737 11307155847608200594511803)
          ·
            refine ⟨16960733771412300891767705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11307155847608200594511803 16960733771412300891767705)
            ·
              refine ⟨12720550328559225668825779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16960733771412300891767705 12720550328559225668825779)
              ·
                refine ⟨19080825492838838503238669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12720550328559225668825779 19080825492838838503238669)
                ·
                  refine ⟨7155309559814564438714501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19080825492838838503238669 7155309559814564438714501)
                  ·
                    refine ⟨1341620542465230832258969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7155309559814564438714501 1341620542465230832258969)
                    ·
                      rfl

theorem cell23_7838390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_7838390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838390 prefixEnd_7838390 := by exact prefixLift 7838390
  have htrace : WordTrace (prefixWord ++ tailWord_7838390) baseStart_7838390 baseEnd_7838390 := by
    simpa [prefixWord, tailWord_7838390, baseEnd_7838390] using wordTrace_append hprefix tailTrace_7838390
  have hstable : (prefixWord ++ tailWord_7838390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838390).length < 2 ^ (prefixWord ++ tailWord_7838390).sum := by decide
  have hdescent : baseEnd_7838390 < baseStart_7838390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838436 : List Nat := [2, 3, 1, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_7838436 : Nat := 118140960795 + 7838436 * 2 ^ 59
def prefixEnd_7838436 : Nat := 4983230072969 + 3 ^ 40 * 7838436 * 2
def baseEnd_7838436 : Nat := 4024885247505799316801695

theorem tailTrace_7838436 : CollatzResearch.WordTrace tailWord_7838436 prefixEnd_7838436 4024885247505799316801695 := by
  unfold tailWord_7838436
  simp only [CollatzResearch.WordTrace]
  refine ⟨142945623915346272567347581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190594165220461696756463441 142945623915346272567347581)
  ·
    refine ⟨53604608968254852212755343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142945623915346272567347581 53604608968254852212755343)
    ·
      refine ⟨80406913452382278319133015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53604608968254852212755343 80406913452382278319133015)
      ·
        refine ⟨120610370178573417478699523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80406913452382278319133015 120610370178573417478699523)
        ·
          refine ⟨180915555267860126218049285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120610370178573417478699523 180915555267860126218049285)
          ·
            refine ⟨33921666612723773665884241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 180915555267860126218049285 33921666612723773665884241)
            ·
              refine ⟨25441249959542830249413181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33921666612723773665884241 25441249959542830249413181)
              ·
                refine ⟨9540468734828561343529943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25441249959542830249413181 9540468734828561343529943)
                ·
                  refine ⟨14310703102242842015294915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9540468734828561343529943 14310703102242842015294915)
                  ·
                    refine ⟨21466054653364263022942373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14310703102242842015294915 21466054653364263022942373)
                    ·
                      refine ⟨4024885247505799316801695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21466054653364263022942373 4024885247505799316801695)
                      ·
                        rfl

theorem cell23_7838436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_7838436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838436 prefixEnd_7838436 := by exact prefixLift 7838436
  have htrace : WordTrace (prefixWord ++ tailWord_7838436) baseStart_7838436 baseEnd_7838436 := by
    simpa [prefixWord, tailWord_7838436, baseEnd_7838436] using wordTrace_append hprefix tailTrace_7838436
  have hstable : (prefixWord ++ tailWord_7838436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838436).length < 2 ^ (prefixWord ++ tailWord_7838436).sum := by decide
  have hdescent : baseEnd_7838436 < baseStart_7838436 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838446 : List Nat := [4, 1, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_7838446 : Nat := 118140960795 + 7838446 * 2 ^ 59
def prefixEnd_7838446 : Nat := 4983230072969 + 3 ^ 40 * 7838446 * 2
def baseEnd_7838446 : Nat := 1341630127437448092558883

theorem tailTrace_7838446 : CollatzResearch.WordTrace tailWord_7838446 prefixEnd_7838446 1341630127437448092558883 := by
  unfold tailWord_7838446
  simp only [CollatzResearch.WordTrace]
  refine ⟨35736451570082039605319899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190594408373770877895039461 35736451570082039605319899)
  ·
    refine ⟨53604677355123059407979849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35736451570082039605319899 53604677355123059407979849)
    ·
      refine ⟨40203508016342294555984887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53604677355123059407979849 40203508016342294555984887)
      ·
        refine ⟨60305262024513441833977331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40203508016342294555984887 60305262024513441833977331)
        ·
          refine ⟨90457893036770162750965997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60305262024513441833977331 90457893036770162750965997)
          ·
            refine ⟨33921709888788811031612249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90457893036770162750965997 33921709888788811031612249)
            ·
              refine ⟨25441282416591608273709187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33921709888788811031612249 25441282416591608273709187)
              ·
                refine ⟨38161923624887412410563781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25441282416591608273709187 38161923624887412410563781)
                ·
                  refine ⟨7155360679666389826980709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38161923624887412410563781 7155360679666389826980709)
                  ·
                    refine ⟨1341630127437448092558883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7155360679666389826980709 1341630127437448092558883)
                    ·
                      rfl

theorem cell23_7838446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_7838446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838446 prefixEnd_7838446 := by exact prefixLift 7838446
  have htrace : WordTrace (prefixWord ++ tailWord_7838446) baseStart_7838446 baseEnd_7838446 := by
    simpa [prefixWord, tailWord_7838446, baseEnd_7838446] using wordTrace_append hprefix tailTrace_7838446
  have hstable : (prefixWord ++ tailWord_7838446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838446).length < 2 ^ (prefixWord ++ tailWord_7838446).sum := by decide
  have hdescent : baseEnd_7838446 < baseStart_7838446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838466 : List Nat := [3, 4, 1, 1, 1, 2, 2, 1, 1, 1, 6]
def baseStart_7838466 : Nat := 118140960795 + 7838466 * 2 ^ 59
def prefixEnd_7838466 : Nat := 4983230072969 + 3 ^ 40 * 7838466 * 2
def baseEnd_7838466 : Nat := 4024900651925434199426557

theorem tailTrace_7838466 : CollatzResearch.WordTrace tailWord_7838466 prefixEnd_7838466 4024900651925434199426557 := by
  unfold tailWord_7838466
  simp only [CollatzResearch.WordTrace]
  refine ⟨71473085505145965064571813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190594894680389240172191501 71473085505145965064571813)
  ·
    refine ⟨13401203532214868449607215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71473085505145965064571813 13401203532214868449607215)
    ·
      refine ⟨20101805298322302674410823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13401203532214868449607215 20101805298322302674410823)
      ·
        refine ⟨30152707947483454011616235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20101805298322302674410823 30152707947483454011616235)
        ·
          refine ⟨45229061921225181017424353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30152707947483454011616235 45229061921225181017424353)
          ·
            refine ⟨33921796440918885763068265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45229061921225181017424353 33921796440918885763068265)
            ·
              refine ⟨25441347330689164322301199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33921796440918885763068265 25441347330689164322301199)
              ·
                refine ⟨38162020996033746483451799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25441347330689164322301199 38162020996033746483451799)
                ·
                  refine ⟨57243031494050619725177699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38162020996033746483451799 57243031494050619725177699)
                  ·
                    refine ⟨85864547241075929587766549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57243031494050619725177699 85864547241075929587766549)
                    ·
                      refine ⟨4024900651925434199426557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85864547241075929587766549 4024900651925434199426557)
                      ·
                        rfl

theorem cell23_7838466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_7838466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838466 prefixEnd_7838466 := by exact prefixLift 7838466
  have htrace : WordTrace (prefixWord ++ tailWord_7838466) baseStart_7838466 baseEnd_7838466 := by
    simpa [prefixWord, tailWord_7838466, baseEnd_7838466] using wordTrace_append hprefix tailTrace_7838466
  have hstable : (prefixWord ++ tailWord_7838466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838466).length < 2 ^ (prefixWord ++ tailWord_7838466).sum := by decide
  have hdescent : baseEnd_7838466 < baseStart_7838466 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838469 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 5, 3, 3]
def baseStart_7838469 : Nat := 118140960795 + 7838469 * 2 ^ 59
def prefixEnd_7838469 : Nat := 4983230072969 + 3 ^ 40 * 7838469 * 2
def baseEnd_7838469 : Nat := 4024902192367397687689043

theorem tailTrace_7838469 : CollatzResearch.WordTrace tailWord_7838469 prefixEnd_7838469 4024902192367397687689043 := by
  unfold tailWord_7838469
  simp only [CollatzResearch.WordTrace]
  refine ⟨285892451439572991770646461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190594967626381994513764307 285892451439572991770646461)
  ·
    refine ⟨107209669289839871913992423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285892451439572991770646461 107209669289839871913992423)
    ·
      refine ⟨160814503934759807870988635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107209669289839871913992423 160814503934759807870988635)
      ·
        refine ⟨241221755902139711806482953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160814503934759807870988635 241221755902139711806482953)
        ·
          refine ⟨180916316926604783854862215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241221755902139711806482953 180916316926604783854862215)
          ·
            refine ⟨271374475389907175782293323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180916316926604783854862215 271374475389907175782293323)
            ·
              refine ⟨407061713084860763673439985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271374475389907175782293323 407061713084860763673439985)
              ·
                refine ⟨305296284813645572755079989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407061713084860763673439985 305296284813645572755079989)
                ·
                  refine ⟨28621526701279272445788749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 305296284813645572755079989 28621526701279272445788749)
                  ·
                    refine ⟨10733072512979727167170781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28621526701279272445788749 10733072512979727167170781)
                    ·
                      refine ⟨4024902192367397687689043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10733072512979727167170781 4024902192367397687689043)
                      ·
                        rfl

theorem cell23_7838469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 5, 3, 3].length) (baseStart_7838469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838469 prefixEnd_7838469 := by exact prefixLift 7838469
  have htrace : WordTrace (prefixWord ++ tailWord_7838469) baseStart_7838469 baseEnd_7838469 := by
    simpa [prefixWord, tailWord_7838469, baseEnd_7838469] using wordTrace_append hprefix tailTrace_7838469
  have hstable : (prefixWord ++ tailWord_7838469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838469).length < 2 ^ (prefixWord ++ tailWord_7838469).sum := by decide
  have hdescent : baseEnd_7838469 < baseStart_7838469 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838519 : List Nat := [1, 1, 3, 1, 2, 1, 5, 1, 2, 6]
def baseStart_7838519 : Nat := 118140960795 + 7838519 * 2 ^ 59
def prefixEnd_7838519 : Nat := 4983230072969 + 3 ^ 40 * 7838519 * 2
def baseEnd_7838519 : Nat := 1341642622133374164021271

theorem tailTrace_7838519 : CollatzResearch.WordTrace tailWord_7838519 prefixEnd_7838519 1341642622133374164021271 := by
  unfold tailWord_7838519
  simp only [CollatzResearch.WordTrace]
  refine ⟨285894275089391850309966611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190596183392927900206644407 285894275089391850309966611)
  ·
    refine ⟨428841412634087775464949917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285894275089391850309966611 428841412634087775464949917)
    ·
      refine ⟨160815529737782915799356219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428841412634087775464949917 160815529737782915799356219)
      ·
        refine ⟨241223294606674373699034329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160815529737782915799356219 241223294606674373699034329)
        ·
          refine ⟨180917470955005780274275747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241223294606674373699034329 180917470955005780274275747)
          ·
            refine ⟨271376206432508670411413621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180917470955005780274275747 271376206432508670411413621)
            ·
              refine ⟨25441519353047687851070027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271376206432508670411413621 25441519353047687851070027)
              ·
                refine ⟨38162279029571531776605041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25441519353047687851070027 38162279029571531776605041)
                ·
                  refine ⟨28621709272178648832453781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38162279029571531776605041 28621709272178648832453781)
                  ·
                    refine ⟨1341642622133374164021271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28621709272178648832453781 1341642622133374164021271)
                    ·
                      rfl

theorem cell23_7838519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 6].length) (baseStart_7838519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838519 prefixEnd_7838519 := by exact prefixLift 7838519
  have htrace : WordTrace (prefixWord ++ tailWord_7838519) baseStart_7838519 baseEnd_7838519 := by
    simpa [prefixWord, tailWord_7838519, baseEnd_7838519] using wordTrace_append hprefix tailTrace_7838519
  have hstable : (prefixWord ++ tailWord_7838519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838519).length < 2 ^ (prefixWord ++ tailWord_7838519).sum := by decide
  have hdescent : baseEnd_7838519 < baseStart_7838519 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838549 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 9]
def baseStart_7838549 : Nat := 118140960795 + 7838549 * 2 ^ 59
def prefixEnd_7838549 : Nat := 4983230072969 + 3 ^ 40 * 7838549 * 2
def baseEnd_7838549 : Nat := 447215918979973041632075

theorem tailTrace_7838549 : CollatzResearch.WordTrace tailWord_7838549 prefixEnd_7838549 447215918979973041632075 := by
  unfold tailWord_7838549
  simp only [CollatzResearch.WordTrace]
  refine ⟨285895369279283165433558701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190596912852855443622372467 285895369279283165433558701)
  ·
    refine ⟨107210763479731187037584513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285895369279283165433558701 107210763479731187037584513)
    ·
      refine ⟨80408072609798390278188385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107210763479731187037584513 80408072609798390278188385)
      ·
        refine ⟨60306054457348792708641289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80408072609798390278188385 60306054457348792708641289)
        ·
          refine ⟨45229540843011594531480967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60306054457348792708641289 45229540843011594531480967)
          ·
            refine ⟨67844311264517391797221451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45229540843011594531480967 67844311264517391797221451)
            ·
              refine ⟨101766466896776087695832177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67844311264517391797221451 101766466896776087695832177)
              ·
                refine ⟨76324850172582065771874133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101766466896776087695832177 76324850172582065771874133)
                ·
                  refine ⟨447215918979973041632075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 76324850172582065771874133 447215918979973041632075)
                  ·
                    rfl

theorem cell23_7838549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 9].length) (baseStart_7838549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838549 prefixEnd_7838549 := by exact prefixLift 7838549
  have htrace : WordTrace (prefixWord ++ tailWord_7838549) baseStart_7838549 baseEnd_7838549 := by
    simpa [prefixWord, tailWord_7838549, baseEnd_7838549] using wordTrace_append hprefix tailTrace_7838549
  have hstable : (prefixWord ++ tailWord_7838549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838549).length < 2 ^ (prefixWord ++ tailWord_7838549).sum := by decide
  have hdescent : baseEnd_7838549 < baseStart_7838549 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838576 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 3]
def baseStart_7838576 : Nat := 118140960795 + 7838576 * 2 ^ 59
def prefixEnd_7838576 : Nat := 4983230072969 + 3 ^ 40 * 7838576 * 2
def baseEnd_7838576 : Nat := 4024957134797428769051051

theorem tailTrace_7838576 : CollatzResearch.WordTrace tailWord_7838576 prefixEnd_7838576 4024957134797428769051051 := by
  unfold tailWord_7838576
  simp only [CollatzResearch.WordTrace]
  refine ⟨142948177025092674522395791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190597569366790232696527721 142948177025092674522395791)
  ·
    refine ⟨214422265537639011783593687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142948177025092674522395791 214422265537639011783593687)
    ·
      refine ⟨321633398306458517675390531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214422265537639011783593687 321633398306458517675390531)
      ·
        refine ⟨482450097459687776513085797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321633398306458517675390531 482450097459687776513085797)
        ·
          refine ⟨90459393273691458096203587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 482450097459687776513085797 90459393273691458096203587)
          ·
            refine ⟨135689089910537187144305381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90459393273691458096203587 135689089910537187144305381)
            ·
              refine ⟨25441704358225722589557259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135689089910537187144305381 25441704358225722589557259)
              ·
                refine ⟨38162556537338583884335889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25441704358225722589557259 38162556537338583884335889)
                ·
                  refine ⟨28621917403003937913251917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38162556537338583884335889 28621917403003937913251917)
                  ·
                    refine ⟨10733219026126476717469469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28621917403003937913251917 10733219026126476717469469)
                    ·
                      refine ⟨4024957134797428769051051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10733219026126476717469469 4024957134797428769051051)
                      ·
                        rfl

theorem cell23_7838576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3, 3].length) (baseStart_7838576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838576 prefixEnd_7838576 := by exact prefixLift 7838576
  have htrace : WordTrace (prefixWord ++ tailWord_7838576) baseStart_7838576 baseEnd_7838576 := by
    simpa [prefixWord, tailWord_7838576, baseEnd_7838576] using wordTrace_append hprefix tailTrace_7838576
  have hstable : (prefixWord ++ tailWord_7838576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838576).length < 2 ^ (prefixWord ++ tailWord_7838576).sum := by decide
  have hdescent : baseEnd_7838576 < baseStart_7838576 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838577 : List Nat := [1, 2, 2, 2, 1, 5, 3, 1, 2, 2, 2]
def baseStart_7838577 : Nat := 118140960795 + 7838577 * 2 ^ 59
def prefixEnd_7838577 : Nat := 4983230072969 + 3 ^ 40 * 7838577 * 2
def baseEnd_7838577 : Nat := 4024957648278083265138547

theorem tailTrace_7838577 : CollatzResearch.WordTrace tailWord_7838577 prefixEnd_7838577 4024957648278083265138547 := by
  unfold tailWord_7838577
  simp only [CollatzResearch.WordTrace]
  refine ⟨285896390523181726215577985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190597593682121150810385323 285896390523181726215577985)
  ·
    refine ⟨214422292892386294661683489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285896390523181726215577985 214422292892386294661683489)
    ·
      refine ⟨160816719669289720996262617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214422292892386294661683489 160816719669289720996262617)
      ·
        refine ⟨120612539751967290747196963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160816719669289720996262617 120612539751967290747196963)
        ·
          refine ⟨180918809627950936120795445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120612539751967290747196963 180918809627950936120795445)
          ·
            refine ⟨16961138402620400261324573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180918809627950936120795445 16961138402620400261324573)
            ·
              refine ⟨6360426900982650097996715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16961138402620400261324573 6360426900982650097996715)
              ·
                refine ⟨9540640351473975146995073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6360426900982650097996715 9540640351473975146995073)
                ·
                  refine ⟨7155480263605481360246305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9540640351473975146995073 7155480263605481360246305)
                  ·
                    refine ⟨5366610197704111020184729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7155480263605481360246305 5366610197704111020184729)
                    ·
                      refine ⟨4024957648278083265138547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5366610197704111020184729 4024957648278083265138547)
                      ·
                        rfl

theorem cell23_7838577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 3, 1, 2, 2, 2].length) (baseStart_7838577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838577 prefixEnd_7838577 := by exact prefixLift 7838577
  have htrace : WordTrace (prefixWord ++ tailWord_7838577) baseStart_7838577 baseEnd_7838577 := by
    simpa [prefixWord, tailWord_7838577, baseEnd_7838577] using wordTrace_append hprefix tailTrace_7838577
  have hstable : (prefixWord ++ tailWord_7838577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838577).length < 2 ^ (prefixWord ++ tailWord_7838577).sum := by decide
  have hdescent : baseEnd_7838577 < baseStart_7838577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838579 : List Nat := [1, 1, 1, 2, 2, 1, 5, 2, 1, 7]
def baseStart_7838579 : Nat := 118140960795 + 7838579 * 2 ^ 59
def prefixEnd_7838579 : Nat := 4983230072969 + 3 ^ 40 * 7838579 * 2
def baseEnd_7838579 : Nat := 1341652891746464085771179

theorem tailTrace_7838579 : CollatzResearch.WordTrace tailWord_7838579 prefixEnd_7838579 1341652891746464085771179 := by
  unfold tailWord_7838579
  simp only [CollatzResearch.WordTrace]
  refine ⟨285896463469174480557150791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190597642312782987038100527 285896463469174480557150791)
  ·
    refine ⟨428844695203761720835726187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285896463469174480557150791 428844695203761720835726187)
    ·
      refine ⟨643267042805642581253589281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428844695203761720835726187 643267042805642581253589281)
      ·
        refine ⟨482450282104231935940191961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643267042805642581253589281 482450282104231935940191961)
        ·
          refine ⟨361837711578173951955143971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482450282104231935940191961 361837711578173951955143971)
          ·
            refine ⟨542756567367260927932715957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361837711578173951955143971 542756567367260927932715957)
            ·
              refine ⟨50883428190680711993692121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 542756567367260927932715957 50883428190680711993692121)
              ·
                refine ⟨38162571143010533995269091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50883428190680711993692121 38162571143010533995269091)
                ·
                  refine ⟨57243856714515800992903637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38162571143010533995269091 57243856714515800992903637)
                  ·
                    refine ⟨1341652891746464085771179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57243856714515800992903637 1341652891746464085771179)
                    ·
                      rfl

theorem cell23_7838579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 7].length) (baseStart_7838579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838579 prefixEnd_7838579 := by exact prefixLift 7838579
  have htrace : WordTrace (prefixWord ++ tailWord_7838579) baseStart_7838579 baseEnd_7838579 := by
    simpa [prefixWord, tailWord_7838579, baseEnd_7838579] using wordTrace_append hprefix tailTrace_7838579
  have hstable : (prefixWord ++ tailWord_7838579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838579).length < 2 ^ (prefixWord ++ tailWord_7838579).sum := by decide
  have hdescent : baseEnd_7838579 < baseStart_7838579 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838596 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 2, 5]
def baseStart_7838596 : Nat := 118140960795 + 7838596 * 2 ^ 59
def prefixEnd_7838596 : Nat := 4983230072969 + 3 ^ 40 * 7838596 * 2
def baseEnd_7838596 : Nat := 1341655801470172896933653

theorem tailTrace_7838596 : CollatzResearch.WordTrace tailWord_7838596 prefixEnd_7838596 1341655801470172896933653 := by
  unfold tailWord_7838596
  simp only [CollatzResearch.WordTrace]
  refine ⟨142948541755056446230259821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190598055673408594973679761 142948541755056446230259821)
  ·
    refine ⟨53605703158146167336347433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142948541755056446230259821 53605703158146167336347433)
    ·
      refine ⟨40204277368609625502260575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53605703158146167336347433 40204277368609625502260575)
      ·
        refine ⟨60306416052914438253390863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40204277368609625502260575 60306416052914438253390863)
        ·
          refine ⟨90459624079371657380086295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60306416052914438253390863 90459624079371657380086295)
          ·
            refine ⟨135689436119057486070129443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90459624079371657380086295 135689436119057486070129443)
            ·
              refine ⟨203534154178586229105194165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135689436119057486070129443 203534154178586229105194165)
              ·
                refine ⟨19081326954242458978611953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 203534154178586229105194165 19081326954242458978611953)
                ·
                  refine ⟨14310995215681844233958965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19081326954242458978611953 14310995215681844233958965)
                  ·
                    refine ⟨1341655801470172896933653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14310995215681844233958965 1341655801470172896933653)
                    ·
                      rfl

theorem cell23_7838596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_7838596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838596 prefixEnd_7838596 := by exact prefixLift 7838596
  have htrace : WordTrace (prefixWord ++ tailWord_7838596) baseStart_7838596 baseEnd_7838596 := by
    simpa [prefixWord, tailWord_7838596, baseEnd_7838596] using wordTrace_append hprefix tailTrace_7838596
  have hstable : (prefixWord ++ tailWord_7838596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838596).length < 2 ^ (prefixWord ++ tailWord_7838596).sum := by decide
  have hdescent : baseEnd_7838596 < baseStart_7838596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838600 : List Nat := [2, 1, 3, 3, 2, 3, 1, 3, 5]
def baseStart_7838600 : Nat := 118140960795 + 7838600 * 2 ^ 59
def prefixEnd_7838600 : Nat := 4983230072969 + 3 ^ 40 * 7838600 * 2
def baseEnd_7838600 : Nat := 447218828703681852794549

theorem tailTrace_7838600 : CollatzResearch.WordTrace tailWord_7838600 prefixEnd_7838600 447218828703681852794549 := by
  unfold tailWord_7838600
  simp only [CollatzResearch.WordTrace]
  refine ⟨142948614701049200571832627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190598152934732267429110169 142948614701049200571832627)
  ·
    refine ⟨214422922051573800857748941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142948614701049200571832627 214422922051573800857748941)
    ·
      refine ⟨80408595769340175321655853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214422922051573800857748941 80408595769340175321655853)
      ·
        refine ⟨30153223413502565745620945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80408595769340175321655853 30153223413502565745620945)
        ·
          refine ⟨22614917560126924309215709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30153223413502565745620945 22614917560126924309215709)
          ·
            refine ⟨8480594085047596615955891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22614917560126924309215709 8480594085047596615955891)
            ·
              refine ⟨12720891127571394923933837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8480594085047596615955891 12720891127571394923933837)
              ·
                refine ⟨4770334172839273096475189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12720891127571394923933837 4770334172839273096475189)
                ·
                  refine ⟨447218828703681852794549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4770334172839273096475189 447218828703681852794549)
                  ·
                    rfl

theorem cell23_7838600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 5].length) (baseStart_7838600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838600 prefixEnd_7838600 := by exact prefixLift 7838600
  have htrace : WordTrace (prefixWord ++ tailWord_7838600) baseStart_7838600 baseEnd_7838600 := by
    simpa [prefixWord, tailWord_7838600, baseEnd_7838600] using wordTrace_append hprefix tailTrace_7838600
  have hstable : (prefixWord ++ tailWord_7838600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838600).length < 2 ^ (prefixWord ++ tailWord_7838600).sum := by decide
  have hdescent : baseEnd_7838600 < baseStart_7838600 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838639 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 10]
def baseStart_7838639 : Nat := 118140960795 + 7838639 * 2 ^ 59
def prefixEnd_7838639 : Nat := 4983230072969 + 3 ^ 40 * 7838639 * 2
def baseEnd_7838639 : Nat := 447221053786518002507029

theorem tailTrace_7838639 : CollatzResearch.WordTrace tailWord_7838639 prefixEnd_7838639 447221053786518002507029 := by
  unfold tailWord_7838639
  simp only [CollatzResearch.WordTrace]
  refine ⟨285898651848957110804334971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190599101232638073869556647 285898651848957110804334971)
  ·
    refine ⟨428847977773435666206502457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285898651848957110804334971 428847977773435666206502457)
    ·
      refine ⟨321635983330076749654876843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428847977773435666206502457 321635983330076749654876843)
      ·
        refine ⟨482453974995115124482315265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321635983330076749654876843 482453974995115124482315265)
        ·
          refine ⟨361840481246336343361736449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482453974995115124482315265 361840481246336343361736449)
          ·
            refine ⟨271380360934752257521302337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361840481246336343361736449 271380360934752257521302337)
            ·
              refine ⟨203535270701064193140976753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271380360934752257521302337 203535270701064193140976753)
              ·
                refine ⟨152651453025798144855732565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203535270701064193140976753 152651453025798144855732565)
                ·
                  refine ⟨447221053786518002507029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 152651453025798144855732565 447221053786518002507029)
                  ·
                    rfl

theorem cell23_7838639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 10].length) (baseStart_7838639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838639 prefixEnd_7838639 := by exact prefixLift 7838639
  have htrace : WordTrace (prefixWord ++ tailWord_7838639) baseStart_7838639 baseEnd_7838639 := by
    simpa [prefixWord, tailWord_7838639, baseEnd_7838639] using wordTrace_append hprefix tailTrace_7838639
  have hstable : (prefixWord ++ tailWord_7838639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838639).length < 2 ^ (prefixWord ++ tailWord_7838639).sum := by decide
  have hdescent : baseEnd_7838639 < baseStart_7838639 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838677 : List Nat := [1, 3, 2, 3, 3, 1, 1, 4, 1, 4]
def baseStart_7838677 : Nat := 118140960795 + 7838677 * 2 ^ 59
def prefixEnd_7838677 : Nat := 4983230072969 + 3 ^ 40 * 7838677 * 2
def baseEnd_7838677 : Nat := 1341669665447844291296029

theorem tailTrace_7838677 : CollatzResearch.WordTrace tailWord_7838677 prefixEnd_7838677 1341669665447844291296029 := by
  unfold tailWord_7838677
  simp only [CollatzResearch.WordTrace]
  refine ⟨285900037822819443294218285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190600025215212962196145523 285900037822819443294218285)
  ·
    refine ⟨107212514183557291235331857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285900037822819443294218285 107212514183557291235331857)
    ·
      refine ⟨80409385637667968426498893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107212514183557291235331857 80409385637667968426498893)
      ·
        refine ⟨30153519614125488159937085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80409385637667968426498893 30153519614125488159937085)
        ·
          refine ⟨11307569855297058059976407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30153519614125488159937085 11307569855297058059976407)
          ·
            refine ⟨16961354782945587089964611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11307569855297058059976407 16961354782945587089964611)
            ·
              refine ⟨25442032174418380634946917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16961354782945587089964611 25442032174418380634946917)
              ·
                refine ⟨4770381032703446369052547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25442032174418380634946917 4770381032703446369052547)
                ·
                  refine ⟨7155571549055169553578821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770381032703446369052547 7155571549055169553578821)
                  ·
                    refine ⟨1341669665447844291296029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7155571549055169553578821 1341669665447844291296029)
                    ·
                      rfl

theorem cell23_7838677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_7838677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838677 prefixEnd_7838677 := by exact prefixLift 7838677
  have htrace : WordTrace (prefixWord ++ tailWord_7838677) baseStart_7838677 baseEnd_7838677 := by
    simpa [prefixWord, tailWord_7838677, baseEnd_7838677] using wordTrace_append hprefix tailTrace_7838677
  have hstable : (prefixWord ++ tailWord_7838677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838677).length < 2 ^ (prefixWord ++ tailWord_7838677).sum := by decide
  have hdescent : baseEnd_7838677 < baseStart_7838677 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838690 : List Nat := [3, 3, 3, 1, 1, 1, 2, 3, 6]
def baseStart_7838690 : Nat := 118140960795 + 7838690 * 2 ^ 59
def prefixEnd_7838690 : Nat := 4983230072969 + 3 ^ 40 * 7838690 * 2
def baseEnd_7838690 : Nat := 447223963510226813669503

theorem tailTrace_7838690 : CollatzResearch.WordTrace tailWord_7838690 prefixEnd_7838690 447223963510226813669503 := by
  unfold tailWord_7838690
  simp only [CollatzResearch.WordTrace]
  refine ⟨71475127992943086628610381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190600341314514897676294349 71475127992943086628610381)
  ·
    refine ⟨26803172997353657485728893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71475127992943086628610381 26803172997353657485728893)
    ·
      refine ⟨10051189874007621557148335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26803172997353657485728893 10051189874007621557148335)
      ·
        refine ⟨15076784811011432335722503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10051189874007621557148335 15076784811011432335722503)
        ·
          refine ⟨22615177216517148503583755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15076784811011432335722503 22615177216517148503583755)
          ·
            refine ⟨33922765824775722755375633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22615177216517148503583755 33922765824775722755375633)
            ·
              refine ⟨25442074368581792066531725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33922765824775722755375633 25442074368581792066531725)
              ·
                refine ⟨9540777888218172024949397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25442074368581792066531725 9540777888218172024949397)
                ·
                  refine ⟨447223963510226813669503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9540777888218172024949397 447223963510226813669503)
                  ·
                    rfl

theorem cell23_7838690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 6].length) (baseStart_7838690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838690 prefixEnd_7838690 := by exact prefixLift 7838690
  have htrace : WordTrace (prefixWord ++ tailWord_7838690) baseStart_7838690 baseEnd_7838690 := by
    simpa [prefixWord, tailWord_7838690, baseEnd_7838690] using wordTrace_append hprefix tailTrace_7838690
  have hstable : (prefixWord ++ tailWord_7838690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838690).length < 2 ^ (prefixWord ++ tailWord_7838690).sum := by decide
  have hdescent : baseEnd_7838690 < baseStart_7838690 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838743 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 5]
def baseStart_7838743 : Nat := 118140960795 + 7838743 * 2 ^ 59
def prefixEnd_7838743 : Nat := 4983230072969 + 3 ^ 40 * 7838743 * 2
def baseEnd_7838743 : Nat := 4025042886066729615662783

theorem tailTrace_7838743 : CollatzResearch.WordTrace tailWord_7838743 prefixEnd_7838743 4025042886066729615662783 := by
  unfold tailWord_7838743
  simp only [CollatzResearch.WordTrace]
  refine ⟨285902445040580336566120883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190601630027053557710747255 285902445040580336566120883)
  ·
    refine ⟨428853667560870504849181325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285902445040580336566120883 428853667560870504849181325)
    ·
      refine ⟨160820125335326439318442997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428853667560870504849181325 160820125335326439318442997)
      ·
        refine ⟨15076886750186853686104031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 160820125335326439318442997 15076886750186853686104031)
        ·
          refine ⟨22615330125280280529156047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15076886750186853686104031 22615330125280280529156047)
          ·
            refine ⟨33922995187920420793734071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22615330125280280529156047 33922995187920420793734071)
            ·
              refine ⟨50884492781880631190601107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33922995187920420793734071 50884492781880631190601107)
              ·
                refine ⟨76326739172820946785901661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50884492781880631190601107 76326739172820946785901661)
                ·
                  refine ⟨28622527189807855044713123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76326739172820946785901661 28622527189807855044713123)
                  ·
                    refine ⟨42933790784711782567069685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28622527189807855044713123 42933790784711782567069685)
                    ·
                      refine ⟨4025042886066729615662783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42933790784711782567069685 4025042886066729615662783)
                      ·
                        rfl

theorem cell23_7838743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_7838743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838743 prefixEnd_7838743 := by exact prefixLift 7838743
  have htrace : WordTrace (prefixWord ++ tailWord_7838743) baseStart_7838743 baseEnd_7838743 := by
    simpa [prefixWord, tailWord_7838743, baseEnd_7838743] using wordTrace_append hprefix tailTrace_7838743
  have hstable : (prefixWord ++ tailWord_7838743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838743).length < 2 ^ (prefixWord ++ tailWord_7838743).sum := by decide
  have hdescent : baseEnd_7838743 < baseStart_7838743 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838746 : List Nat := [3, 1, 1, 3, 1, 2, 2, 10]
def baseStart_7838746 : Nat := 118140960795 + 7838746 * 2 ^ 59
def prefixEnd_7838746 : Nat := 4983230072969 + 3 ^ 40 * 7838746 * 2
def baseEnd_7838746 : Nat := 149075719500321966812047

theorem tailTrace_7838746 : CollatzResearch.WordTrace tailWord_7838746 prefixEnd_7838746 149075719500321966812047 := by
  unfold tailWord_7838746
  simp only [CollatzResearch.WordTrace]
  refine ⟨71475638614892367019620023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190601702973046312052320061 71475638614892367019620023)
  ·
    refine ⟨107213457922338550529430035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71475638614892367019620023 107213457922338550529430035)
    ·
      refine ⟨160820186883507825794145053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107213457922338550529430035 160820186883507825794145053)
      ·
        refine ⟨60307570081315434672804395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160820186883507825794145053 60307570081315434672804395)
        ·
          refine ⟨90461355121973152009206593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60307570081315434672804395 90461355121973152009206593)
          ·
            refine ⟨67846016341479864006904945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90461355121973152009206593 67846016341479864006904945)
            ·
              refine ⟨50884512256109898005178709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67846016341479864006904945 50884512256109898005178709)
              ·
                refine ⟨149075719500321966812047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 50884512256109898005178709 149075719500321966812047)
                ·
                  rfl

theorem cell23_7838746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 10].length) (baseStart_7838746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838746 prefixEnd_7838746 := by exact prefixLift 7838746
  have htrace : WordTrace (prefixWord ++ tailWord_7838746) baseStart_7838746 baseEnd_7838746 := by
    simpa [prefixWord, tailWord_7838746, baseEnd_7838746] using wordTrace_append hprefix tailTrace_7838746
  have hstable : (prefixWord ++ tailWord_7838746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838746).length < 2 ^ (prefixWord ++ tailWord_7838746).sum := by decide
  have hdescent : baseEnd_7838746 < baseStart_7838746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838753 : List Nat := [1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 6]
def baseStart_7838753 : Nat := 118140960795 + 7838753 * 2 ^ 59
def prefixEnd_7838753 : Nat := 4983230072969 + 3 ^ 40 * 7838753 * 2
def baseEnd_7838753 : Nat := 4025048020873274576537737

theorem tailTrace_7838753 : CollatzResearch.WordTrace tailWord_7838753 prefixEnd_7838753 4025048020873274576537737 := by
  unfold tailWord_7838753
  simp only [CollatzResearch.WordTrace]
  refine ⟨285902809770544108273984913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190601873180362738849323275 285902809770544108273984913)
  ·
    refine ⟨214427107327908081205488685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285902809770544108273984913 214427107327908081205488685)
    ·
      refine ⟨80410165247965530452058257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214427107327908081205488685 80410165247965530452058257)
      ·
        refine ⟨60307623935974147839043693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80410165247965530452058257 60307623935974147839043693)
        ·
          refine ⟨22615358975990305439641385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60307623935974147839043693 22615358975990305439641385)
          ·
            refine ⟨16961519231992729079731039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22615358975990305439641385 16961519231992729079731039)
            ·
              refine ⟨25442278847989093619596559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16961519231992729079731039 25442278847989093619596559)
              ·
                refine ⟨38163418271983640429394839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25442278847989093619596559 38163418271983640429394839)
                ·
                  refine ⟨57245127407975460644092259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38163418271983640429394839 57245127407975460644092259)
                  ·
                    refine ⟨85867691111963190966138389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57245127407975460644092259 85867691111963190966138389)
                    ·
                      refine ⟨4025048020873274576537737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85867691111963190966138389 4025048020873274576537737)
                      ·
                        rfl

theorem cell23_7838753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_7838753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838753 prefixEnd_7838753 := by exact prefixLift 7838753
  have htrace : WordTrace (prefixWord ++ tailWord_7838753) baseStart_7838753 baseEnd_7838753 := by
    simpa [prefixWord, tailWord_7838753, baseEnd_7838753] using wordTrace_append hprefix tailTrace_7838753
  have hstable : (prefixWord ++ tailWord_7838753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838753).length < 2 ^ (prefixWord ++ tailWord_7838753).sum := by decide
  have hdescent : baseEnd_7838753 < baseStart_7838753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838773 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_7838773 : Nat := 118140960795 + 7838773 * 2 ^ 59
def prefixEnd_7838773 : Nat := 4983230072969 + 3 ^ 40 * 7838773 * 2
def baseEnd_7838773 : Nat := 4025058290486364498287645

theorem tailTrace_7838773 : CollatzResearch.WordTrace tailWord_7838773 prefixEnd_7838773 4025058290486364498287645 := by
  unfold tailWord_7838773
  simp only [CollatzResearch.WordTrace]
  refine ⟨285903539230471651689712973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190602359486981101126475315 285903539230471651689712973)
  ·
    refine ⟨107213827211426869383642365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285903539230471651689712973 107213827211426869383642365)
    ·
      refine ⟨40205185204285076018865887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107213827211426869383642365 40205185204285076018865887)
      ·
        refine ⟨60307777806427614028298831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40205185204285076018865887 60307777806427614028298831)
        ·
          refine ⟨90461666709641421042448247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60307777806427614028298831 90461666709641421042448247)
          ·
            refine ⟨135692500064462131563672371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90461666709641421042448247 135692500064462131563672371)
            ·
              refine ⟨203538750096693197345508557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135692500064462131563672371 203538750096693197345508557)
              ·
                refine ⟨76327031286259949004565709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203538750096693197345508557 76327031286259949004565709)
                ·
                  refine ⟨28622636732347480876712141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76327031286259949004565709 28622636732347480876712141)
                  ·
                    refine ⟨10733488774630305328767053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28622636732347480876712141 10733488774630305328767053)
                    ·
                      refine ⟨4025058290486364498287645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10733488774630305328767053 4025058290486364498287645)
                      ·
                        rfl

theorem cell23_7838773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_7838773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838773 prefixEnd_7838773 := by exact prefixLift 7838773
  have htrace : WordTrace (prefixWord ++ tailWord_7838773) baseStart_7838773 baseEnd_7838773 := by
    simpa [prefixWord, tailWord_7838773, baseEnd_7838773] using wordTrace_append hprefix tailTrace_7838773
  have hstable : (prefixWord ++ tailWord_7838773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838773).length < 2 ^ (prefixWord ++ tailWord_7838773).sum := by decide
  have hdescent : baseEnd_7838773 < baseStart_7838773 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838791 : List Nat := [1, 1, 4, 1, 3, 3, 3, 2, 1, 2, 2]
def baseStart_7838791 : Nat := 118140960795 + 7838791 * 2 ^ 59
def prefixEnd_7838791 : Nat := 4983230072969 + 3 ^ 40 * 7838791 * 2
def baseEnd_7838791 : Nat := 4025067533138145427862563

theorem tailTrace_7838791 : CollatzResearch.WordTrace tailWord_7838791 prefixEnd_7838791 4025067533138145427862563 := by
  unfold tailWord_7838791
  simp only [CollatzResearch.WordTrace]
  refine ⟨285904195744406440763868227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190602797162937627175912151 285904195744406440763868227)
  ·
    refine ⟨428856293616609661145802341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285904195744406440763868227 428856293616609661145802341)
    ·
      refine ⟨80410555053114311464837939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428856293616609661145802341 80410555053114311464837939)
      ·
        refine ⟨120615832579671467197256909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80410555053114311464837939 120615832579671467197256909)
        ·
          refine ⟨45230937217376800198971341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120615832579671467197256909 45230937217376800198971341)
          ·
            refine ⟨16961601456516300074614253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45230937217376800198971341 16961601456516300074614253)
            ·
              refine ⟨6360600546193612527980345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16961601456516300074614253 6360600546193612527980345)
              ·
                refine ⟨4770450409645209395985259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6360600546193612527980345 4770450409645209395985259)
                ·
                  refine ⟨7155675614467814093977889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770450409645209395985259 7155675614467814093977889)
                  ·
                    refine ⟨5366756710850860570483417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7155675614467814093977889 5366756710850860570483417)
                    ·
                      refine ⟨4025067533138145427862563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5366756710850860570483417 4025067533138145427862563)
                      ·
                        rfl

theorem cell23_7838791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 3, 2, 1, 2, 2].length) (baseStart_7838791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838791 prefixEnd_7838791 := by exact prefixLift 7838791
  have htrace : WordTrace (prefixWord ++ tailWord_7838791) baseStart_7838791 baseEnd_7838791 := by
    simpa [prefixWord, tailWord_7838791, baseEnd_7838791] using wordTrace_append hprefix tailTrace_7838791
  have hstable : (prefixWord ++ tailWord_7838791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838791).length < 2 ^ (prefixWord ++ tailWord_7838791).sum := by decide
  have hdescent : baseEnd_7838791 < baseStart_7838791 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838817 : List Nat := [1, 2, 3, 1, 1, 2, 5, 2, 1, 3, 2]
def baseStart_7838817 : Nat := 118140960795 + 7838817 * 2 ^ 59
def prefixEnd_7838817 : Nat := 4983230072969 + 3 ^ 40 * 7838817 * 2
def baseEnd_7838817 : Nat := 4025080883635162326137443

theorem tailTrace_7838817 : CollatzResearch.WordTrace tailWord_7838817 prefixEnd_7838817 4025080883635162326137443 := by
  unfold tailWord_7838817
  simp only [CollatzResearch.WordTrace]
  refine ⟨285905144042312247204314705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190603429361541498136209803 285905144042312247204314705)
  ·
    refine ⟨214428858031734185403236029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285905144042312247204314705 214428858031734185403236029)
    ·
      refine ⟨80410821761900319526213511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214428858031734185403236029 80410821761900319526213511)
      ·
        refine ⟨120616232642850479289320267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80410821761900319526213511 120616232642850479289320267)
        ·
          refine ⟨180924348964275718933980401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120616232642850479289320267 180924348964275718933980401)
          ·
            refine ⟨135693261723206789200485301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180924348964275718933980401 135693261723206789200485301)
            ·
              refine ⟨12721243286550636487545497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135693261723206789200485301 12721243286550636487545497)
              ·
                refine ⟨9540932464912977365659123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12721243286550636487545497 9540932464912977365659123)
                ·
                  refine ⟨14311398697369466048488685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9540932464912977365659123 14311398697369466048488685)
                  ·
                    refine ⟨5366774511513549768183257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14311398697369466048488685 5366774511513549768183257)
                    ·
                      refine ⟨4025080883635162326137443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5366774511513549768183257 4025080883635162326137443)
                      ·
                        rfl

theorem cell23_7838817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_7838817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838817 prefixEnd_7838817 := by exact prefixLift 7838817
  have htrace : WordTrace (prefixWord ++ tailWord_7838817) baseStart_7838817 baseEnd_7838817 := by
    simpa [prefixWord, tailWord_7838817, baseEnd_7838817] using wordTrace_append hprefix tailTrace_7838817
  have hstable : (prefixWord ++ tailWord_7838817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838817).length < 2 ^ (prefixWord ++ tailWord_7838817).sum := by decide
  have hdescent : baseEnd_7838817 < baseStart_7838817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838834 : List Nat := [3, 2, 1, 2, 2, 1, 5, 1, 1, 3, 2]
def baseStart_7838834 : Nat := 118140960795 + 7838834 * 2 ^ 59
def prefixEnd_7838834 : Nat := 4983230072969 + 3 ^ 40 * 7838834 * 2
def baseEnd_7838834 : Nat := 4025089612806288759624865

theorem tailTrace_7838834 : CollatzResearch.WordTrace tailWord_7838834 prefixEnd_7838834 4025089612806288759624865 := by
  unfold tailWord_7838834
  simp only [CollatzResearch.WordTrace]
  refine ⟨71476441020812664776920889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190603842722167106071789037 71476441020812664776920889)
  ·
    refine ⟨53607330765609498582690667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71476441020812664776920889 53607330765609498582690667)
    ·
      refine ⟨80410996148414247874036001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53607330765609498582690667 80410996148414247874036001)
      ·
        refine ⟨60308247111310685905527001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80410996148414247874036001 60308247111310685905527001)
        ·
          refine ⟨45231185333483014429145251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60308247111310685905527001 45231185333483014429145251)
          ·
            refine ⟨67846778000224521643717877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45231185333483014429145251 67846778000224521643717877)
            ·
              refine ⟨6360635437521048904098551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 67846778000224521643717877 6360635437521048904098551)
              ·
                refine ⟨9540953156281573356147827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6360635437521048904098551 9540953156281573356147827)
                ·
                  refine ⟨14311429734422360034221741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9540953156281573356147827 14311429734422360034221741)
                  ·
                    refine ⟨5366786150408385012833153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14311429734422360034221741 5366786150408385012833153)
                    ·
                      refine ⟨4025089612806288759624865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5366786150408385012833153 4025089612806288759624865)
                      ·
                        rfl

theorem cell23_7838834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_7838834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838834 prefixEnd_7838834 := by exact prefixLift 7838834
  have htrace : WordTrace (prefixWord ++ tailWord_7838834) baseStart_7838834 baseEnd_7838834 := by
    simpa [prefixWord, tailWord_7838834, baseEnd_7838834] using wordTrace_append hprefix tailTrace_7838834
  have hstable : (prefixWord ++ tailWord_7838834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838834).length < 2 ^ (prefixWord ++ tailWord_7838834).sum := by decide
  have hdescent : baseEnd_7838834 < baseStart_7838834 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838887 : List Nat := [1, 1, 6, 2, 1, 1, 1, 5, 5]
def baseStart_7838887 : Nat := 118140960795 + 7838887 * 2 ^ 59
def prefixEnd_7838887 : Nat := 4983230072969 + 3 ^ 40 * 7838887 * 2
def baseEnd_7838887 : Nat := 447235203031219672473569

theorem tailTrace_7838887 : CollatzResearch.WordTrace tailWord_7838887 prefixEnd_7838887 447235203031219672473569 := by
  unfold tailWord_7838887
  simp only [CollatzResearch.WordTrace]
  refine ⟨285907697152058649159362915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190605131434705766106241943 285907697152058649159362915)
  ·
    refine ⟨428861545728087973739044373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285907697152058649159362915 428861545728087973739044373)
    ·
      refine ⟨20102884956004123769017705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 428861545728087973739044373 20102884956004123769017705)
      ·
        refine ⟨15077163717003092826763279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20102884956004123769017705 15077163717003092826763279)
        ·
          refine ⟨22615745575504639240144919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15077163717003092826763279 22615745575504639240144919)
          ·
            refine ⟨33923618363256958860217379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22615745575504639240144919 33923618363256958860217379)
            ·
              refine ⟨50885427544885438290326069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33923618363256958860217379 50885427544885438290326069)
              ·
                refine ⟨4770508832333009839718069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50885427544885438290326069 4770508832333009839718069)
                ·
                  refine ⟨447235203031219672473569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4770508832333009839718069 447235203031219672473569)
                  ·
                    rfl

theorem cell23_7838887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 1, 5, 5].length) (baseStart_7838887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838887 prefixEnd_7838887 := by exact prefixLift 7838887
  have htrace : WordTrace (prefixWord ++ tailWord_7838887) baseStart_7838887 baseEnd_7838887 := by
    simpa [prefixWord, tailWord_7838887, baseEnd_7838887] using wordTrace_append hprefix tailTrace_7838887
  have hstable : (prefixWord ++ tailWord_7838887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838887).length < 2 ^ (prefixWord ++ tailWord_7838887).sum := by decide
  have hdescent : baseEnd_7838887 < baseStart_7838887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838943 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 8]
def baseStart_7838943 : Nat := 118140960795 + 7838943 * 2 ^ 59
def prefixEnd_7838943 : Nat := 4983230072969 + 3 ^ 40 * 7838943 * 2
def baseEnd_7838943 : Nat := 447238398021958759240207

theorem tailTrace_7838943 : CollatzResearch.WordTrace tailWord_7838943 prefixEnd_7838943 447238398021958759240207 := by
  unfold tailWord_7838943
  simp only [CollatzResearch.WordTrace]
  refine ⟨285909739639855770723401483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190606493093237180482267655 285909739639855770723401483)
  ·
    refine ⟨428864609459783656085102225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285909739639855770723401483 428864609459783656085102225)
    ·
      refine ⟨321648457094837742063826669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428864609459783656085102225 321648457094837742063826669)
      ·
        refine ⟨120618171410564153273935001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321648457094837742063826669 120618171410564153273935001)
        ·
          refine ⟨90463628557923114955451251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120618171410564153273935001 90463628557923114955451251)
          ·
            refine ⟨135695442836884672433176877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90463628557923114955451251 135695442836884672433176877)
            ·
              refine ⟨50885791063831752162441329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135695442836884672433176877 50885791063831752162441329)
              ·
                refine ⟨38164343297873814121830997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50885791063831752162441329 38164343297873814121830997)
                ·
                  refine ⟨447238398021958759240207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38164343297873814121830997 447238398021958759240207)
                  ·
                    rfl

theorem cell23_7838943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 8].length) (baseStart_7838943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838943 prefixEnd_7838943 := by exact prefixLift 7838943
  have htrace : WordTrace (prefixWord ++ tailWord_7838943) baseStart_7838943 baseEnd_7838943 := by
    simpa [prefixWord, tailWord_7838943, baseEnd_7838943] using wordTrace_append hprefix tailTrace_7838943
  have hstable : (prefixWord ++ tailWord_7838943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838943).length < 2 ^ (prefixWord ++ tailWord_7838943).sum := by decide
  have hdescent : baseEnd_7838943 < baseStart_7838943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838957 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_7838957 : Nat := 118140960795 + 7838957 * 2 ^ 59
def prefixEnd_7838957 : Nat := 4983230072969 + 3 ^ 40 * 7838957 * 2
def baseEnd_7838957 : Nat := 4025152770926791778386799

theorem tailTrace_7838957 : CollatzResearch.WordTrace tailWord_7838957 prefixEnd_7838957 4025152770926791778386799 := by
  unfold tailWord_7838957
  simp only [CollatzResearch.WordTrace]
  refine ⟨285910250261805051114411125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190606833507870034076274083 285910250261805051114411125)
  ·
    refine ⟨26804085962044223541976043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285910250261805051114411125 26804085962044223541976043)
    ·
      refine ⟨40206128943066335312964065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26804085962044223541976043 40206128943066335312964065)
      ·
        refine ⟨30154596707299751484723049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40206128943066335312964065 30154596707299751484723049)
        ·
          refine ⟨22615947530474813613542287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30154596707299751484723049 22615947530474813613542287)
          ·
            refine ⟨33923921295712220420313431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22615947530474813613542287 33923921295712220420313431)
            ·
              refine ⟨50885881943568330630470147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33923921295712220420313431 50885881943568330630470147)
              ·
                refine ⟨76328822915352495945705221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50885881943568330630470147 76328822915352495945705221)
                ·
                  refine ⟨14311654296628592989819729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 76328822915352495945705221 14311654296628592989819729)
                  ·
                    refine ⟨10733740722471444742364797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14311654296628592989819729 10733740722471444742364797)
                    ·
                      refine ⟨4025152770926791778386799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10733740722471444742364797 4025152770926791778386799)
                      ·
                        rfl

theorem cell23_7838957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_7838957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838957 prefixEnd_7838957 := by exact prefixLift 7838957
  have htrace : WordTrace (prefixWord ++ tailWord_7838957) baseStart_7838957 baseEnd_7838957 := by
    simpa [prefixWord, tailWord_7838957, baseEnd_7838957] using wordTrace_append hprefix tailTrace_7838957
  have hstable : (prefixWord ++ tailWord_7838957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838957).length < 2 ^ (prefixWord ++ tailWord_7838957).sum := by decide
  have hdescent : baseEnd_7838957 < baseStart_7838957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838973 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 1, 11]
def baseStart_7838973 : Nat := 118140960795 + 7838973 * 2 ^ 59
def prefixEnd_7838973 : Nat := 4983230072969 + 3 ^ 40 * 7838973 * 2
def baseEnd_7838973 : Nat := 1341720328872421238595575

theorem tailTrace_7838973 : CollatzResearch.WordTrace tailWord_7838973 prefixEnd_7838973 1341720328872421238595575 := by
  unfold tailWord_7838973
  simp only [CollatzResearch.WordTrace]
  refine ⟨285910833829747085846993573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190607222553164723897995715 285910833829747085846993573)
  ·
    refine ⟨53608281343077578596311295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285910833829747085846993573 53608281343077578596311295)
    ·
      refine ⟨80412422014616367894466943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53608281343077578596311295 80412422014616367894466943)
      ·
        refine ⟨120618633021924551841700415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80412422014616367894466943 120618633021924551841700415)
        ·
          refine ⟨180927949532886827762550623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120618633021924551841700415 180927949532886827762550623)
          ·
            refine ⟨271391924299330241643825935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180927949532886827762550623 271391924299330241643825935)
            ·
              refine ⟨407087886448995362465738903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271391924299330241643825935 407087886448995362465738903)
              ·
                refine ⟨610631829673493043698608355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407087886448995362465738903 610631829673493043698608355)
                ·
                  refine ⟨915947744510239565547912533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610631829673493043698608355 915947744510239565547912533)
                  ·
                    refine ⟨1341720328872421238595575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 915947744510239565547912533 1341720328872421238595575)
                    ·
                      rfl

theorem cell23_7838973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_7838973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838973 prefixEnd_7838973 := by exact prefixLift 7838973
  have htrace : WordTrace (prefixWord ++ tailWord_7838973) baseStart_7838973 baseEnd_7838973 := by
    simpa [prefixWord, tailWord_7838973, baseEnd_7838973] using wordTrace_append hprefix tailTrace_7838973
  have hstable : (prefixWord ++ tailWord_7838973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838973).length < 2 ^ (prefixWord ++ tailWord_7838973).sum := by decide
  have hdescent : baseEnd_7838973 < baseStart_7838973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7838977 : List Nat := [1, 2, 4, 1, 1, 3, 4, 1, 6]
def baseStart_7838977 : Nat := 118140960795 + 7838977 * 2 ^ 59
def prefixEnd_7838977 : Nat := 4983230072969 + 3 ^ 40 * 7838977 * 2
def baseEnd_7838977 : Nat := 447240337837764633348523

theorem tailTrace_7838977 : CollatzResearch.WordTrace tailWord_7838977 prefixEnd_7838977 447240337837764633348523 := by
  unfold tailWord_7838977
  simp only [CollatzResearch.WordTrace]
  refine ⟨285910979721732594530139185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190607319814488396353426123 285910979721732594530139185)
  ·
    refine ⟨214433234791299445897604389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285910979721732594530139185 214433234791299445897604389)
    ·
      refine ⟨40206231523368646105800823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214433234791299445897604389 40206231523368646105800823)
      ·
        refine ⟨60309347285052969158701235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40206231523368646105800823 60309347285052969158701235)
        ·
          refine ⟨90464020927579453738051853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60309347285052969158701235 90464020927579453738051853)
          ·
            refine ⟨33924007847842295151769445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90464020927579453738051853 33924007847842295151769445)
            ·
              refine ⟨6360751471470430340956771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33924007847842295151769445 6360751471470430340956771)
              ·
                refine ⟨9541127207205645511435157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6360751471470430340956771 9541127207205645511435157)
                ·
                  refine ⟨447240337837764633348523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9541127207205645511435157 447240337837764633348523)
                  ·
                    rfl

theorem cell23_7838977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 6].length) (baseStart_7838977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7838977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7838977 prefixEnd_7838977 := by exact prefixLift 7838977
  have htrace : WordTrace (prefixWord ++ tailWord_7838977) baseStart_7838977 baseEnd_7838977 := by
    simpa [prefixWord, tailWord_7838977, baseEnd_7838977] using wordTrace_append hprefix tailTrace_7838977
  have hstable : (prefixWord ++ tailWord_7838977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7838977).length < 2 ^ (prefixWord ++ tailWord_7838977).sum := by decide
  have hdescent : baseEnd_7838977 < baseStart_7838977 := by decide
  rcases family_descends (prefixWord ++ tailWord_7838977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839044 : List Nat := [2, 3, 4, 1, 1, 1, 2, 1, 3, 1, 4]
def baseStart_7839044 : Nat := 118140960795 + 7839044 * 2 ^ 59
def prefixEnd_7839044 : Nat := 4983230072969 + 3 ^ 40 * 7839044 * 2
def baseEnd_7839044 : Nat := 4025197443743732937998899

theorem tailTrace_7839044 : CollatzResearch.WordTrace tailWord_7839044 prefixEnd_7839044 4025197443743732937998899 := by
  unfold tailWord_7839044
  simp only [CollatzResearch.WordTrace]
  refine ⟨142956711706244932486414093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190608948941659909981885457 142956711706244932486414093)
  ·
    refine ⟨53608766889841849682405285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142956711706244932486414093 53608766889841849682405285)
    ·
      refine ⟨10051643791845346815450991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53608766889841849682405285 10051643791845346815450991)
      ·
        refine ⟨15077465687768020223176487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10051643791845346815450991 15077465687768020223176487)
        ·
          refine ⟨22616198531652030334764731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15077465687768020223176487 22616198531652030334764731)
          ·
            refine ⟨33924297797478045502147097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22616198531652030334764731 33924297797478045502147097)
            ·
              refine ⟨25443223348108534126610323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33924297797478045502147097 25443223348108534126610323)
              ·
                refine ⟨38164835022162801189915485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25443223348108534126610323 38164835022162801189915485)
                ·
                  refine ⟨14311813133311050446218307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38164835022162801189915485 14311813133311050446218307)
                  ·
                    refine ⟨21467719699966575669327461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14311813133311050446218307 21467719699966575669327461)
                    ·
                      refine ⟨4025197443743732937998899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21467719699966575669327461 4025197443743732937998899)
                      ·
                        rfl

theorem cell23_7839044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_7839044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839044 prefixEnd_7839044 := by exact prefixLift 7839044
  have htrace : WordTrace (prefixWord ++ tailWord_7839044) baseStart_7839044 baseEnd_7839044 := by
    simpa [prefixWord, tailWord_7839044, baseEnd_7839044] using wordTrace_append hprefix tailTrace_7839044
  have hstable : (prefixWord ++ tailWord_7839044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839044).length < 2 ^ (prefixWord ++ tailWord_7839044).sum := by decide
  have hdescent : baseEnd_7839044 < baseStart_7839044 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839047 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 3]
def baseStart_7839047 : Nat := 118140960795 + 7839047 * 2 ^ 59
def prefixEnd_7839047 : Nat := 4983230072969 + 3 ^ 40 * 7839047 * 2
def baseEnd_7839047 : Nat := 4025198984185696426261385

theorem tailTrace_7839047 : CollatzResearch.WordTrace tailWord_7839047 prefixEnd_7839047 4025198984185696426261385 := by
  unfold tailWord_7839047
  simp only [CollatzResearch.WordTrace]
  refine ⟨285913532831478996485187395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190609021887652664323458263 285913532831478996485187395)
  ·
    refine ⟨428870299247218494727781093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285913532831478996485187395 428870299247218494727781093)
    ·
      refine ⟨80413181108853467761458955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428870299247218494727781093 80413181108853467761458955)
      ·
        refine ⟨120619771663280201642188433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80413181108853467761458955 120619771663280201642188433)
        ·
          refine ⟨90464828747460151231641325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120619771663280201642188433 90464828747460151231641325)
          ·
            refine ⟨33924310780297556711865497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90464828747460151231641325 33924310780297556711865497)
            ·
              refine ⟨25443233085223167533899123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33924310780297556711865497 25443233085223167533899123)
              ·
                refine ⟨38164849627834751300848685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25443233085223167533899123 38164849627834751300848685)
                ·
                  refine ⟨14311818610438031737818257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38164849627834751300848685 14311818610438031737818257)
                  ·
                    refine ⟨10733863957828523803363693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14311818610438031737818257 10733863957828523803363693)
                    ·
                      refine ⟨4025198984185696426261385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10733863957828523803363693 4025198984185696426261385)
                      ·
                        rfl

theorem cell23_7839047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2, 3].length) (baseStart_7839047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839047 prefixEnd_7839047 := by exact prefixLift 7839047
  have htrace : WordTrace (prefixWord ++ tailWord_7839047) baseStart_7839047 baseEnd_7839047 := by
    simpa [prefixWord, tailWord_7839047, baseEnd_7839047] using wordTrace_append hprefix tailTrace_7839047
  have hstable : (prefixWord ++ tailWord_7839047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839047).length < 2 ^ (prefixWord ++ tailWord_7839047).sum := by decide
  have hdescent : baseEnd_7839047 < baseStart_7839047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839061 : List Nat := [1, 3, 2, 2, 3, 3, 2, 1, 1, 1, 4]
def baseStart_7839061 : Nat := 118140960795 + 7839061 * 2 ^ 59
def prefixEnd_7839061 : Nat := 4983230072969 + 3 ^ 40 * 7839061 * 2
def baseEnd_7839061 : Nat := 4025206172914859371486321

theorem tailTrace_7839061 : CollatzResearch.WordTrace tailWord_7839061 prefixEnd_7839061 4025206172914859371486321 := by
  unfold tailWord_7839061
  simp only [CollatzResearch.WordTrace]
  refine ⟨285914043453428276876197037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190609362302285517917464691 285914043453428276876197037)
  ·
    refine ⟨107217766295035603828573889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285914043453428276876197037 107217766295035603828573889)
    ·
      refine ⟨80413324721276702871430417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107217766295035603828573889 80413324721276702871430417)
      ·
        refine ⟨60309993540957527153572813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80413324721276702871430417 60309993540957527153572813)
        ·
          refine ⟨22616247577859072682589805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60309993540957527153572813 22616247577859072682589805)
          ·
            refine ⟨8481092841697152255971177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22616247577859072682589805 8481092841697152255971177)
            ·
              refine ⟨6360819631272864191978383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8481092841697152255971177 6360819631272864191978383)
              ·
                refine ⟨9541229446909296287967575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6360819631272864191978383 9541229446909296287967575)
                ·
                  refine ⟨14311844170363944431951363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9541229446909296287967575 14311844170363944431951363)
                  ·
                    refine ⟨21467766255545916647927045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14311844170363944431951363 21467766255545916647927045)
                    ·
                      refine ⟨4025206172914859371486321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21467766255545916647927045 4025206172914859371486321)
                      ·
                        rfl

theorem cell23_7839061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_7839061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839061 prefixEnd_7839061 := by exact prefixLift 7839061
  have htrace : WordTrace (prefixWord ++ tailWord_7839061) baseStart_7839061 baseEnd_7839061 := by
    simpa [prefixWord, tailWord_7839061, baseEnd_7839061] using wordTrace_append hprefix tailTrace_7839061
  have hstable : (prefixWord ++ tailWord_7839061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839061).length < 2 ^ (prefixWord ++ tailWord_7839061).sum := by decide
  have hdescent : baseEnd_7839061 < baseStart_7839061 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839194 : List Nat := [3, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2]
def baseStart_7839194 : Nat := 118140960795 + 7839194 * 2 ^ 59
def prefixEnd_7839194 : Nat := 4983230072969 + 3 ^ 40 * 7839194 * 2
def baseEnd_7839194 : Nat := 4025274465841907351123209

theorem tailTrace_7839194 : CollatzResearch.WordTrace tailWord_7839194 prefixEnd_7839194 4025274465841907351123209 := by
  unfold tailWord_7839194
  simp only [CollatzResearch.WordTrace]
  refine ⟨71479723590486610147697159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190612596241297627060525757 71479723590486610147697159)
  ·
    refine ⟨107219585385729915221545739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71479723590486610147697159 107219585385729915221545739)
    ·
      refine ⟨160829378078594872832318609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107219585385729915221545739 160829378078594872832318609)
      ·
        refine ⟨120622033558946154624238957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160829378078594872832318609 120622033558946154624238957)
        ·
          refine ⟨45233262584604807984089609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120622033558946154624238957 45233262584604807984089609)
          ·
            refine ⟨33924946938453605988067207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45233262584604807984089609 33924946938453605988067207)
            ·
              refine ⟨50887420407680408982100811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33924946938453605988067207 50887420407680408982100811)
              ·
                refine ⟨76331130611520613473151217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50887420407680408982100811 76331130611520613473151217)
                ·
                  refine ⟨57248347958640460104863413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76331130611520613473151217 57248347958640460104863413)
                  ·
                    refine ⟨5367032621122543134830945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 57248347958640460104863413 5367032621122543134830945)
                    ·
                      refine ⟨4025274465841907351123209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5367032621122543134830945 4025274465841907351123209)
                      ·
                        rfl

theorem cell23_7839194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_7839194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839194 prefixEnd_7839194 := by exact prefixLift 7839194
  have htrace : WordTrace (prefixWord ++ tailWord_7839194) baseStart_7839194 baseEnd_7839194 := by
    simpa [prefixWord, tailWord_7839194, baseEnd_7839194] using wordTrace_append hprefix tailTrace_7839194
  have hstable : (prefixWord ++ tailWord_7839194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839194).length < 2 ^ (prefixWord ++ tailWord_7839194).sum := by decide
  have hdescent : baseEnd_7839194 < baseStart_7839194 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839221 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 2, 5]
def baseStart_7839221 : Nat := 118140960795 + 7839221 * 2 ^ 59
def prefixEnd_7839221 : Nat := 4983230072969 + 3 ^ 40 * 7839221 * 2
def baseEnd_7839221 : Nat := 1341762776606526248495195

theorem tailTrace_7839221 : CollatzResearch.WordTrace tailWord_7839221 prefixEnd_7839221 1341762776606526248495195 := by
  unfold tailWord_7839221
  simp only [CollatzResearch.WordTrace]
  refine ⟨285919879132848624202021517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190613252755232416134681011 285919879132848624202021517)
  ·
    refine ⟨107219954674818234075758069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285919879132848624202021517 107219954674818234075758069)
    ·
      refine ⟨10051870750764209444602319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 107219954674818234075758069 10051870750764209444602319)
      ·
        refine ⟨15077806126146314166903479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10051870750764209444602319 15077806126146314166903479)
        ·
          refine ⟨22616709189219471250355219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15077806126146314166903479 22616709189219471250355219)
          ·
            refine ⟨33925063783829206875532829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22616709189219471250355219 33925063783829206875532829)
            ·
              refine ⟨12721898918935952578324811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33925063783829206875532829 12721898918935952578324811)
              ·
                refine ⟨19082848378403928867487217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12721898918935952578324811 19082848378403928867487217)
                ·
                  refine ⟨14312136283802946650615413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19082848378403928867487217 14312136283802946650615413)
                  ·
                    refine ⟨1341762776606526248495195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14312136283802946650615413 1341762776606526248495195)
                    ·
                      rfl

theorem cell23_7839221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_7839221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839221 prefixEnd_7839221 := by exact prefixLift 7839221
  have htrace : WordTrace (prefixWord ++ tailWord_7839221) baseStart_7839221 baseEnd_7839221 := by
    simpa [prefixWord, tailWord_7839221, baseEnd_7839221] using wordTrace_append hprefix tailTrace_7839221
  have hstable : (prefixWord ++ tailWord_7839221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839221).length < 2 ^ (prefixWord ++ tailWord_7839221).sum := by decide
  have hdescent : baseEnd_7839221 < baseStart_7839221 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839224 : List Nat := [2, 1, 2, 1, 1, 5, 3, 1, 2, 1, 4]
def baseStart_7839224 : Nat := 118140960795 + 7839224 * 2 ^ 59
def prefixEnd_7839224 : Nat := 4983230072969 + 3 ^ 40 * 7839224 * 2
def baseEnd_7839224 : Nat := 4025289870261542233748071

theorem tailTrace_7839224 : CollatzResearch.WordTrace tailWord_7839224 prefixEnd_7839224 4025289870261542233748071 := by
  unfold tailWord_7839224
  simp only [CollatzResearch.WordTrace]
  refine ⟨142959994275918877857190363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190613325701225170476253817 142959994275918877857190363)
  ·
    refine ⟨214439991413878316785785545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142959994275918877857190363 214439991413878316785785545)
    ·
      refine ⟨160829993560408737589339159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214439991413878316785785545 160829993560408737589339159)
      ·
        refine ⟨241244990340613106384008739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160829993560408737589339159 241244990340613106384008739)
        ·
          refine ⟨361867485510919659576013109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241244990340613106384008739 361867485510919659576013109)
          ·
            refine ⟨33925076766648718085251229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 361867485510919659576013109 33925076766648718085251229)
            ·
              refine ⟨12721903787493269281969211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33925076766648718085251229 12721903787493269281969211)
              ·
                refine ⟨19082855681239903922953817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12721903787493269281969211 19082855681239903922953817)
                ·
                  refine ⟨14312141760929927942215363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19082855681239903922953817 14312141760929927942215363)
                  ·
                    refine ⟨21468212641394891913323045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14312141760929927942215363 21468212641394891913323045)
                    ·
                      refine ⟨4025289870261542233748071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21468212641394891913323045 4025289870261542233748071)
                      ·
                        rfl

theorem cell23_7839224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3, 1, 2, 1, 4].length) (baseStart_7839224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839224 prefixEnd_7839224 := by exact prefixLift 7839224
  have htrace : WordTrace (prefixWord ++ tailWord_7839224) baseStart_7839224 baseEnd_7839224 := by
    simpa [prefixWord, tailWord_7839224, baseEnd_7839224] using wordTrace_append hprefix tailTrace_7839224
  have hstable : (prefixWord ++ tailWord_7839224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839224).length < 2 ^ (prefixWord ++ tailWord_7839224).sum := by decide
  have hdescent : baseEnd_7839224 < baseStart_7839224 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839227 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 3]
def baseStart_7839227 : Nat := 118140960795 + 7839227 * 2 ^ 59
def prefixEnd_7839227 : Nat := 4983230072969 + 3 ^ 40 * 7839227 * 2
def baseEnd_7839227 : Nat := 4025291410703505722010557

theorem tailTrace_7839227 : CollatzResearch.WordTrace tailWord_7839227 prefixEnd_7839227 4025291410703505722010557 := by
  unfold tailWord_7839227
  simp only [CollatzResearch.WordTrace]
  refine ⟨285920097970826887226739935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190613398647217924817826623 285920097970826887226739935)
  ·
    refine ⟨428880146956240330840109903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285920097970826887226739935 428880146956240330840109903)
    ·
      refine ⟨643320220434360496260164855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428880146956240330840109903 643320220434360496260164855)
      ·
        refine ⟨964980330651540744390247283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643320220434360496260164855 964980330651540744390247283)
        ·
          refine ⟨1447470495977311116585370925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 964980330651540744390247283 1447470495977311116585370925)
          ·
            refine ⟨542801435991491668719514097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1447470495977311116585370925 542801435991491668719514097)
            ·
              refine ⟨407101076993618751539635573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542801435991491668719514097 407101076993618751539635573)
              ·
                refine ⟨38165725968151757956840835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 407101076993618751539635573 38165725968151757956840835)
                ·
                  refine ⟨57248588952227636935261253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38165725968151757956840835 57248588952227636935261253)
                  ·
                    refine ⟨10734110428542681925361485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57248588952227636935261253 10734110428542681925361485)
                    ·
                      refine ⟨4025291410703505722010557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10734110428542681925361485 4025291410703505722010557)
                      ·
                        rfl

theorem cell23_7839227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 3].length) (baseStart_7839227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839227 prefixEnd_7839227 := by exact prefixLift 7839227
  have htrace : WordTrace (prefixWord ++ tailWord_7839227) baseStart_7839227 baseEnd_7839227 := by
    simpa [prefixWord, tailWord_7839227, baseEnd_7839227] using wordTrace_append hprefix tailTrace_7839227
  have hstable : (prefixWord ++ tailWord_7839227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839227).length < 2 ^ (prefixWord ++ tailWord_7839227).sum := by decide
  have hdescent : baseEnd_7839227 < baseStart_7839227 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839251 : List Nat := [1, 1, 1, 2, 1, 6, 2, 4, 1, 4]
def baseStart_7839251 : Nat := 118140960795 + 7839251 * 2 ^ 59
def prefixEnd_7839251 : Nat := 4983230072969 + 3 ^ 40 * 7839251 * 2
def baseEnd_7839251 : Nat := 1341767911413071209370149

theorem tailTrace_7839251 : CollatzResearch.WordTrace tailWord_7839251 prefixEnd_7839251 1341767911413071209370149 := by
  unfold tailWord_7839251
  simp only [CollatzResearch.WordTrace]
  refine ⟨285920973322739939325613607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190613982215159959550409071 285920973322739939325613607)
  ·
    refine ⟨428881459984109908988420411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285920973322739939325613607 428881459984109908988420411)
    ·
      refine ⟨643322189976164863482630617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428881459984109908988420411 643322189976164863482630617)
      ·
        refine ⟨482491642482123647611972963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643322189976164863482630617 482491642482123647611972963)
        ·
          refine ⟨723737463723185471417959445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482491642482123647611972963 723737463723185471417959445)
          ·
            refine ⟨33925193612024318972716849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 723737463723185471417959445 33925193612024318972716849)
            ·
              refine ⟨25443895209018239229537637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33925193612024318972716849 25443895209018239229537637)
              ·
                refine ⟨4770730351690919855538307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25443895209018239229537637 4770730351690919855538307)
                ·
                  refine ⟨7156095527536379783307461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770730351690919855538307 7156095527536379783307461)
                  ·
                    refine ⟨1341767911413071209370149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7156095527536379783307461 1341767911413071209370149)
                    ·
                      rfl

theorem cell23_7839251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 4, 1, 4].length) (baseStart_7839251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839251 prefixEnd_7839251 := by exact prefixLift 7839251
  have htrace : WordTrace (prefixWord ++ tailWord_7839251) baseStart_7839251 baseEnd_7839251 := by
    simpa [prefixWord, tailWord_7839251, baseEnd_7839251] using wordTrace_append hprefix tailTrace_7839251
  have hstable : (prefixWord ++ tailWord_7839251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839251).length < 2 ^ (prefixWord ++ tailWord_7839251).sum := by decide
  have hdescent : baseEnd_7839251 < baseStart_7839251 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839257 : List Nat := [1, 2, 1, 2, 1, 1, 2, 1, 4, 5, 3]
def baseStart_7839257 : Nat := 118140960795 + 7839257 * 2 ^ 59
def prefixEnd_7839257 : Nat := 4983230072969 + 3 ^ 40 * 7839257 * 2
def baseEnd_7839257 : Nat := 4025306815123140604635419

theorem tailTrace_7839257 : CollatzResearch.WordTrace tailWord_7839257 prefixEnd_7839257 4025306815123140604635419 := by
  unfold tailWord_7839257
  simp only [CollatzResearch.WordTrace]
  refine ⟨285921192160718202350332025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190614128107145468233554683 285921192160718202350332025)
  ·
    refine ⟨214440894120538651762749019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285921192160718202350332025 214440894120538651762749019)
    ·
      refine ⟨321661341180807977644123529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214440894120538651762749019 321661341180807977644123529)
      ·
        refine ⟨241246005885605983233092647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321661341180807977644123529 241246005885605983233092647)
        ·
          refine ⟨361869008828408974849638971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241246005885605983233092647 361869008828408974849638971)
          ·
            refine ⟨542803513242613462274458457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361869008828408974849638971 542803513242613462274458457)
            ·
              refine ⟨407102634931960096705843843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542803513242613462274458457 407102634931960096705843843)
              ·
                refine ⟨610653952397940145058765765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407102634931960096705843843 610653952397940145058765765)
                ·
                  refine ⟨114497616074613777198518581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 610653952397940145058765765 114497616074613777198518581)
                  ·
                    refine ⟨10734151506995041612361117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114497616074613777198518581 10734151506995041612361117)
                    ·
                      refine ⟨4025306815123140604635419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10734151506995041612361117 4025306815123140604635419)
                      ·
                        rfl

theorem cell23_7839257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 5, 3].length) (baseStart_7839257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839257 prefixEnd_7839257 := by exact prefixLift 7839257
  have htrace : WordTrace (prefixWord ++ tailWord_7839257) baseStart_7839257 baseEnd_7839257 := by
    simpa [prefixWord, tailWord_7839257, baseEnd_7839257] using wordTrace_append hprefix tailTrace_7839257
  have hstable : (prefixWord ++ tailWord_7839257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839257).length < 2 ^ (prefixWord ++ tailWord_7839257).sum := by decide
  have hdescent : baseEnd_7839257 < baseStart_7839257 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839274 : List Nat := [3, 1, 4, 1, 1, 1, 1, 1, 2, 5, 3]
def baseStart_7839274 : Nat := 118140960795 + 7839274 * 2 ^ 59
def prefixEnd_7839274 : Nat := 4983230072969 + 3 ^ 40 * 7839274 * 2
def baseEnd_7839274 : Nat := 4025315544294267038122841

theorem tailTrace_7839274 : CollatzResearch.WordTrace tailWord_7839274 prefixEnd_7839274 4025315544294267038122841 := by
  unfold tailWord_7839274
  simp only [CollatzResearch.WordTrace]
  refine ⟨71480453050414153563425219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190614541467771076169133917 71480453050414153563425219)
  ·
    refine ⟨107220679575621230345137829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71480453050414153563425219 107220679575621230345137829)
    ·
      refine ⟨20103877420428980689713343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107220679575621230345137829 20103877420428980689713343)
      ·
        refine ⟨30155816130643471034570015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20103877420428980689713343 30155816130643471034570015)
        ·
          refine ⟨45233724195965206551855023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30155816130643471034570015 45233724195965206551855023)
          ·
            refine ⟨67850586293947809827782535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45233724195965206551855023 67850586293947809827782535)
            ·
              refine ⟨101775879440921714741673803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67850586293947809827782535 101775879440921714741673803)
              ·
                refine ⟨152663819161382572112510705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101775879440921714741673803 152663819161382572112510705)
                ·
                  refine ⟨114497864371036929084383029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152663819161382572112510705 114497864371036929084383029)
                  ·
                    refine ⟨10734174784784712101660909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114497864371036929084383029 10734174784784712101660909)
                    ·
                      refine ⟨4025315544294267038122841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10734174784784712101660909 4025315544294267038122841)
                      ·
                        rfl

theorem cell23_7839274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_7839274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839274 prefixEnd_7839274 := by exact prefixLift 7839274
  have htrace : WordTrace (prefixWord ++ tailWord_7839274) baseStart_7839274 baseEnd_7839274 := by
    simpa [prefixWord, tailWord_7839274, baseEnd_7839274] using wordTrace_append hprefix tailTrace_7839274
  have hstable : (prefixWord ++ tailWord_7839274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839274).length < 2 ^ (prefixWord ++ tailWord_7839274).sum := by decide
  have hdescent : baseEnd_7839274 < baseStart_7839274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839301 : List Nat := [1, 3, 1, 1, 1, 4, 3, 2, 2, 3, 2]
def baseStart_7839301 : Nat := 118140960795 + 7839301 * 2 ^ 59
def prefixEnd_7839301 : Nat := 4983230072969 + 3 ^ 40 * 7839301 * 2
def baseEnd_7839301 : Nat := 4025329408271938432485217

theorem tailTrace_7839301 : CollatzResearch.WordTrace tailWord_7839301 prefixEnd_7839301 4025329408271938432485217 := by
  unfold tailWord_7839301
  simp only [CollatzResearch.WordTrace]
  refine ⟨285922796972558797864933757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190615197981705865243289171 285922796972558797864933757)
  ·
    refine ⟨107221048864709549199350159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285922796972558797864933757 107221048864709549199350159)
    ·
      refine ⟨160831573297064323799025239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107221048864709549199350159 160831573297064323799025239)
      ·
        refine ⟨241247359945596485698537859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160831573297064323799025239 241247359945596485698537859)
        ·
          refine ⟨361871039918394728547806789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241247359945596485698537859 361871039918394728547806789)
          ·
            refine ⟨67850819984699011602713773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 361871039918394728547806789 67850819984699011602713773)
            ·
              refine ⟨25444057494262129351017665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67850819984699011602713773 25444057494262129351017665)
              ·
                refine ⟨19083043120696597013263249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25444057494262129351017665 19083043120696597013263249)
                ·
                  refine ⟨14312282340522447759947437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19083043120696597013263249 14312282340522447759947437)
                  ·
                    refine ⟨5367105877695917909980289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14312282340522447759947437 5367105877695917909980289)
                    ·
                      refine ⟨4025329408271938432485217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5367105877695917909980289 4025329408271938432485217)
                      ·
                        rfl

theorem cell23_7839301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 3, 2].length) (baseStart_7839301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839301 prefixEnd_7839301 := by exact prefixLift 7839301
  have htrace : WordTrace (prefixWord ++ tailWord_7839301) baseStart_7839301 baseEnd_7839301 := by
    simpa [prefixWord, tailWord_7839301, baseEnd_7839301] using wordTrace_append hprefix tailTrace_7839301
  have hstable : (prefixWord ++ tailWord_7839301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839301).length < 2 ^ (prefixWord ++ tailWord_7839301).sum := by decide
  have hdescent : baseEnd_7839301 < baseStart_7839301 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839302 : List Nat := [6, 1, 1, 1, 4, 1, 1, 1, 3, 4]
def baseStart_7839302 : Nat := 118140960795 + 7839302 * 2 ^ 59
def prefixEnd_7839302 : Nat := 4983230072969 + 3 ^ 40 * 7839302 * 2
def baseEnd_7839302 : Nat := 1341776640584197642857571

theorem tailTrace_7839302 : CollatzResearch.WordTrace tailWord_7839302 prefixEnd_7839302 1341776640584197642857571 := by
  unfold tailWord_7839302
  simp only [CollatzResearch.WordTrace]
  refine ⟨8935088545173599219866255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 190615222297036783357146773 8935088545173599219866255)
  ·
    refine ⟨13402632817760398829799383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8935088545173599219866255 13402632817760398829799383)
    ·
      refine ⟨20103949226640598244699075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13402632817760398829799383 20103949226640598244699075)
      ·
        refine ⟨30155923839960897367048613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20103949226640598244699075 30155923839960897367048613)
        ·
          refine ⟨5654235719992668256321615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30155923839960897367048613 5654235719992668256321615)
          ·
            refine ⟨8481353579989002384482423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5654235719992668256321615 8481353579989002384482423)
            ·
              refine ⟨12722030369983503576723635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8481353579989002384482423 12722030369983503576723635)
              ·
                refine ⟨19083045554975255365085453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12722030369983503576723635 19083045554975255365085453)
                ·
                  refine ⟨7156142083115720761907045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19083045554975255365085453 7156142083115720761907045)
                  ·
                    refine ⟨1341776640584197642857571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7156142083115720761907045 1341776640584197642857571)
                    ·
                      rfl

theorem cell23_7839302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_7839302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839302 prefixEnd_7839302 := by exact prefixLift 7839302
  have htrace : WordTrace (prefixWord ++ tailWord_7839302) baseStart_7839302 baseEnd_7839302 := by
    simpa [prefixWord, tailWord_7839302, baseEnd_7839302] using wordTrace_append hprefix tailTrace_7839302
  have hstable : (prefixWord ++ tailWord_7839302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839302).length < 2 ^ (prefixWord ++ tailWord_7839302).sum := by decide
  have hdescent : baseEnd_7839302 < baseStart_7839302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839308 : List Nat := [2, 2, 1, 3, 1, 5, 1, 1, 3, 1, 3]
def baseStart_7839308 : Nat := 118140960795 + 7839308 * 2 ^ 59
def prefixEnd_7839308 : Nat := 4983230072969 + 3 ^ 40 * 7839308 * 2
def baseEnd_7839308 : Nat := 4025333002636519905097685

theorem tailTrace_7839308 : CollatzResearch.WordTrace tailWord_7839308 prefixEnd_7839308 4025333002636519905097685 := by
  unfold tailWord_7839308
  simp only [CollatzResearch.WordTrace]
  refine ⟨142961526141766719030219289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190615368189022292040292385 142961526141766719030219289)
  ·
    refine ⟨107221144606325039272664467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142961526141766719030219289 107221144606325039272664467)
    ·
      refine ⟨160831716909487558908996701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107221144606325039272664467 160831716909487558908996701)
      ·
        refine ⟨60311893841057834590873763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160831716909487558908996701 60311893841057834590873763)
        ·
          refine ⟨90467840761586751886310645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60311893841057834590873763 90467840761586751886310645)
          ·
            refine ⟨8481360071398757989341623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90467840761586751886310645 8481360071398757989341623)
            ·
              refine ⟨12722040107098136984012435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8481360071398757989341623 12722040107098136984012435)
              ·
                refine ⟨19083060160647205476018653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12722040107098136984012435 19083060160647205476018653)
                ·
                  refine ⟨7156147560242702053506995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19083060160647205476018653 7156147560242702053506995)
                  ·
                    refine ⟨10734221340364053080260493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7156147560242702053506995 10734221340364053080260493)
                    ·
                      refine ⟨4025333002636519905097685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10734221340364053080260493 4025333002636519905097685)
                      ·
                        rfl

theorem cell23_7839308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_7839308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839308 prefixEnd_7839308 := by exact prefixLift 7839308
  have htrace : WordTrace (prefixWord ++ tailWord_7839308) baseStart_7839308 baseEnd_7839308 := by
    simpa [prefixWord, tailWord_7839308, baseEnd_7839308] using wordTrace_append hprefix tailTrace_7839308
  have hstable : (prefixWord ++ tailWord_7839308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839308).length < 2 ^ (prefixWord ++ tailWord_7839308).sum := by decide
  have hdescent : baseEnd_7839308 < baseStart_7839308 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839331 : List Nat := [1, 1, 1, 5, 1, 3, 3, 2, 1, 1, 4]
def baseStart_7839331 : Nat := 118140960795 + 7839331 * 2 ^ 59
def prefixEnd_7839331 : Nat := 4983230072969 + 3 ^ 40 * 7839331 * 2
def baseEnd_7839331 : Nat := 4025344812691573315110079

theorem tailTrace_7839331 : CollatzResearch.WordTrace tailWord_7839331 prefixEnd_7839331 4025344812691573315110079 := by
  unfold tailWord_7839331
  simp only [CollatzResearch.WordTrace]
  refine ⟨285923891162450112988525847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190615927441633408659017231 285923891162450112988525847)
  ·
    refine ⟨428885836743675169482788771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285923891162450112988525847 428885836743675169482788771)
    ·
      refine ⟨643328755115512754224183157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428885836743675169482788771 643328755115512754224183157)
      ·
        refine ⟨60312070792079320708517171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 643328755115512754224183157 60312070792079320708517171)
        ·
          refine ⟨90468106188118981062775757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60312070792079320708517171 90468106188118981062775757)
          ·
            refine ⟨33925539820544617898540909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90468106188118981062775757 33925539820544617898540909)
            ·
              refine ⟨12722077432704231711952841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33925539820544617898540909 12722077432704231711952841)
              ·
                refine ⟨9541558074528173783964631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12722077432704231711952841 9541558074528173783964631)
                ·
                  refine ⟨14312337111792260675946947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9541558074528173783964631 14312337111792260675946947)
                  ·
                    refine ⟨21468505667688391013920421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14312337111792260675946947 21468505667688391013920421)
                    ·
                      refine ⟨4025344812691573315110079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21468505667688391013920421 4025344812691573315110079)
                      ·
                        rfl

theorem cell23_7839331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 1, 4].length) (baseStart_7839331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839331 prefixEnd_7839331 := by exact prefixLift 7839331
  have htrace : WordTrace (prefixWord ++ tailWord_7839331) baseStart_7839331 baseEnd_7839331 := by
    simpa [prefixWord, tailWord_7839331, baseEnd_7839331] using wordTrace_append hprefix tailTrace_7839331
  have hstable : (prefixWord ++ tailWord_7839331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839331).length < 2 ^ (prefixWord ++ tailWord_7839331).sum := by decide
  have hdescent : baseEnd_7839331 < baseStart_7839331 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839337 : List Nat := [1, 2, 1, 1, 1, 4, 4, 9]
def baseStart_7839337 : Nat := 118140960795 + 7839337 * 2 ^ 59
def prefixEnd_7839337 : Nat := 4983230072969 + 3 ^ 40 * 7839337 * 2
def baseEnd_7839337 : Nat := 149086959021314825616113

theorem tailTrace_7839337 : CollatzResearch.WordTrace tailWord_7839337 prefixEnd_7839337 149086959021314825616113 := by
  unfold tailWord_7839337
  simp only [CollatzResearch.WordTrace]
  refine ⟨285924110000428376013244265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190616073333618917342162843 285924110000428376013244265)
  ·
    refine ⟨214443082500321282009933199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285924110000428376013244265 214443082500321282009933199)
    ·
      refine ⟨321664623750481923014899799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214443082500321282009933199 321664623750481923014899799)
      ·
        refine ⟨482496935625722884522349699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321664623750481923014899799 482496935625722884522349699)
        ·
          refine ⟨723745403438584326783524549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482496935625722884522349699 723745403438584326783524549)
          ·
            refine ⟨135702263144734561271910853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 723745403438584326783524549 135702263144734561271910853)
            ·
              refine ⟨25444174339637730238483285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135702263144734561271910853 25444174339637730238483285)
              ·
                refine ⟨149086959021314825616113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 25444174339637730238483285 149086959021314825616113)
                ·
                  rfl

theorem cell23_7839337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 9].length) (baseStart_7839337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839337 prefixEnd_7839337 := by exact prefixLift 7839337
  have htrace : WordTrace (prefixWord ++ tailWord_7839337) baseStart_7839337 baseEnd_7839337 := by
    simpa [prefixWord, tailWord_7839337, baseEnd_7839337] using wordTrace_append hprefix tailTrace_7839337
  have hstable : (prefixWord ++ tailWord_7839337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839337).length < 2 ^ (prefixWord ++ tailWord_7839337).sum := by decide
  have hdescent : baseEnd_7839337 < baseStart_7839337 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839341 : List Nat := [1, 5, 1, 1, 4, 1, 1, 2, 1, 6]
def baseStart_7839341 : Nat := 118140960795 + 7839341 * 2 ^ 59
def prefixEnd_7839341 : Nat := 4983230072969 + 3 ^ 40 * 7839341 * 2
def baseEnd_7839341 : Nat := 1341783315832706091995011

theorem tailTrace_7839341 : CollatzResearch.WordTrace tailWord_7839341 prefixEnd_7839341 1341783315832706091995011 := by
  unfold tailWord_7839341
  simp only [CollatzResearch.WordTrace]
  refine ⟨285924255892413884696389877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190616170594942589797593251 285924255892413884696389877)
  ·
    refine ⟨26805398989913801690286551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285924255892413884696389877 26805398989913801690286551)
    ·
      refine ⟨40208098484870702535429827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26805398989913801690286551 40208098484870702535429827)
      ·
        refine ⟨60312147727306053803144741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40208098484870702535429827 60312147727306053803144741)
        ·
          refine ⟨11308527698869885088089639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60312147727306053803144741 11308527698869885088089639)
          ·
            refine ⟨16962791548304827632134459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11308527698869885088089639 16962791548304827632134459)
            ·
              refine ⟨25444187322457241448201689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16962791548304827632134459 25444187322457241448201689)
              ·
                refine ⟨19083140491842931086151267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25444187322457241448201689 19083140491842931086151267)
                ·
                  refine ⟨28624710737764396629226901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19083140491842931086151267 28624710737764396629226901)
                  ·
                    refine ⟨1341783315832706091995011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28624710737764396629226901 1341783315832706091995011)
                    ·
                      rfl

theorem cell23_7839341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_7839341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839341 prefixEnd_7839341 := by exact prefixLift 7839341
  have htrace : WordTrace (prefixWord ++ tailWord_7839341) baseStart_7839341 baseEnd_7839341 := by
    simpa [prefixWord, tailWord_7839341, baseEnd_7839341] using wordTrace_append hprefix tailTrace_7839341
  have hstable : (prefixWord ++ tailWord_7839341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839341).length < 2 ^ (prefixWord ++ tailWord_7839341).sum := by decide
  have hdescent : baseEnd_7839341 < baseStart_7839341 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839344 : List Nat := [2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 4]
def baseStart_7839344 : Nat := 118140960795 + 7839344 * 2 ^ 59
def prefixEnd_7839344 : Nat := 4983230072969 + 3 ^ 40 * 7839344 * 2
def baseEnd_7839344 : Nat := 4025351487940081764247519

theorem tailTrace_7839344 : CollatzResearch.WordTrace tailWord_7839344 prefixEnd_7839344 4025351487940081764247519 := by
  unfold tailWord_7839344
  simp only [CollatzResearch.WordTrace]
  refine ⟨142962182655701508104374543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190616243540935344139166057 142962182655701508104374543)
  ·
    refine ⟨214443273983552262156561815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142962182655701508104374543 214443273983552262156561815)
    ·
      refine ⟨321664910975328393234842723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214443273983552262156561815 321664910975328393234842723)
      ·
        refine ⟨482497366462992589852264085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321664910975328393234842723 482497366462992589852264085)
        ·
          refine ⟨22617064052952777649324879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 482497366462992589852264085 22617064052952777649324879)
          ·
            refine ⟨33925596079429166473987319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22617064052952777649324879 33925596079429166473987319)
            ·
              refine ⟨50888394119143749710980979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33925596079429166473987319 50888394119143749710980979)
              ·
                refine ⟨76332591178715624566471469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50888394119143749710980979 76332591178715624566471469)
                ·
                  refine ⟨28624721692018359212426801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76332591178715624566471469 28624721692018359212426801)
                  ·
                    refine ⟨21468541269013769409320101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28624721692018359212426801 21468541269013769409320101)
                    ·
                      refine ⟨4025351487940081764247519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21468541269013769409320101 4025351487940081764247519)
                      ·
                        rfl

theorem cell23_7839344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 1, 3, 2, 4].length) (baseStart_7839344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839344 prefixEnd_7839344 := by exact prefixLift 7839344
  have htrace : WordTrace (prefixWord ++ tailWord_7839344) baseStart_7839344 baseEnd_7839344 := by
    simpa [prefixWord, tailWord_7839344, baseEnd_7839344] using wordTrace_append hprefix tailTrace_7839344
  have hstable : (prefixWord ++ tailWord_7839344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839344).length < 2 ^ (prefixWord ++ tailWord_7839344).sum := by decide
  have hdescent : baseEnd_7839344 < baseStart_7839344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839365 : List Nat := [1, 3, 1, 1, 4, 1, 3, 4, 1, 2, 2]
def baseStart_7839365 : Nat := 118140960795 + 7839365 * 2 ^ 59
def prefixEnd_7839365 : Nat := 4983230072969 + 3 ^ 40 * 7839365 * 2
def baseEnd_7839365 : Nat := 4025362271033826182084923

theorem tailTrace_7839365 : CollatzResearch.WordTrace tailWord_7839365 prefixEnd_7839365 4025362271033826182084923 := by
  unfold tailWord_7839365
  simp only [CollatzResearch.WordTrace]
  refine ⟨285925131244326936795263549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190616754162884624530175699 285925131244326936795263549)
  ·
    refine ⟨107221924216622601298223831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285925131244326936795263549 107221924216622601298223831)
    ·
      refine ⟨160832886324933901947335747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107221924216622601298223831 160832886324933901947335747)
      ·
        refine ⟨241249329487400852921003621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160832886324933901947335747 241249329487400852921003621)
        ·
          refine ⟨45234249278887659922688179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241249329487400852921003621 45234249278887659922688179)
          ·
            refine ⟨67851373918331489884032269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45234249278887659922688179 67851373918331489884032269)
            ·
              refine ⟨25444265219374308706512101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67851373918331489884032269 25444265219374308706512101)
              ·
                refine ⟨4770799728632682882471019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25444265219374308706512101 4770799728632682882471019)
                ·
                  refine ⟨7156199592949024323706529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770799728632682882471019 7156199592949024323706529)
                  ·
                    refine ⟨5367149694711768242779897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7156199592949024323706529 5367149694711768242779897)
                    ·
                      refine ⟨4025362271033826182084923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5367149694711768242779897 4025362271033826182084923)
                      ·
                        rfl

theorem cell23_7839365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 4, 1, 2, 2].length) (baseStart_7839365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839365 prefixEnd_7839365 := by exact prefixLift 7839365
  have htrace : WordTrace (prefixWord ++ tailWord_7839365) baseStart_7839365 baseEnd_7839365 := by
    simpa [prefixWord, tailWord_7839365, baseEnd_7839365] using wordTrace_append hprefix tailTrace_7839365
  have hstable : (prefixWord ++ tailWord_7839365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839365).length < 2 ^ (prefixWord ++ tailWord_7839365).sum := by decide
  have hdescent : baseEnd_7839365 < baseStart_7839365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839378 : List Nat := [3, 2, 3, 1, 3, 1, 2, 1, 1, 2, 4]
def baseStart_7839378 : Nat := 118140960795 + 7839378 * 2 ^ 59
def prefixEnd_7839378 : Nat := 4983230072969 + 3 ^ 40 * 7839378 * 2
def baseEnd_7839378 : Nat := 4025368946282334631222363

theorem tailTrace_7839378 : CollatzResearch.WordTrace tailWord_7839378 prefixEnd_7839378 4025368946282334631222363 := by
  unfold tailWord_7839378
  simp only [CollatzResearch.WordTrace]
  refine ⟨71481401348319960003871697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190617070262186560010324525 71481401348319960003871697)
  ·
    refine ⟨53611051011239970002903773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71481401348319960003871697 53611051011239970002903773)
    ·
      refine ⟨20104144129214988751088915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53611051011239970002903773 20104144129214988751088915)
      ·
        refine ⟨30156216193822483126633373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20104144129214988751088915 30156216193822483126633373)
        ·
          refine ⟨11308581072683431172487515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30156216193822483126633373 11308581072683431172487515)
          ·
            refine ⟨16962871609025146758731273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11308581072683431172487515 16962871609025146758731273)
            ·
              refine ⟨12722153706768860069048455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16962871609025146758731273 12722153706768860069048455)
              ·
                refine ⟨19083230560153290103572683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12722153706768860069048455 19083230560153290103572683)
                ·
                  refine ⟨28624845840229935155359025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19083230560153290103572683 28624845840229935155359025)
                  ·
                    refine ⟨21468634380172451366519269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28624845840229935155359025 21468634380172451366519269)
                    ·
                      refine ⟨4025368946282334631222363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21468634380172451366519269 4025368946282334631222363)
                      ·
                        rfl

theorem cell23_7839378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 1, 1, 2, 4].length) (baseStart_7839378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839378 prefixEnd_7839378 := by exact prefixLift 7839378
  have htrace : WordTrace (prefixWord ++ tailWord_7839378) baseStart_7839378 baseEnd_7839378 := by
    simpa [prefixWord, tailWord_7839378, baseEnd_7839378] using wordTrace_append hprefix tailTrace_7839378
  have hstable : (prefixWord ++ tailWord_7839378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839378).length < 2 ^ (prefixWord ++ tailWord_7839378).sum := by decide
  have hdescent : baseEnd_7839378 < baseStart_7839378 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839415 : List Nat := [1, 1, 3, 1, 5, 3, 1, 2, 2, 1, 3]
def baseStart_7839415 : Nat := 118140960795 + 7839415 * 2 ^ 59
def prefixEnd_7839415 : Nat := 4983230072969 + 3 ^ 40 * 7839415 * 2
def baseEnd_7839415 : Nat := 4025387945066550986459693

theorem tailTrace_7839415 : CollatzResearch.WordTrace tailWord_7839415 prefixEnd_7839415 4025387945066550986459693 := by
  unfold tailWord_7839415
  simp only [CollatzResearch.WordTrace]
  refine ⟨285926954894145795334583699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190617969929430530223055799 285926954894145795334583699)
  ·
    refine ⟨428890432341218693001875549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285926954894145795334583699 428890432341218693001875549)
    ·
      refine ⟨160833912127957009875703331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 428890432341218693001875549 160833912127957009875703331)
      ·
        refine ⟨241250868191935514813554997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160833912127957009875703331 241250868191935514813554997)
        ·
          refine ⟨22617268892993954513770781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 241250868191935514813554997 22617268892993954513770781)
          ·
            refine ⟨8481475834872732942664043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22617268892993954513770781 8481475834872732942664043)
            ·
              refine ⟨12722213752309099413996065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8481475834872732942664043 12722213752309099413996065)
              ·
                refine ⟨9541660314231824560497049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12722213752309099413996065 9541660314231824560497049)
                ·
                  refine ⟨7156245235673868420372787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9541660314231824560497049 7156245235673868420372787)
                  ·
                    refine ⟨10734367853510802630559181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7156245235673868420372787 10734367853510802630559181)
                    ·
                      refine ⟨4025387945066550986459693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10734367853510802630559181 4025387945066550986459693)
                      ·
                        rfl

theorem cell23_7839415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_7839415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839415 prefixEnd_7839415 := by exact prefixLift 7839415
  have htrace : WordTrace (prefixWord ++ tailWord_7839415) baseStart_7839415 baseEnd_7839415 := by
    simpa [prefixWord, tailWord_7839415, baseEnd_7839415] using wordTrace_append hprefix tailTrace_7839415
  have hstable : (prefixWord ++ tailWord_7839415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839415).length < 2 ^ (prefixWord ++ tailWord_7839415).sum := by decide
  have hdescent : baseEnd_7839415 < baseStart_7839415 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839478 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 7]
def baseStart_7839478 : Nat := 118140960795 + 7839478 * 2 ^ 59
def prefixEnd_7839478 : Nat := 4983230072969 + 3 ^ 40 * 7839478 * 2
def baseEnd_7839478 : Nat := 447268921594198248885767

theorem tailTrace_7839478 : CollatzResearch.WordTrace tailWord_7839478 prefixEnd_7839478 447268921594198248885767 := by
  unfold tailWord_7839478
  simp only [CollatzResearch.WordTrace]
  refine ⟨17870578293307347318382943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190619501795278371396084725 17870578293307347318382943)
  ·
    refine ⟨26805867439961020977574415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17870578293307347318382943 26805867439961020977574415)
    ·
      refine ⟨40208801159941531466361623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26805867439961020977574415 40208801159941531466361623)
      ·
        refine ⟨60313201739912297199542435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40208801159941531466361623 60313201739912297199542435)
        ·
          refine ⟨90469802609868445799313653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60313201739912297199542435 90469802609868445799313653)
          ·
            refine ⟨8481543994675166793685655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 90469802609868445799313653 8481543994675166793685655)
            ·
              refine ⟨12722315992012750190528483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8481543994675166793685655 12722315992012750190528483)
              ·
                refine ⟨19083473988019125285792725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12722315992012750190528483 19083473988019125285792725)
                ·
                  refine ⟨447268921594198248885767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19083473988019125285792725 447268921594198248885767)
                  ·
                    rfl

theorem cell23_7839478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 7].length) (baseStart_7839478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839478 prefixEnd_7839478 := by exact prefixLift 7839478
  have htrace : WordTrace (prefixWord ++ tailWord_7839478) baseStart_7839478 baseEnd_7839478 := by
    simpa [prefixWord, tailWord_7839478, baseEnd_7839478] using wordTrace_append hprefix tailTrace_7839478
  have hstable : (prefixWord ++ tailWord_7839478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839478).length < 2 ^ (prefixWord ++ tailWord_7839478).sum := by decide
  have hdescent : baseEnd_7839478 < baseStart_7839478 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839528 : List Nat := [2, 1, 5, 1, 1, 2, 2, 2, 2, 1, 4]
def baseStart_7839528 : Nat := 118140960795 + 7839528 * 2 ^ 59
def prefixEnd_7839528 : Nat := 4983230072969 + 3 ^ 40 * 7839528 * 2
def baseEnd_7839528 : Nat := 4025445968380509044346673

theorem tailTrace_7839528 : CollatzResearch.WordTrace tailWord_7839528 prefixEnd_7839528 4025445968380509044346673 := by
  unfold tailWord_7839528
  simp only [CollatzResearch.WordTrace]
  refine ⟨142965538171368207816723619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190620717561824277088964825 142965538171368207816723619)
  ·
    refine ⟨214448307257052311725085429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142965538171368207816723619 214448307257052311725085429)
    ·
      refine ⟨20104528805348654224226759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214448307257052311725085429 20104528805348654224226759)
      ·
        refine ⟨30156793208022981336340139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20104528805348654224226759 30156793208022981336340139)
        ·
          refine ⟨45235189812034472004510209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30156793208022981336340139 45235189812034472004510209)
          ·
            refine ⟨33926392359025854003382657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45235189812034472004510209 33926392359025854003382657)
            ·
              refine ⟨25444794269269390502536993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33926392359025854003382657 25444794269269390502536993)
              ·
                refine ⟨19083595701952042876902745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25444794269269390502536993 19083595701952042876902745)
                ·
                  refine ⟨14312696776464032157677059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19083595701952042876902745 14312696776464032157677059)
                  ·
                    refine ⟨21469045164696048236515589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14312696776464032157677059 21469045164696048236515589)
                    ·
                      refine ⟨4025445968380509044346673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21469045164696048236515589 4025445968380509044346673)
                      ·
                        rfl

theorem cell23_7839528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 2, 2, 2, 1, 4].length) (baseStart_7839528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839528 prefixEnd_7839528 := by exact prefixLift 7839528
  have htrace : WordTrace (prefixWord ++ tailWord_7839528) baseStart_7839528 baseEnd_7839528 := by
    simpa [prefixWord, tailWord_7839528, baseEnd_7839528] using wordTrace_append hprefix tailTrace_7839528
  have hstable : (prefixWord ++ tailWord_7839528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839528).length < 2 ^ (prefixWord ++ tailWord_7839528).sum := by decide
  have hdescent : baseEnd_7839528 < baseStart_7839528 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839565 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 1, 4, 3]
def baseStart_7839565 : Nat := 118140960795 + 7839565 * 2 ^ 59
def prefixEnd_7839565 : Nat := 4983230072969 + 3 ^ 40 * 7839565 * 2
def baseEnd_7839565 : Nat := 4025464967164725399584003

theorem tailTrace_7839565 : CollatzResearch.WordTrace tailWord_7839565 prefixEnd_7839565 4025464967164725399584003 := by
  unfold tailWord_7839565
  simp only [CollatzResearch.WordTrace]
  refine ⟨285932425843602370952544149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190621617229068247301696099 285932425843602370952544149)
  ·
    refine ⟨13403082461418861138400507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 285932425843602370952544149 13403082461418861138400507)
    ·
      refine ⟨20104623692128291707600761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13403082461418861138400507 20104623692128291707600761)
      ·
        refine ⟨15078467769096218780700571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20104623692128291707600761 15078467769096218780700571)
        ·
          refine ⟨22617701653644328171050857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15078467769096218780700571 22617701653644328171050857)
          ·
            refine ⟨16963276240233246128288143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22617701653644328171050857 16963276240233246128288143)
            ·
              refine ⟨25444914360349869192432215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16963276240233246128288143 25444914360349869192432215)
              ·
                refine ⟨38167371540524803788648323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25444914360349869192432215 38167371540524803788648323)
                ·
                  refine ⟨57251057310787205682972485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38167371540524803788648323 57251057310787205682972485)
                  ·
                    refine ⟨10734573245772601065557341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 57251057310787205682972485 10734573245772601065557341)
                    ·
                      refine ⟨4025464967164725399584003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10734573245772601065557341 4025464967164725399584003)
                      ·
                        rfl

theorem cell23_7839565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_7839565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839565 prefixEnd_7839565 := by exact prefixLift 7839565
  have htrace : WordTrace (prefixWord ++ tailWord_7839565) baseStart_7839565 baseEnd_7839565 := by
    simpa [prefixWord, tailWord_7839565, baseEnd_7839565] using wordTrace_append hprefix tailTrace_7839565
  have hstable : (prefixWord ++ tailWord_7839565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839565).length < 2 ^ (prefixWord ++ tailWord_7839565).sum := by decide
  have hdescent : baseEnd_7839565 < baseStart_7839565 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839572 : List Nat := [2, 4, 1, 1, 3, 2, 2, 3, 1, 4]
def baseStart_7839572 : Nat := 118140960795 + 7839572 * 2 ^ 59
def prefixEnd_7839572 : Nat := 4983230072969 + 3 ^ 40 * 7839572 * 2
def baseEnd_7839572 : Nat := 1341822853843102290732157

theorem tailTrace_7839572 : CollatzResearch.WordTrace tailWord_7839572 prefixEnd_7839572 1341822853843102290732157 := by
  unfold tailWord_7839572
  simp only [CollatzResearch.WordTrace]
  refine ⟨142966340577288505574024485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190621787436384674098699313 142966340577288505574024485)
  ·
    refine ⟨26806188858241594795129591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142966340577288505574024485 26806188858241594795129591)
    ·
      refine ⟨40209283287362392192694387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26806188858241594795129591 40209283287362392192694387)
      ·
        refine ⟨60313924931043588289041581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40209283287362392192694387 60313924931043588289041581)
        ·
          refine ⟨22617721849141345608390593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60313924931043588289041581 22617721849141345608390593)
          ·
            refine ⟨16963291386856009206292945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22617721849141345608390593 16963291386856009206292945)
            ·
              refine ⟨12722468540142006904719709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16963291386856009206292945 12722468540142006904719709)
              ·
                refine ⟨4770925702553252589269891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12722468540142006904719709 4770925702553252589269891)
                ·
                  refine ⟨7156388553829878883904837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4770925702553252589269891 7156388553829878883904837)
                  ·
                    refine ⟨1341822853843102290732157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7156388553829878883904837 1341822853843102290732157)
                    ·
                      rfl

theorem cell23_7839572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 2, 3, 1, 4].length) (baseStart_7839572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839572 prefixEnd_7839572 := by exact prefixLift 7839572
  have htrace : WordTrace (prefixWord ++ tailWord_7839572) baseStart_7839572 baseEnd_7839572 := by
    simpa [prefixWord, tailWord_7839572, baseEnd_7839572] using wordTrace_append hprefix tailTrace_7839572
  have hstable : (prefixWord ++ tailWord_7839572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839572).length < 2 ^ (prefixWord ++ tailWord_7839572).sum := by decide
  have hdescent : baseEnd_7839572 < baseStart_7839572 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839578 : List Nat := [3, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3]
def baseStart_7839578 : Nat := 118140960795 + 7839578 * 2 ^ 59
def prefixEnd_7839578 : Nat := 4983230072969 + 3 ^ 40 * 7839578 * 2
def baseEnd_7839578 : Nat := 4025471642413233848721443

theorem tailTrace_7839578 : CollatzResearch.WordTrace tailWord_7839578 prefixEnd_7839578 4025471642413233848721443 := by
  unfold tailWord_7839578
  simp only [CollatzResearch.WordTrace]
  refine ⟨71483224998138818543191847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190621933328370182781844925 71483224998138818543191847)
  ·
    refine ⟨107224837497208227814787771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71483224998138818543191847 107224837497208227814787771)
    ·
      refine ⟨160837256245812341722181657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107224837497208227814787771 160837256245812341722181657)
      ·
        refine ⟨120627942184359256291636243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160837256245812341722181657 120627942184359256291636243)
        ·
          refine ⟨180941913276538884437454365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120627942184359256291636243 180941913276538884437454365)
          ·
            refine ⟨67853217478702081664045387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180941913276538884437454365 67853217478702081664045387)
            ·
              refine ⟨101779826218053122496068081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67853217478702081664045387 101779826218053122496068081)
              ·
                refine ⟨76334869663539841872051061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101779826218053122496068081 76334869663539841872051061)
                ·
                  refine ⟨7156394030956860175504787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 76334869663539841872051061 7156394030956860175504787)
                  ·
                    refine ⟨10734591046435290263257181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7156394030956860175504787 10734591046435290263257181)
                    ·
                      refine ⟨4025471642413233848721443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10734591046435290263257181 4025471642413233848721443)
                      ·
                        rfl

theorem cell23_7839578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_7839578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839578 prefixEnd_7839578 := by exact prefixLift 7839578
  have htrace : WordTrace (prefixWord ++ tailWord_7839578) baseStart_7839578 baseEnd_7839578 := by
    simpa [prefixWord, tailWord_7839578, baseEnd_7839578] using wordTrace_append hprefix tailTrace_7839578
  have hstable : (prefixWord ++ tailWord_7839578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839578).length < 2 ^ (prefixWord ++ tailWord_7839578).sum := by decide
  have hdescent : baseEnd_7839578 < baseStart_7839578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839621 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 5]
def baseStart_7839621 : Nat := 118140960795 + 7839621 * 2 ^ 59
def prefixEnd_7839621 : Nat := 4983230072969 + 3 ^ 40 * 7839621 * 2
def baseEnd_7839621 : Nat := 4025493722081377180483745

theorem tailTrace_7839621 : CollatzResearch.WordTrace tailWord_7839621 prefixEnd_7839621 4025493722081377180483745 := by
  unfold tailWord_7839621
  simp only [CollatzResearch.WordTrace]
  refine ⟨285934468331399492516582717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190622978887599661677721811 285934468331399492516582717)
  ·
    refine ⟨107225425624274809693718519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285934468331399492516582717 107225425624274809693718519)
    ·
      refine ⟨160838138436412214540577779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107225425624274809693718519 160838138436412214540577779)
      ·
        refine ⟨241257207654618321810866669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160838138436412214540577779 241257207654618321810866669)
        ·
          refine ⟨90471452870481870679075001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241257207654618321810866669 90471452870481870679075001)
          ·
            refine ⟨67853589652861403009306251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90471452870481870679075001 67853589652861403009306251)
            ·
              refine ⟨101780384479292104513959377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67853589652861403009306251 101780384479292104513959377)
              ·
                refine ⟨76335288359469078385469533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101780384479292104513959377 76335288359469078385469533)
                ·
                  refine ⟨28625733134800904394551075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76335288359469078385469533 28625733134800904394551075)
                  ·
                    refine ⟨42938599702201356591826613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28625733134800904394551075 42938599702201356591826613)
                    ·
                      refine ⟨4025493722081377180483745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42938599702201356591826613 4025493722081377180483745)
                      ·
                        rfl

theorem cell23_7839621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 1, 5].length) (baseStart_7839621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839621 prefixEnd_7839621 := by exact prefixLift 7839621
  have htrace : WordTrace (prefixWord ++ tailWord_7839621) baseStart_7839621 baseEnd_7839621 := by
    simpa [prefixWord, tailWord_7839621, baseEnd_7839621] using wordTrace_append hprefix tailTrace_7839621
  have hstable : (prefixWord ++ tailWord_7839621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839621).length < 2 ^ (prefixWord ++ tailWord_7839621).sum := by decide
  have hdescent : baseEnd_7839621 < baseStart_7839621 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839646 : List Nat := [4, 3, 1, 3, 1, 2, 1, 1, 3, 1, 3]
def baseStart_7839646 : Nat := 118140960795 + 7839646 * 2 ^ 59
def prefixEnd_7839646 : Nat := 4983230072969 + 3 ^ 40 * 7839646 * 2
def baseEnd_7839646 : Nat := 4025506559097739582671131

theorem tailTrace_7839646 : CollatzResearch.WordTrace tailWord_7839646 prefixEnd_7839646 4025506559097739582671131 := by
  unfold tailWord_7839646
  simp only [CollatzResearch.WordTrace]
  refine ⟨35741922519538615223280349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190623586770872614524161861 35741922519538615223280349)
  ·
    refine ⟨13403220944826980708730131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35741922519538615223280349 13403220944826980708730131)
    ·
      refine ⟨20104831417240471063095197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13403220944826980708730131 20104831417240471063095197)
      ·
        refine ⟨7539311781465176648660699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20104831417240471063095197 7539311781465176648660699)
        ·
          refine ⟨11308967672197764972991049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7539311781465176648660699 11308967672197764972991049)
          ·
            refine ⟨8481725754148323729743287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11308967672197764972991049 8481725754148323729743287)
            ·
              refine ⟨12722588631222485594614931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8481725754148323729743287 12722588631222485594614931)
              ·
                refine ⟨19083882946833728391922397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12722588631222485594614931 19083882946833728391922397)
                ·
                  refine ⟨7156456105062648146970899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19083882946833728391922397 7156456105062648146970899)
                  ·
                    refine ⟨10734684157593972220456349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7156456105062648146970899 10734684157593972220456349)
                    ·
                      refine ⟨4025506559097739582671131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10734684157593972220456349 4025506559097739582671131)
                      ·
                        rfl

theorem cell23_7839646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_7839646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839646 prefixEnd_7839646 := by exact prefixLift 7839646
  have htrace : WordTrace (prefixWord ++ tailWord_7839646) baseStart_7839646 baseEnd_7839646 := by
    simpa [prefixWord, tailWord_7839646, baseEnd_7839646] using wordTrace_append hprefix tailTrace_7839646
  have hstable : (prefixWord ++ tailWord_7839646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839646).length < 2 ^ (prefixWord ++ tailWord_7839646).sum := by decide
  have hdescent : baseEnd_7839646 < baseStart_7839646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839652 : List Nat := [2, 3, 1, 2, 1, 3, 3, 1, 3, 2, 2]
def baseStart_7839652 : Nat := 118140960795 + 7839652 * 2 ^ 59
def prefixEnd_7839652 : Nat := 4983230072969 + 3 ^ 40 * 7839652 * 2
def baseEnd_7839652 : Nat := 4025509639981666559196103

theorem tailTrace_7839652 : CollatzResearch.WordTrace tailWord_7839652 prefixEnd_7839652 4025509639981666559196103 := by
  unfold tailWord_7839652
  simp only [CollatzResearch.WordTrace]
  refine ⟨142967799497143592405480605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190623732662858123207307473 142967799497143592405480605)
  ·
    refine ⟨53612924811428847152055227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142967799497143592405480605 53612924811428847152055227)
    ·
      refine ⟨80419387217143270728082841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53612924811428847152055227 80419387217143270728082841)
      ·
        refine ⟨60314540412857453046062131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80419387217143270728082841 60314540412857453046062131)
        ·
          refine ⟨90471810619286179569093197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60314540412857453046062131 90471810619286179569093197)
          ·
            refine ⟨33926928982232317338409949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90471810619286179569093197 33926928982232317338409949)
            ·
              refine ⟨12722598368337119001903731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33926928982232317338409949 12722598368337119001903731)
              ·
                refine ⟨19083897552505678502855597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12722598368337119001903731 19083897552505678502855597)
                ·
                  refine ⟨7156461582189629438570849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19083897552505678502855597 7156461582189629438570849)
                  ·
                    refine ⟨5367346186642222078928137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7156461582189629438570849 5367346186642222078928137)
                    ·
                      refine ⟨4025509639981666559196103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5367346186642222078928137 4025509639981666559196103)
                      ·
                        rfl

theorem cell23_7839652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_7839652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839652 prefixEnd_7839652 := by exact prefixLift 7839652
  have htrace : WordTrace (prefixWord ++ tailWord_7839652) baseStart_7839652 baseEnd_7839652 := by
    simpa [prefixWord, tailWord_7839652, baseEnd_7839652] using wordTrace_append hprefix tailTrace_7839652
  have hstable : (prefixWord ++ tailWord_7839652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839652).length < 2 ^ (prefixWord ++ tailWord_7839652).sum := by decide
  have hdescent : baseEnd_7839652 < baseStart_7839652 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839765 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 7]
def baseStart_7839765 : Nat := 118140960795 + 7839765 * 2 ^ 59
def prefixEnd_7839765 : Nat := 4983230072969 + 3 ^ 40 * 7839765 * 2
def baseEnd_7839765 : Nat := 447285295921736068564787

theorem tailTrace_7839765 : CollatzResearch.WordTrace tailWord_7839765 prefixEnd_7839765 447285295921736068564787 := by
  unfold tailWord_7839765
  simp only [CollatzResearch.WordTrace]
  refine ⟨285939720442877805109824749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190626480295251870073216499 285939720442877805109824749)
  ·
    refine ⟨107227395166079176916184281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285939720442877805109824749 107227395166079176916184281)
    ·
      refine ⟨80420546374559382687138211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107227395166079176916184281 80420546374559382687138211)
      ·
        refine ⟨120630819561839074030707317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80420546374559382687138211 120630819561839074030707317)
        ·
          refine ⟨11309139333922413190378811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 120630819561839074030707317 11309139333922413190378811)
          ·
            refine ⟨16963709000883619785568217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11309139333922413190378811 16963709000883619785568217)
            ·
              refine ⟨12722781750662714839176163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16963709000883619785568217 12722781750662714839176163)
              ·
                refine ⟨19084172625994072258764245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12722781750662714839176163 19084172625994072258764245)
                ·
                  refine ⟨447285295921736068564787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19084172625994072258764245 447285295921736068564787)
                  ·
                    rfl

theorem cell23_7839765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 7].length) (baseStart_7839765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839765 prefixEnd_7839765 := by exact prefixLift 7839765
  have htrace : WordTrace (prefixWord ++ tailWord_7839765) baseStart_7839765 baseEnd_7839765 := by
    simpa [prefixWord, tailWord_7839765, baseEnd_7839765] using wordTrace_append hprefix tailTrace_7839765
  have hstable : (prefixWord ++ tailWord_7839765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839765).length < 2 ^ (prefixWord ++ tailWord_7839765).sum := by decide
  have hdescent : baseEnd_7839765 < baseStart_7839765 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839778 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 3, 7]
def baseStart_7839778 : Nat := 118140960795 + 7839778 * 2 ^ 59
def prefixEnd_7839778 : Nat := 4983230072969 + 3 ^ 40 * 7839778 * 2
def baseEnd_7839778 : Nat := 1341858112848044355406841

theorem tailTrace_7839778 : CollatzResearch.WordTrace tailWord_7839778 prefixEnd_7839778 1341858112848044355406841 := by
  unfold tailWord_7839778
  simp only [CollatzResearch.WordTrace]
  refine ⟨71485048647957677082511997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190626796394553805553365325 71485048647957677082511997)
  ·
    refine ⟨26806893242984128905941999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71485048647957677082511997 26806893242984128905941999)
    ·
      refine ⟨40210339864476193358912999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26806893242984128905941999 40210339864476193358912999)
      ·
        refine ⟨60315509796714290038369499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40210339864476193358912999 60315509796714290038369499)
        ·
          refine ⟨90473264695071435057554249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60315509796714290038369499 90473264695071435057554249)
          ·
            refine ⟨67854948521303576293165687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90473264695071435057554249 67854948521303576293165687)
            ·
              refine ⟨101782422781955364439748531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67854948521303576293165687 101782422781955364439748531)
              ·
                refine ⟨152673634172933046659622797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101782422781955364439748531 152673634172933046659622797)
                ·
                  refine ⟨57252612814849892497358549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152673634172933046659622797 57252612814849892497358549)
                  ·
                    refine ⟨1341858112848044355406841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57252612814849892497358549 1341858112848044355406841)
                    ·
                      rfl

theorem cell23_7839778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 3, 7].length) (baseStart_7839778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839778 prefixEnd_7839778 := by exact prefixLift 7839778
  have htrace : WordTrace (prefixWord ++ tailWord_7839778) baseStart_7839778 baseEnd_7839778 := by
    simpa [prefixWord, tailWord_7839778, baseEnd_7839778] using wordTrace_append hprefix tailTrace_7839778
  have hstable : (prefixWord ++ tailWord_7839778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839778).length < 2 ^ (prefixWord ++ tailWord_7839778).sum := by decide
  have hdescent : baseEnd_7839778 < baseStart_7839778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839815 : List Nat := [1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 4]
def baseStart_7839815 : Nat := 118140960795 + 7839815 * 2 ^ 59
def prefixEnd_7839815 : Nat := 4983230072969 + 3 ^ 40 * 7839815 * 2
def baseEnd_7839815 : Nat := 4025593337328349421457853

theorem tailTrace_7839815 : CollatzResearch.WordTrace tailWord_7839815 prefixEnd_7839815 4025593337328349421457853 := by
  unfold tailWord_7839815
  simp only [CollatzResearch.WordTrace]
  refine ⟨285941544092696663649144899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190627696061797775766096599 285941544092696663649144899)
  ·
    refine ⟨428912316139044995473717349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285941544092696663649144899 428912316139044995473717349)
    ·
      refine ⟨80421059276070936651322003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428912316139044995473717349 80421059276070936651322003)
      ·
        refine ⟨120631588914106404976983005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80421059276070936651322003 120631588914106404976983005)
        ·
          refine ⟨45236845842789901866368627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120631588914106404976983005 45236845842789901866368627)
          ·
            refine ⟨67855268764184852799552941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45236845842789901866368627 67855268764184852799552941)
            ·
              refine ⟨25445725786569319799832353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67855268764184852799552941 25445725786569319799832353)
              ·
                refine ⟨19084294339926989849874265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25445725786569319799832353 19084294339926989849874265)
                ·
                  refine ⟨14313220754945242387405699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19084294339926989849874265 14313220754945242387405699)
                  ·
                    refine ⟨21469831132417863581108549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14313220754945242387405699 21469831132417863581108549)
                    ·
                      refine ⟨4025593337328349421457853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21469831132417863581108549 4025593337328349421457853)
                      ·
                        rfl

theorem cell23_7839815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 4].length) (baseStart_7839815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839815 prefixEnd_7839815 := by exact prefixLift 7839815
  have htrace : WordTrace (prefixWord ++ tailWord_7839815) baseStart_7839815 baseEnd_7839815 := by
    simpa [prefixWord, tailWord_7839815, baseEnd_7839815] using wordTrace_append hprefix tailTrace_7839815
  have hstable : (prefixWord ++ tailWord_7839815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839815).length < 2 ^ (prefixWord ++ tailWord_7839815).sum := by decide
  have hdescent : baseEnd_7839815 < baseStart_7839815 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839852 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 3]
def baseStart_7839852 : Nat := 118140960795 + 7839852 * 2 ^ 59
def prefixEnd_7839852 : Nat := 4983230072969 + 3 ^ 40 * 7839852 * 2
def baseEnd_7839852 : Nat := 4025612336112565776695183

theorem tailTrace_7839852 : CollatzResearch.WordTrace tailWord_7839852 prefixEnd_7839852 4025612336112565776695183 := by
  unfold tailWord_7839852
  simp only [CollatzResearch.WordTrace]
  refine ⟨142971446796781309484120905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190628595729041745978827873 142971446796781309484120905)
  ·
    refine ⟨107228585097585982113090679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142971446796781309484120905 107228585097585982113090679)
    ·
      refine ⟨160842877646378973169636019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107228585097585982113090679 160842877646378973169636019)
      ·
        refine ⟨241264316469568459754454029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160842877646378973169636019 241264316469568459754454029)
        ·
          refine ⟨90474118676088172407920261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241264316469568459754454029 90474118676088172407920261)
          ·
            refine ⟨16963897251766532326485049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 90474118676088172407920261 16963897251766532326485049)
            ·
              refine ⟨12722922938824899244863787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16963897251766532326485049 12722922938824899244863787)
              ·
                refine ⟨19084384408237348867295681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12722922938824899244863787 19084384408237348867295681)
                ·
                  refine ⟨14313288306178011650471761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19084384408237348867295681 14313288306178011650471761)
                  ·
                    refine ⟨10734966229633508737853821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14313288306178011650471761 10734966229633508737853821)
                    ·
                      refine ⟨4025612336112565776695183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10734966229633508737853821 4025612336112565776695183)
                      ·
                        rfl

theorem cell23_7839852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 3].length) (baseStart_7839852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839852 prefixEnd_7839852 := by exact prefixLift 7839852
  have htrace : WordTrace (prefixWord ++ tailWord_7839852) baseStart_7839852 baseEnd_7839852 := by
    simpa [prefixWord, tailWord_7839852, baseEnd_7839852] using wordTrace_append hprefix tailTrace_7839852
  have hstable : (prefixWord ++ tailWord_7839852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839852).length < 2 ^ (prefixWord ++ tailWord_7839852).sum := by decide
  have hdescent : baseEnd_7839852 < baseStart_7839852 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839922 : List Nat := [3, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4]
def baseStart_7839922 : Nat := 118140960795 + 7839922 * 2 ^ 59
def prefixEnd_7839922 : Nat := 4983230072969 + 3 ^ 40 * 7839922 * 2
def baseEnd_7839922 : Nat := 4025648279758380502819861

theorem tailTrace_7839922 : CollatzResearch.WordTrace tailWord_7839922 prefixEnd_7839922 4025648279758380502819861 := by
  unfold tailWord_7839922
  simp only [CollatzResearch.WordTrace]
  refine ⟨71486361675827255230822505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190630297802206013948860013 71486361675827255230822505)
  ·
    refine ⟨53614771256870441423116879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71486361675827255230822505 53614771256870441423116879)
    ·
      refine ⟨80422156885305662134675319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53614771256870441423116879 80422156885305662134675319)
      ·
        refine ⟨120633235327958493202012979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80422156885305662134675319 120633235327958493202012979)
        ·
          refine ⟨180949852991937739803019469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120633235327958493202012979 180949852991937739803019469)
          ·
            refine ⟨67856194871976652426132301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180949852991937739803019469 67856194871976652426132301)
            ·
              refine ⟨25446073076991244659799613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67856194871976652426132301 25446073076991244659799613)
              ·
                refine ⟨9542277403871716747424855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25446073076991244659799613 9542277403871716747424855)
                ·
                  refine ⟨14313416105807575121137283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9542277403871716747424855 14313416105807575121137283)
                  ·
                    refine ⟨21470124158711362681705925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14313416105807575121137283 21470124158711362681705925)
                    ·
                      refine ⟨4025648279758380502819861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21470124158711362681705925 4025648279758380502819861)
                      ·
                        rfl

theorem cell23_7839922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 3, 1, 1, 4].length) (baseStart_7839922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839922 prefixEnd_7839922 := by exact prefixLift 7839922
  have htrace : WordTrace (prefixWord ++ tailWord_7839922) baseStart_7839922 baseEnd_7839922 := by
    simpa [prefixWord, tailWord_7839922, baseEnd_7839922] using wordTrace_append hprefix tailTrace_7839922
  have hstable : (prefixWord ++ tailWord_7839922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839922).length < 2 ^ (prefixWord ++ tailWord_7839922).sum := by decide
  have hdescent : baseEnd_7839922 < baseStart_7839922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839928 : List Nat := [2, 1, 2, 1, 2, 1, 14]
def baseStart_7839928 : Nat := 118140960795 + 7839928 * 2 ^ 59
def prefixEnd_7839928 : Nat := 4983230072969 + 3 ^ 40 * 7839928 * 2
def baseEnd_7839928 : Nat := 49699399514102561473393

theorem tailTrace_7839928 : CollatzResearch.WordTrace tailWord_7839928 prefixEnd_7839928 49699399514102561473393 := by
  unfold tailWord_7839928
  simp only [CollatzResearch.WordTrace]
  refine ⟨142972832770643641974004219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190630443694191522632005625 142972832770643641974004219)
  ·
    refine ⟨214459249155965462961006329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142972832770643641974004219 214459249155965462961006329)
    ·
      refine ⟨160844436866974097220754747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214459249155965462961006329 160844436866974097220754747)
      ·
        refine ⟨241266655300461145831132121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160844436866974097220754747 241266655300461145831132121)
        ·
          refine ⟨180949991475345859373349091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241266655300461145831132121 180949991475345859373349091)
          ·
            refine ⟨271424987213018789060023637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180949991475345859373349091 271424987213018789060023637)
            ·
              refine ⟨49699399514102561473393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 271424987213018789060023637 49699399514102561473393)
              ·
                rfl

theorem cell23_7839928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 14].length) (baseStart_7839928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839928 prefixEnd_7839928 := by exact prefixLift 7839928
  have htrace : WordTrace (prefixWord ++ tailWord_7839928) baseStart_7839928 baseEnd_7839928 := by
    simpa [prefixWord, tailWord_7839928, baseEnd_7839928] using wordTrace_append hprefix tailTrace_7839928
  have hstable : (prefixWord ++ tailWord_7839928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839928).length < 2 ^ (prefixWord ++ tailWord_7839928).sum := by decide
  have hdescent : baseEnd_7839928 < baseStart_7839928 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7839973 : List Nat := [1, 3, 1, 4, 2, 1, 3, 3, 1, 2, 2]
def baseStart_7839973 : Nat := 118140960795 + 7839973 * 2 ^ 59
def prefixEnd_7839973 : Nat := 4983230072969 + 3 ^ 40 * 7839973 * 2
def baseEnd_7839973 : Nat := 4025674467271759803282127

theorem tailTrace_7839973 : CollatzResearch.WordTrace tailWord_7839973 prefixEnd_7839973 4025674467271759803282127 := by
  unfold tailWord_7839973
  simp only [CollatzResearch.WordTrace]
  refine ⟨285947306826124256633396573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190631537884082837755597715 285947306826124256633396573)
  ·
    refine ⟨107230240059796596237523715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285947306826124256633396573 107230240059796596237523715)
    ·
      refine ⟨160845360089694894356285573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107230240059796596237523715 160845360089694894356285573)
      ·
        refine ⟨30158505016817792691803545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160845360089694894356285573 30158505016817792691803545)
        ·
          refine ⟨22618878762613344518852659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30158505016817792691803545 22618878762613344518852659)
          ·
            refine ⟨33928318143920016778278989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22618878762613344518852659 33928318143920016778278989)
            ·
              refine ⟨12723119303970006291854621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33928318143920016778278989 12723119303970006291854621)
              ·
                refine ⟨4771169738988752359445483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12723119303970006291854621 4771169738988752359445483)
                ·
                  refine ⟨7156754608483128539168225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4771169738988752359445483 7156754608483128539168225)
                  ·
                    refine ⟨5367565956362346404376169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7156754608483128539168225 5367565956362346404376169)
                    ·
                      refine ⟨4025674467271759803282127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5367565956362346404376169 4025674467271759803282127)
                      ·
                        rfl

theorem cell23_7839973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_7839973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7839973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7839973 prefixEnd_7839973 := by exact prefixLift 7839973
  have htrace : WordTrace (prefixWord ++ tailWord_7839973) baseStart_7839973 baseEnd_7839973 := by
    simpa [prefixWord, tailWord_7839973, baseEnd_7839973] using wordTrace_append hprefix tailTrace_7839973
  have hstable : (prefixWord ++ tailWord_7839973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7839973).length < 2 ^ (prefixWord ++ tailWord_7839973).sum := by decide
  have hdescent : baseEnd_7839973 < baseStart_7839973 := by decide
  rcases family_descends (prefixWord ++ tailWord_7839973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840032 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 5]
def baseStart_7840032 : Nat := 118140960795 + 7840032 * 2 ^ 59
def prefixEnd_7840032 : Nat := 4983230072969 + 3 ^ 40 * 7840032 * 2
def baseEnd_7840032 : Nat := 4025704762630375072444355

theorem tailTrace_7840032 : CollatzResearch.WordTrace tailWord_7840032 prefixEnd_7840032 4025704762630375072444355 := by
  unfold tailWord_7840032
  simp only [CollatzResearch.WordTrace]
  refine ⟨142974729366455254854897175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190632972488607006473196233 142974729366455254854897175)
  ·
    refine ⟨214462094049682882282345763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142974729366455254854897175 214462094049682882282345763)
    ·
      refine ⟨321693141074524323423518645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214462094049682882282345763 321693141074524323423518645)
      ·
        refine ⟨30158731975736655320954873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 321693141074524323423518645 30158731975736655320954873)
        ·
          refine ⟨22619048981802491490716155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30158731975736655320954873 22619048981802491490716155)
          ·
            refine ⟨33928573472703737236074233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22619048981802491490716155 33928573472703737236074233)
            ·
              refine ⟨25446430104527802927055675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33928573472703737236074233 25446430104527802927055675)
              ·
                refine ⟨38169645156791704390583513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25446430104527802927055675 38169645156791704390583513)
                ·
                  refine ⟨28627233867593778292937635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38169645156791704390583513 28627233867593778292937635)
                  ·
                    refine ⟨42940850801390667439406453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28627233867593778292937635 42940850801390667439406453)
                    ·
                      refine ⟨4025704762630375072444355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42940850801390667439406453 4025704762630375072444355)
                      ·
                        rfl

theorem cell23_7840032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_7840032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840032 prefixEnd_7840032 := by exact prefixLift 7840032
  have htrace : WordTrace (prefixWord ++ tailWord_7840032) baseStart_7840032 baseEnd_7840032 := by
    simpa [prefixWord, tailWord_7840032, baseEnd_7840032] using wordTrace_append hprefix tailTrace_7840032
  have hstable : (prefixWord ++ tailWord_7840032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840032).length < 2 ^ (prefixWord ++ tailWord_7840032).sum := by decide
  have hdescent : baseEnd_7840032 < baseStart_7840032 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840075 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 5]
def baseStart_7840075 : Nat := 118140960795 + 7840075 * 2 ^ 59
def prefixEnd_7840075 : Nat := 4983230072969 + 3 ^ 40 * 7840075 * 2
def baseEnd_7840075 : Nat := 4025726842298518404206657

theorem tailTrace_7840075 : CollatzResearch.WordTrace tailWord_7840075 prefixEnd_7840075 4025726842298518404206657 := by
  unfold tailWord_7840075
  simp only [CollatzResearch.WordTrace]
  refine ⟨285951027071754728053609679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190634018047836485369073119 285951027071754728053609679)
  ·
    refine ⟨428926540607632092080414519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285951027071754728053609679 428926540607632092080414519)
    ·
      refine ⟨643389810911448138120621779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428926540607632092080414519 643389810911448138120621779)
      ·
        refine ⟨965084716367172207180932669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643389810911448138120621779 965084716367172207180932669)
        ·
          refine ⟨361906768637689577692849751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 965084716367172207180932669 361906768637689577692849751)
          ·
            refine ⟨542860152956534366539274627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361906768637689577692849751 542860152956534366539274627)
            ·
              refine ⟨814290229434801549808911941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 542860152956534366539274627 814290229434801549808911941)
              ·
                refine ⟨152679418019025290589170989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 814290229434801549808911941 152679418019025290589170989)
                ·
                  refine ⟨57254781757134483970939121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 152679418019025290589170989 57254781757134483970939121)
                  ·
                    refine ⟨42941086317850862978204341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57254781757134483970939121 42941086317850862978204341)
                    ·
                      refine ⟨4025726842298518404206657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42941086317850862978204341 4025726842298518404206657)
                      ·
                        rfl

theorem cell23_7840075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 2, 5].length) (baseStart_7840075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840075 prefixEnd_7840075 := by exact prefixLift 7840075
  have htrace : WordTrace (prefixWord ++ tailWord_7840075) baseStart_7840075 baseEnd_7840075 := by
    simpa [prefixWord, tailWord_7840075, baseEnd_7840075] using wordTrace_append hprefix tailTrace_7840075
  have hstable : (prefixWord ++ tailWord_7840075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840075).length < 2 ^ (prefixWord ++ tailWord_7840075).sum := by decide
  have hdescent : baseEnd_7840075 < baseStart_7840075 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840132 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 2, 4, 4]
def baseStart_7840132 : Nat := 118140960795 + 7840132 * 2 ^ 59
def prefixEnd_7840132 : Nat := 4983230072969 + 3 ^ 40 * 7840132 * 2
def baseEnd_7840132 : Nat := 4025756110695824681193895

theorem tailTrace_7840132 : CollatzResearch.WordTrace tailWord_7840132 prefixEnd_7840132 4025756110695824681193895 := by
  unfold tailWord_7840132
  simp only [CollatzResearch.WordTrace]
  refine ⟨142976553016274113394217325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190635404021698817858956433 142976553016274113394217325)
  ·
    refine ⟨53616207381102792522831497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142976553016274113394217325 53616207381102792522831497)
    ·
      refine ⟨40212155535827094392123623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53616207381102792522831497 40212155535827094392123623)
      ·
        refine ⟨60318233303740641588185435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40212155535827094392123623 60318233303740641588185435)
        ·
          refine ⟨90477349955610962382278153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60318233303740641588185435 90477349955610962382278153)
          ·
            refine ⟨67858012466708221786708615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90477349955610962382278153 67858012466708221786708615)
            ·
              refine ⟨101787018700062332680062923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67858012466708221786708615 101787018700062332680062923)
              ·
                refine ⟨152680528050093499020094385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101787018700062332680062923 152680528050093499020094385)
                ·
                  refine ⟨114510396037570124265070789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152680528050093499020094385 114510396037570124265070789)
                  ·
                    refine ⟨21470699257044398299700773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 114510396037570124265070789 21470699257044398299700773)
                    ·
                      refine ⟨4025756110695824681193895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21470699257044398299700773 4025756110695824681193895)
                      ·
                        rfl

theorem cell23_7840132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_7840132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840132 prefixEnd_7840132 := by exact prefixLift 7840132
  have htrace : WordTrace (prefixWord ++ tailWord_7840132) baseStart_7840132 baseEnd_7840132 := by
    simpa [prefixWord, tailWord_7840132, baseEnd_7840132] using wordTrace_append hprefix tailTrace_7840132
  have hstable : (prefixWord ++ tailWord_7840132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840132).length < 2 ^ (prefixWord ++ tailWord_7840132).sum := by decide
  have hdescent : baseEnd_7840132 < baseStart_7840132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840150 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_7840150 : Nat := 118140960795 + 7840150 * 2 ^ 59
def prefixEnd_7840150 : Nat := 4983230072969 + 3 ^ 40 * 7840150 * 2
def baseEnd_7840150 : Nat := 1341921784449201870256271

theorem tailTrace_7840150 : CollatzResearch.WordTrace tailWord_7840150 prefixEnd_7840150 1341921784449201870256271 := by
  unfold tailWord_7840150
  simp only [CollatzResearch.WordTrace]
  refine ⟨17872110159155188491411869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190635841697655343908393269 17872110159155188491411869)
  ·
    refine ⟨6702041309683195684279451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17872110159155188491411869 6702041309683195684279451)
    ·
      refine ⟨10053061964524793526419177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6702041309683195684279451 10053061964524793526419177)
      ·
        refine ⟨7539796473393595144814383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10053061964524793526419177 7539796473393595144814383)
        ·
          refine ⟨11309694710090392717221575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7539796473393595144814383 11309694710090392717221575)
          ·
            refine ⟨16964542065135589075832363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11309694710090392717221575 16964542065135589075832363)
            ·
              refine ⟨25446813097703383613748545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16964542065135589075832363 25446813097703383613748545)
              ·
                refine ⟨19085109823277537710311409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25446813097703383613748545 19085109823277537710311409)
                ·
                  refine ⟨14313832367458153282733557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19085109823277537710311409 14313832367458153282733557)
                  ·
                    refine ⟨1341921784449201870256271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14313832367458153282733557 1341921784449201870256271)
                    ·
                      rfl

theorem cell23_7840150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_7840150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840150 prefixEnd_7840150 := by exact prefixLift 7840150
  have htrace : WordTrace (prefixWord ++ tailWord_7840150) baseStart_7840150 baseEnd_7840150 := by
    simpa [prefixWord, tailWord_7840150, baseEnd_7840150] using wordTrace_append hprefix tailTrace_7840150
  have hstable : (prefixWord ++ tailWord_7840150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840150).length < 2 ^ (prefixWord ++ tailWord_7840150).sum := by decide
  have hdescent : baseEnd_7840150 < baseStart_7840150 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840163 : List Nat := [1, 1, 1, 4, 1, 5, 3, 2, 1, 4]
def baseStart_7840163 : Nat := 118140960795 + 7840163 * 2 ^ 59
def prefixEnd_7840163 : Nat := 4983230072969 + 3 ^ 40 * 7840163 * 2
def baseEnd_7840163 : Nat := 1341924009532038019968751

theorem tailTrace_7840163 : CollatzResearch.WordTrace tailWord_7840163 prefixEnd_7840163 1341924009532038019968751 := by
  unfold tailWord_7840163
  simp only [CollatzResearch.WordTrace]
  refine ⟨285954236695435919082813143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190636157796957279388542095 285954236695435919082813143)
  ·
    refine ⟨428931355043153878624219715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285954236695435919082813143 428931355043153878624219715)
    ·
      refine ⟨643397032564730817936329573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428931355043153878624219715 643397032564730817936329573)
      ·
        refine ⟨120636943605887028363061795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 643397032564730817936329573 120636943605887028363061795)
        ·
          refine ⟨180955415408830542544592693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120636943605887028363061795 180955415408830542544592693)
          ·
            refine ⟨16964570194577863363555565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 180955415408830542544592693 16964570194577863363555565)
            ·
              refine ⟨6361713822966698761333337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16964570194577863363555565 6361713822966698761333337)
              ·
                refine ⟨4771285367225024071000003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6361713822966698761333337 4771285367225024071000003)
                ·
                  refine ⟨7156928050837536106500005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4771285367225024071000003 7156928050837536106500005)
                  ·
                    refine ⟨1341924009532038019968751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7156928050837536106500005 1341924009532038019968751)
                    ·
                      rfl

theorem cell23_7840163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 1, 4].length) (baseStart_7840163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840163 prefixEnd_7840163 := by exact prefixLift 7840163
  have htrace : WordTrace (prefixWord ++ tailWord_7840163) baseStart_7840163 baseEnd_7840163 := by
    simpa [prefixWord, tailWord_7840163, baseEnd_7840163] using wordTrace_append hprefix tailTrace_7840163
  have hstable : (prefixWord ++ tailWord_7840163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840163).length < 2 ^ (prefixWord ++ tailWord_7840163).sum := by decide
  have hdescent : baseEnd_7840163 < baseStart_7840163 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840172 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 3, 5]
def baseStart_7840172 : Nat := 118140960795 + 7840172 * 2 ^ 59
def prefixEnd_7840172 : Nat := 4983230072969 + 3 ^ 40 * 7840172 * 2
def baseEnd_7840172 : Nat := 1341925549974001508231237

theorem tailTrace_7840172 : CollatzResearch.WordTrace tailWord_7840172 prefixEnd_7840172 1341925549974001508231237 := by
  unfold tailWord_7840172
  simp only [CollatzResearch.WordTrace]
  refine ⟨142977282476201656809945385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190636376634935542413260513 142977282476201656809945385)
  ·
    refine ⟨107232961857151242607459039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142977282476201656809945385 107232961857151242607459039)
    ·
      refine ⟨160849442785726863911188559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107232961857151242607459039 160849442785726863911188559)
      ·
        refine ⟨241274164178590295866782839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160849442785726863911188559 241274164178590295866782839)
        ·
          refine ⟨361911246267885443800174259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241274164178590295866782839 361911246267885443800174259)
          ·
            refine ⟨542866869401828165700261389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361911246267885443800174259 542866869401828165700261389)
            ·
              refine ⟨203575076025685562137598021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 542866869401828165700261389 203575076025685562137598021)
              ·
                refine ⟨38170326754816042900799629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203575076025685562137598021 38170326754816042900799629)
                ·
                  refine ⟨14313872533056016087799861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38170326754816042900799629 14313872533056016087799861)
                  ·
                    refine ⟨1341925549974001508231237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14313872533056016087799861 1341925549974001508231237)
                    ·
                      rfl

theorem cell23_7840172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 5].length) (baseStart_7840172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840172 prefixEnd_7840172 := by exact prefixLift 7840172
  have htrace : WordTrace (prefixWord ++ tailWord_7840172) baseStart_7840172 baseEnd_7840172 := by
    simpa [prefixWord, tailWord_7840172, baseEnd_7840172] using wordTrace_append hprefix tailTrace_7840172
  have hstable : (prefixWord ++ tailWord_7840172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840172).length < 2 ^ (prefixWord ++ tailWord_7840172).sum := by decide
  have hdescent : baseEnd_7840172 < baseStart_7840172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840189 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 3, 5]
def baseStart_7840189 : Nat := 118140960795 + 7840189 * 2 ^ 59
def prefixEnd_7840189 : Nat := 4983230072969 + 3 ^ 40 * 7840189 * 2
def baseEnd_7840189 : Nat := 1341928459697710319393711

theorem tailTrace_7840189 : CollatzResearch.WordTrace tailWord_7840189 prefixEnd_7840189 1341928459697710319393711 := by
  unfold tailWord_7840189
  simp only [CollatzResearch.WordTrace]
  refine ⟨285955184993341725523259621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190636789995561150348839747 285955184993341725523259621)
  ·
    refine ⟨53616597186251573535611179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285955184993341725523259621 53616597186251573535611179)
    ·
      refine ⟨80424895779377360303416769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53616597186251573535611179 80424895779377360303416769)
      ·
        refine ⟨60318671834533020227562577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80424895779377360303416769 60318671834533020227562577)
        ·
          refine ⟨45239003875899765170671933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60318671834533020227562577 45239003875899765170671933)
          ·
            refine ⟨16964626453462411939001975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45239003875899765170671933 16964626453462411939001975)
            ·
              refine ⟨25446939680193617908502963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16964626453462411939001975 25446939680193617908502963)
              ·
                refine ⟨38170409520290426862754445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25446939680193617908502963 38170409520290426862754445)
                ·
                  refine ⟨14313903570108910073532917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38170409520290426862754445 14313903570108910073532917)
                  ·
                    refine ⟨1341928459697710319393711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14313903570108910073532917 1341928459697710319393711)
                    ·
                      rfl

theorem cell23_7840189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_7840189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840189 prefixEnd_7840189 := by exact prefixLift 7840189
  have htrace : WordTrace (prefixWord ++ tailWord_7840189) baseStart_7840189 baseEnd_7840189 := by
    simpa [prefixWord, tailWord_7840189, baseEnd_7840189] using wordTrace_append hprefix tailTrace_7840189
  have hstable : (prefixWord ++ tailWord_7840189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840189).length < 2 ^ (prefixWord ++ tailWord_7840189).sum := by decide
  have hdescent : baseEnd_7840189 < baseStart_7840189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840209 : List Nat := [1, 2, 2, 1, 2, 1, 1, 7, 1, 1, 4]
def baseStart_7840209 : Nat := 118140960795 + 7840209 * 2 ^ 59
def prefixEnd_7840209 : Nat := 4983230072969 + 3 ^ 40 * 7840209 * 2
def baseEnd_7840209 : Nat := 4025795648706220879931041

theorem tailTrace_7840209 : CollatzResearch.WordTrace tailWord_7840209 prefixEnd_7840209 4025795648706220879931041 := by
  unfold tailWord_7840209
  simp only [CollatzResearch.WordTrace]
  refine ⟨285955914453269268938987681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190637276302179512625991787 285955914453269268938987681)
  ·
    refine ⟨214466935839951951704240761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285955914453269268938987681 214466935839951951704240761)
    ·
      refine ⟨160850201879963963778180571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214466935839951951704240761 160850201879963963778180571)
      ·
        refine ⟨241275302819945945667270857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160850201879963963778180571 241275302819945945667270857)
        ·
          refine ⟨180956477114959459250453143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241275302819945945667270857 180956477114959459250453143)
          ·
            refine ⟨271434715672439188875679715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180956477114959459250453143 271434715672439188875679715)
            ·
              refine ⟨407152073508658783313519573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271434715672439188875679715 407152073508658783313519573)
              ·
                refine ⟨9542626722859190233910615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 407152073508658783313519573 9542626722859190233910615)
                ·
                  refine ⟨14313940084288785350865923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9542626722859190233910615 14313940084288785350865923)
                  ·
                    refine ⟨21470910126433178026298885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14313940084288785350865923 21470910126433178026298885)
                    ·
                      refine ⟨4025795648706220879931041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21470910126433178026298885 4025795648706220879931041)
                      ·
                        rfl

theorem cell23_7840209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_7840209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840209 prefixEnd_7840209 := by exact prefixLift 7840209
  have htrace : WordTrace (prefixWord ++ tailWord_7840209) baseStart_7840209 baseEnd_7840209 := by
    simpa [prefixWord, tailWord_7840209, baseEnd_7840209] using wordTrace_append hprefix tailTrace_7840209
  have hstable : (prefixWord ++ tailWord_7840209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840209).length < 2 ^ (prefixWord ++ tailWord_7840209).sum := by decide
  have hdescent : baseEnd_7840209 < baseStart_7840209 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840246 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3]
def baseStart_7840246 : Nat := 118140960795 + 7840246 * 2 ^ 59
def prefixEnd_7840246 : Nat := 4983230072969 + 3 ^ 40 * 7840246 * 2
def baseEnd_7840246 : Nat := 4025814647490437235168371

theorem tailTrace_7840246 : CollatzResearch.WordTrace tailWord_7840246 prefixEnd_7840246 4025814647490437235168371 := by
  unfold tailWord_7840246
  simp only [CollatzResearch.WordTrace]
  refine ⟨17872328997133451516130287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190638175969423482838723061 17872328997133451516130287)
  ·
    refine ⟨26808493495700177274195431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17872328997133451516130287 26808493495700177274195431)
    ·
      refine ⟨40212740243550265911293147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26808493495700177274195431 40212740243550265911293147)
      ·
        refine ⟨60319110365325398866939721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40212740243550265911293147 60319110365325398866939721)
        ·
          refine ⟨45239332773994049150204791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60319110365325398866939721 45239332773994049150204791)
          ·
            refine ⟨67858999160991073725307187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45239332773994049150204791 67858999160991073725307187)
            ·
              refine ⟨101788498741486610587960781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67858999160991073725307187 101788498741486610587960781)
              ·
                refine ⟨38170687028057478970485293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101788498741486610587960781 38170687028057478970485293)
                ·
                  refine ⟨14314007635521554613931985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38170687028057478970485293 14314007635521554613931985)
                  ·
                    refine ⟨10735505726641165960448989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14314007635521554613931985 10735505726641165960448989)
                    ·
                      refine ⟨4025814647490437235168371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10735505726641165960448989 4025814647490437235168371)
                      ·
                        rfl

theorem cell23_7840246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_7840246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840246 prefixEnd_7840246 := by exact prefixLift 7840246
  have htrace : WordTrace (prefixWord ++ tailWord_7840246) baseStart_7840246 baseEnd_7840246 := by
    simpa [prefixWord, tailWord_7840246, baseEnd_7840246] using wordTrace_append hprefix tailTrace_7840246
  have hstable : (prefixWord ++ tailWord_7840246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840246).length < 2 ^ (prefixWord ++ tailWord_7840246).sum := by decide
  have hdescent : baseEnd_7840246 < baseStart_7840246 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840259 : List Nat := [1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 3]
def baseStart_7840259 : Nat := 118140960795 + 7840259 * 2 ^ 59
def prefixEnd_7840259 : Nat := 4983230072969 + 3 ^ 40 * 7840259 * 2
def baseEnd_7840259 : Nat := 4025821322738945684305811

theorem tailTrace_7840259 : CollatzResearch.WordTrace tailWord_7840259 prefixEnd_7840259 4025821322738945684305811 := by
  unfold tailWord_7840259
  simp only [CollatzResearch.WordTrace]
  refine ⟨285957738103088127478307831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190638492068725418318871887 285957738103088127478307831)
  ·
    refine ⟨428936607154632191217461747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285957738103088127478307831 428936607154632191217461747)
    ·
      refine ⟨643404910731948286826192621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428936607154632191217461747 643404910731948286826192621)
      ·
        refine ⟨241276841524480607559822233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 643404910731948286826192621 241276841524480607559822233)
        ·
          refine ⟨180957631143360455669866675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241276841524480607559822233 180957631143360455669866675)
          ·
            refine ⟨271436446715040683504800013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180957631143360455669866675 271436446715040683504800013)
            ·
              refine ⟨101788667518140256314300005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 271436446715040683504800013 101788667518140256314300005)
              ·
                refine ⟨19085375159651298058931251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101788667518140256314300005 19085375159651298058931251)
                ·
                  refine ⟨28628062739476947088396877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19085375159651298058931251 28628062739476947088396877)
                  ·
                    refine ⟨10735523527303855158148829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28628062739476947088396877 10735523527303855158148829)
                    ·
                      refine ⟨4025821322738945684305811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10735523527303855158148829 4025821322738945684305811)
                      ·
                        rfl

theorem cell23_7840259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 3, 4, 1, 3, 3].length) (baseStart_7840259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840259 prefixEnd_7840259 := by exact prefixLift 7840259
  have htrace : WordTrace (prefixWord ++ tailWord_7840259) baseStart_7840259 baseEnd_7840259 := by
    simpa [prefixWord, tailWord_7840259, baseEnd_7840259] using wordTrace_append hprefix tailTrace_7840259
  have hstable : (prefixWord ++ tailWord_7840259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840259).length < 2 ^ (prefixWord ++ tailWord_7840259).sum := by decide
  have hdescent : baseEnd_7840259 < baseStart_7840259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840260 : List Nat := [2, 3, 2, 3, 1, 3, 2, 1, 1, 1, 4]
def baseStart_7840260 : Nat := 118140960795 + 7840260 * 2 ^ 59
def prefixEnd_7840260 : Nat := 4983230072969 + 3 ^ 40 * 7840260 * 2
def baseEnd_7840260 : Nat := 4025821836219600180393307

theorem tailTrace_7840260 : CollatzResearch.WordTrace tailWord_7840260 prefixEnd_7840260 4025821836219600180393307 := by
  unfold tailWord_7840260
  simp only [CollatzResearch.WordTrace]
  refine ⟨142978887288042252324547117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190638516384056336432729489 142978887288042252324547117)
  ·
    refine ⟨53617082733015844621705169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142978887288042252324547117 53617082733015844621705169)
    ·
      refine ⟨40212812049761883466278877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53617082733015844621705169 40212812049761883466278877)
      ·
        refine ⟨15079804518660706299854579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40212812049761883466278877 15079804518660706299854579)
        ·
          refine ⟨22619706777991059449781869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15079804518660706299854579 22619706777991059449781869)
          ·
            refine ⟨8482390041746647293668201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22619706777991059449781869 8482390041746647293668201)
            ·
              refine ⟨6361792531309985470251151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8482390041746647293668201 6361792531309985470251151)
              ·
                refine ⟨9542688796964978205376727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6361792531309985470251151 9542688796964978205376727)
                ·
                  refine ⟨14314033195447467308065091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9542688796964978205376727 14314033195447467308065091)
                  ·
                    refine ⟨21471049793171200962097637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14314033195447467308065091 21471049793171200962097637)
                    ·
                      refine ⟨4025821836219600180393307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21471049793171200962097637 4025821836219600180393307)
                      ·
                        rfl

theorem cell23_7840260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_7840260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840260 prefixEnd_7840260 := by exact prefixLift 7840260
  have htrace : WordTrace (prefixWord ++ tailWord_7840260) baseStart_7840260 baseEnd_7840260 := by
    simpa [prefixWord, tailWord_7840260, baseEnd_7840260] using wordTrace_append hprefix tailTrace_7840260
  have hstable : (prefixWord ++ tailWord_7840260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840260).length < 2 ^ (prefixWord ++ tailWord_7840260).sum := by decide
  have hdescent : baseEnd_7840260 < baseStart_7840260 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840263 : List Nat := [1, 1, 4, 3, 3, 1, 1, 3, 1, 2, 3]
def baseStart_7840263 : Nat := 118140960795 + 7840263 * 2 ^ 59
def prefixEnd_7840263 : Nat := 4983230072969 + 3 ^ 40 * 7840263 * 2
def baseEnd_7840263 : Nat := 4025823376661563668655793

theorem tailTrace_7840263 : CollatzResearch.WordTrace tailWord_7840263 prefixEnd_7840263 4025823376661563668655793 := by
  unfold tailWord_7840263
  simp only [CollatzResearch.WordTrace]
  refine ⟨285957883995073636161453443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190638589330049090774302295 285957883995073636161453443)
  ·
    refine ⟨428936825992610454242180165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285957883995073636161453443 428936825992610454242180165)
    ·
      refine ⟨80425654873614460170408781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428936825992610454242180165 80425654873614460170408781)
      ·
        refine ⟨30159620577605422563903293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 80425654873614460170408781 30159620577605422563903293)
        ·
          refine ⟨11309857716602033461463735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30159620577605422563903293 11309857716602033461463735)
          ·
            refine ⟨16964786574903050192195603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11309857716602033461463735 16964786574903050192195603)
            ·
              refine ⟨25447179862354575288293405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16964786574903050192195603 25447179862354575288293405)
              ·
                refine ⟨9542692448382965733110027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25447179862354575288293405 9542692448382965733110027)
                ·
                  refine ⟨14314038672574448599665041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9542692448382965733110027 14314038672574448599665041)
                  ·
                    refine ⟨10735529004430836449748781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14314038672574448599665041 10735529004430836449748781)
                    ·
                      refine ⟨4025823376661563668655793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10735529004430836449748781 4025823376661563668655793)
                      ·
                        rfl

theorem cell23_7840263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 1, 2, 3].length) (baseStart_7840263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840263 prefixEnd_7840263 := by exact prefixLift 7840263
  have htrace : WordTrace (prefixWord ++ tailWord_7840263) baseStart_7840263 baseEnd_7840263 := by
    simpa [prefixWord, tailWord_7840263, baseEnd_7840263] using wordTrace_append hprefix tailTrace_7840263
  have hstable : (prefixWord ++ tailWord_7840263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840263).length < 2 ^ (prefixWord ++ tailWord_7840263).sum := by decide
  have hdescent : baseEnd_7840263 < baseStart_7840263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840319 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 5]
def baseStart_7840319 : Nat := 118140960795 + 7840319 * 2 ^ 59
def prefixEnd_7840319 : Nat := 4983230072969 + 3 ^ 40 * 7840319 * 2
def baseEnd_7840319 : Nat := 4025852131578215449555535

theorem tailTrace_7840319 : CollatzResearch.WordTrace tailWord_7840319 prefixEnd_7840319 4025852131578215449555535 := by
  unfold tailWord_7840319
  simp only [CollatzResearch.WordTrace]
  refine ⟨285959926482870757725492011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190639950988580505150328007 285959926482870757725492011)
  ·
    refine ⟨428939889724306136588238017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285959926482870757725492011 428939889724306136588238017)
    ·
      refine ⟨321704917293229602441178513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428939889724306136588238017 321704917293229602441178513)
      ·
        refine ⟨241278687969922201830883885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321704917293229602441178513 241278687969922201830883885)
        ·
          refine ⟨90479507988720825686581457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241278687969922201830883885 90479507988720825686581457)
          ·
            refine ⟨67859630991540619264936093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90479507988720825686581457 67859630991540619264936093)
            ·
              refine ⟨25447361621827732224351035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67859630991540619264936093 25447361621827732224351035)
              ·
                refine ⟨38171042432741598336526553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25447361621827732224351035 38171042432741598336526553)
                ·
                  refine ⟨28628281824556198752394915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38171042432741598336526553 28628281824556198752394915)
                  ·
                    refine ⟨42942422736834298128592373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28628281824556198752394915 42942422736834298128592373)
                    ·
                      refine ⟨4025852131578215449555535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42942422736834298128592373 4025852131578215449555535)
                      ·
                        rfl

theorem cell23_7840319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_7840319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840319 prefixEnd_7840319 := by exact prefixLift 7840319
  have htrace : WordTrace (prefixWord ++ tailWord_7840319) baseStart_7840319 baseEnd_7840319 := by
    simpa [prefixWord, tailWord_7840319, baseEnd_7840319] using wordTrace_append hprefix tailTrace_7840319
  have hstable : (prefixWord ++ tailWord_7840319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840319).length < 2 ^ (prefixWord ++ tailWord_7840319).sum := by decide
  have hdescent : baseEnd_7840319 < baseStart_7840319 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840354 : List Nat := [3, 3, 2, 3, 1, 2, 1, 2, 1, 3, 2]
def baseStart_7840354 : Nat := 118140960795 + 7840354 * 2 ^ 59
def prefixEnd_7840354 : Nat := 4983230072969 + 3 ^ 40 * 7840354 * 2
def baseEnd_7840354 : Nat := 4025870103401122812617875

theorem tailTrace_7840354 : CollatzResearch.WordTrace tailWord_7840354 prefixEnd_7840354 4025870103401122812617875 := by
  unfold tailWord_7840354
  simp only [CollatzResearch.WordTrace]
  refine ⟨71490300759435989675754029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190640802025162639135344077 71490300759435989675754029)
  ·
    refine ⟨26808862784788496128407761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71490300759435989675754029 26808862784788496128407761)
    ·
      refine ⟨20106647088591372096305821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26808862784788496128407761 20106647088591372096305821)
      ·
        refine ⟨7539992658221764536114683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20106647088591372096305821 7539992658221764536114683)
        ·
          refine ⟨11309988987332646804172025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7539992658221764536114683 11309988987332646804172025)
          ·
            refine ⟨8482491740499485103129019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11309988987332646804172025 8482491740499485103129019)
            ·
              refine ⟨12723737610749227654693529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8482491740499485103129019 12723737610749227654693529)
              ·
                refine ⟨9542803208061920741020147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12723737610749227654693529 9542803208061920741020147)
                ·
                  refine ⟨14314204812092881111530221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9542803208061920741020147 14314204812092881111530221)
                  ·
                    refine ⟨5367826804534830416823833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14314204812092881111530221 5367826804534830416823833)
                    ·
                      refine ⟨4025870103401122812617875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5367826804534830416823833 4025870103401122812617875)
                      ·
                        rfl

theorem cell23_7840354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_7840354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840354 prefixEnd_7840354 := by exact prefixLift 7840354
  have htrace : WordTrace (prefixWord ++ tailWord_7840354) baseStart_7840354 baseEnd_7840354 := by
    simpa [prefixWord, tailWord_7840354, baseEnd_7840354] using wordTrace_append hprefix tailTrace_7840354
  have hstable : (prefixWord ++ tailWord_7840354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840354).length < 2 ^ (prefixWord ++ tailWord_7840354).sum := by decide
  have hdescent : baseEnd_7840354 < baseStart_7840354 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840419 : List Nat := [1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 4]
def baseStart_7840419 : Nat := 118140960795 + 7840419 * 2 ^ 59
def prefixEnd_7840419 : Nat := 4983230072969 + 3 ^ 40 * 7840419 * 2
def baseEnd_7840419 : Nat := 4025903479643665058305075

theorem tailTrace_7840419 : CollatzResearch.WordTrace tailWord_7840419 prefixEnd_7840419 4025903479643665058305075 := by
  unfold tailWord_7840419
  simp only [CollatzResearch.WordTrace]
  refine ⟨285963573782508474804132311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190642382521672316536088207 285963573782508474804132311)
  ·
    refine ⟨428945360673762712206198467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285963573782508474804132311 428945360673762712206198467)
    ·
      refine ⟨643418041010644068309297701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428945360673762712206198467 643418041010644068309297701)
      ·
        refine ⟨120640882689495762807993319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 643418041010644068309297701 120640882689495762807993319)
        ·
          refine ⟨180961324034243644211989979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120640882689495762807993319 180961324034243644211989979)
          ·
            refine ⟨271441986051365466317984969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180961324034243644211989979 271441986051365466317984969)
            ·
              refine ⟨203581489538524099738488727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271441986051365466317984969 203581489538524099738488727)
              ·
                refine ⟨305372234307786149607733091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203581489538524099738488727 305372234307786149607733091)
                ·
                  refine ⟨458058351461679224411599637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305372234307786149607733091 458058351461679224411599637)
                  ·
                    refine ⟨21471485224766213644293733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 458058351461679224411599637 21471485224766213644293733)
                    ·
                      refine ⟨4025903479643665058305075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21471485224766213644293733 4025903479643665058305075)
                      ·
                        rfl

theorem cell23_7840419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_7840419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840419 prefixEnd_7840419 := by exact prefixLift 7840419
  have htrace : WordTrace (prefixWord ++ tailWord_7840419) baseStart_7840419 baseEnd_7840419 := by
    simpa [prefixWord, tailWord_7840419, baseEnd_7840419] using wordTrace_append hprefix tailTrace_7840419
  have hstable : (prefixWord ++ tailWord_7840419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840419).length < 2 ^ (prefixWord ++ tailWord_7840419).sum := by decide
  have hdescent : baseEnd_7840419 < baseStart_7840419 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840446 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 8]
def baseStart_7840446 : Nat := 118140960795 + 7840446 * 2 ^ 59
def prefixEnd_7840446 : Nat := 4983230072969 + 3 ^ 40 * 7840446 * 2
def baseEnd_7840446 : Nat := 447324149291259605851939

theorem tailTrace_7840446 : CollatzResearch.WordTrace tailWord_7840446 prefixEnd_7840446 447324149291259605851939 := by
  unfold tailWord_7840446
  simp only [CollatzResearch.WordTrace]
  refine ⟨35745569819176332301920649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190643039035607105610243461 35745569819176332301920649)
  ·
    refine ⟨26809177364382249226440487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35745569819176332301920649 26809177364382249226440487)
    ·
      refine ⟨40213766046573373839660731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26809177364382249226440487 40213766046573373839660731)
      ·
        refine ⟨60320649069860060759491097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40213766046573373839660731 60320649069860060759491097)
        ·
          refine ⟨45240486802395045569618323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60320649069860060759491097 45240486802395045569618323)
          ·
            refine ⟨67860730203592568354427485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45240486802395045569618323 67860730203592568354427485)
            ·
              refine ⟨25447773826347213132910307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67860730203592568354427485 25447773826347213132910307)
              ·
                refine ⟨38171660739520819699365461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25447773826347213132910307 38171660739520819699365461)
                ·
                  refine ⟨447324149291259605851939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 38171660739520819699365461 447324149291259605851939)
                  ·
                    rfl

theorem cell23_7840446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_7840446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840446 prefixEnd_7840446 := by exact prefixLift 7840446
  have htrace : WordTrace (prefixWord ++ tailWord_7840446) baseStart_7840446 baseEnd_7840446 := by
    simpa [prefixWord, tailWord_7840446, baseEnd_7840446] using wordTrace_append hprefix tailTrace_7840446
  have hstable : (prefixWord ++ tailWord_7840446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840446).length < 2 ^ (prefixWord ++ tailWord_7840446).sum := by decide
  have hdescent : baseEnd_7840446 < baseStart_7840446 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840473 : List Nat := [1, 2, 1, 2, 3, 2, 1, 4, 3, 1, 3]
def baseStart_7840473 : Nat := 118140960795 + 7840473 * 2 ^ 59
def prefixEnd_7840473 : Nat := 4983230072969 + 3 ^ 40 * 7840473 * 2
def baseEnd_7840473 : Nat := 4025931207599007847029827

theorem tailTrace_7840473 : CollatzResearch.WordTrace tailWord_7840473 prefixEnd_7840473 4025931207599007847029827 := by
  unfold tailWord_7840473
  simp only [CollatzResearch.WordTrace]
  refine ⟨285965543324312842026598073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190643695549541894684398715 285965543324312842026598073)
  ·
    refine ⟨214474157493234631519948555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285965543324312842026598073 214474157493234631519948555)
    ·
      refine ⟨321711236239851947279922833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214474157493234631519948555 321711236239851947279922833)
      ·
        refine ⟨241283427179888960459942125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321711236239851947279922833 241283427179888960459942125)
        ·
          refine ⟨90481285192458360172478297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241283427179888960459942125 90481285192458360172478297)
          ·
            refine ⟨67860963894343770129358723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90481285192458360172478297 67860963894343770129358723)
            ·
              refine ⟨101791445841515655194038085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67860963894343770129358723 101791445841515655194038085)
              ·
                refine ⟨19085896095284185348882141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101791445841515655194038085 19085896095284185348882141)
                ·
                  refine ⟨7157211035731569505830803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19085896095284185348882141 7157211035731569505830803)
                  ·
                    refine ⟨10735816553597354258746205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7157211035731569505830803 10735816553597354258746205)
                    ·
                      refine ⟨4025931207599007847029827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10735816553597354258746205 4025931207599007847029827)
                      ·
                        rfl

theorem cell23_7840473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 4, 3, 1, 3].length) (baseStart_7840473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840473 prefixEnd_7840473 := by exact prefixLift 7840473
  have htrace : WordTrace (prefixWord ++ tailWord_7840473) baseStart_7840473 baseEnd_7840473 := by
    simpa [prefixWord, tailWord_7840473, baseEnd_7840473] using wordTrace_append hprefix tailTrace_7840473
  have hstable : (prefixWord ++ tailWord_7840473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840473).length < 2 ^ (prefixWord ++ tailWord_7840473).sum := by decide
  have hdescent : baseEnd_7840473 < baseStart_7840473 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840493 : List Nat := [1, 5, 1, 2, 1, 1, 1, 5, 1, 5]
def baseStart_7840493 : Nat := 118140960795 + 7840493 * 2 ^ 59
def prefixEnd_7840493 : Nat := 4983230072969 + 3 ^ 40 * 7840493 * 2
def baseEnd_7840493 : Nat := 1341980492404032589593245

theorem tailTrace_7840493 : CollatzResearch.WordTrace tailWord_7840493 prefixEnd_7840493 1341980492404032589593245 := by
  unfold tailWord_7840493
  simp only [CollatzResearch.WordTrace]
  refine ⟨285966272784240385442326133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190644181856160256961550755 285966272784240385442326133)
  ·
    refine ⟨26809338073522536135218075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 285966272784240385442326133 26809338073522536135218075)
    ·
      refine ⟨40214007110283804202827113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26809338073522536135218075 40214007110283804202827113)
      ·
        refine ⟨30160505332712853152120335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40214007110283804202827113 30160505332712853152120335)
        ·
          refine ⟨45240757999069279728180503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30160505332712853152120335 45240757999069279728180503)
          ·
            refine ⟨67861136998603919592270755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45240757999069279728180503 67861136998603919592270755)
            ·
              refine ⟨101791705497905879388406133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67861136998603919592270755 101791705497905879388406133)
              ·
                refine ⟨9542972390428676192663075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101791705497905879388406133 9542972390428676192663075)
                ·
                  refine ⟨14314458585643014288994613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9542972390428676192663075 14314458585643014288994613)
                  ·
                    refine ⟨1341980492404032589593245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14314458585643014288994613 1341980492404032589593245)
                    ·
                      rfl

theorem cell23_7840493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_7840493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840493 prefixEnd_7840493 := by exact prefixLift 7840493
  have htrace : WordTrace (prefixWord ++ tailWord_7840493) baseStart_7840493 baseEnd_7840493 := by
    simpa [prefixWord, tailWord_7840493, baseEnd_7840493] using wordTrace_append hprefix tailTrace_7840493
  have hstable : (prefixWord ++ tailWord_7840493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840493).length < 2 ^ (prefixWord ++ tailWord_7840493).sum := by decide
  have hdescent : baseEnd_7840493 < baseStart_7840493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840501 : List Nat := [1, 3, 6, 1, 2, 1, 1, 1, 3, 4]
def baseStart_7840501 : Nat := 118140960795 + 7840501 * 2 ^ 59
def prefixEnd_7840501 : Nat := 4983230072969 + 3 ^ 40 * 7840501 * 2
def baseEnd_7840501 : Nat := 1341981861685777912493233

theorem tailTrace_7840501 : CollatzResearch.WordTrace tailWord_7840501 prefixEnd_7840501 1341981861685777912493233 := by
  unfold tailWord_7840501
  simp only [CollatzResearch.WordTrace]
  refine ⟨285966564568211402808617357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190644376378807601872411571 285966564568211402808617357)
  ·
    refine ⟨107237461713079276053231509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285966564568211402808617357 107237461713079276053231509)
    ·
      refine ⟨5026756017800591064995227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 107237461713079276053231509 5026756017800591064995227)
      ·
        refine ⟨7540134026700886597492841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5026756017800591064995227 7540134026700886597492841)
        ·
          refine ⟨5655100520025664948119631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7540134026700886597492841 5655100520025664948119631)
          ·
            refine ⟨8482650780038497422179447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5655100520025664948119631 8482650780038497422179447)
            ·
              refine ⟨12723976170057746133269171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8482650780038497422179447 12723976170057746133269171)
              ·
                refine ⟨19085964255086619199903757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12723976170057746133269171 19085964255086619199903757)
                ·
                  refine ⟨7157236595657482199963909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19085964255086619199903757 7157236595657482199963909)
                  ·
                    refine ⟨1341981861685777912493233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7157236595657482199963909 1341981861685777912493233)
                    ·
                      rfl

theorem cell23_7840501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_7840501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840501 prefixEnd_7840501 := by exact prefixLift 7840501
  have htrace : WordTrace (prefixWord ++ tailWord_7840501) baseStart_7840501 baseEnd_7840501 := by
    simpa [prefixWord, tailWord_7840501, baseEnd_7840501] using wordTrace_append hprefix tailTrace_7840501
  have hstable : (prefixWord ++ tailWord_7840501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840501).length < 2 ^ (prefixWord ++ tailWord_7840501).sum := by decide
  have hdescent : baseEnd_7840501 < baseStart_7840501 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840533 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 3, 2, 3]
def baseStart_7840533 : Nat := 118140960795 + 7840533 * 2 ^ 59
def prefixEnd_7840533 : Nat := 4983230072969 + 3 ^ 40 * 7840533 * 2
def baseEnd_7840533 : Nat := 4025962016438277612279551

theorem tailTrace_7840533 : CollatzResearch.WordTrace tailWord_7840533 prefixEnd_7840533 4025962016438277612279551 := by
  unfold tailWord_7840533
  simp only [CollatzResearch.WordTrace]
  refine ⟨285967731704095472273782253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190645154469396981515854835 285967731704095472273782253)
  ·
    refine ⟨107237899389035802102668345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285967731704095472273782253 107237899389035802102668345)
    ·
      refine ⟨80428424541776851577001259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107237899389035802102668345 80428424541776851577001259)
      ·
        refine ⟨120642636812665277365501889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80428424541776851577001259 120642636812665277365501889)
        ·
          refine ⟨90481977609498958024126417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120642636812665277365501889 90481977609498958024126417)
          ·
            refine ⟨67861483207124218518094813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90481977609498958024126417 67861483207124218518094813)
            ·
              refine ⟨25448056202671581944285555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67861483207124218518094813 25448056202671581944285555)
              ·
                refine ⟨38172084304007372916428333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25448056202671581944285555 38172084304007372916428333)
                ·
                  refine ⟨14314531614002764843660625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38172084304007372916428333 14314531614002764843660625)
                  ·
                    refine ⟨10735898710502073632745469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14314531614002764843660625 10735898710502073632745469)
                    ·
                      refine ⟨4025962016438277612279551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10735898710502073632745469 4025962016438277612279551)
                      ·
                        rfl

theorem cell23_7840533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 3, 2, 3].length) (baseStart_7840533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840533 prefixEnd_7840533 := by exact prefixLift 7840533
  have htrace : WordTrace (prefixWord ++ tailWord_7840533) baseStart_7840533 baseEnd_7840533 := by
    simpa [prefixWord, tailWord_7840533, baseEnd_7840533] using wordTrace_append hprefix tailTrace_7840533
  have hstable : (prefixWord ++ tailWord_7840533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840533).length < 2 ^ (prefixWord ++ tailWord_7840533).sum := by decide
  have hdescent : baseEnd_7840533 < baseStart_7840533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840543 : List Nat := [1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 4]
def baseStart_7840543 : Nat := 118140960795 + 7840543 * 2 ^ 59
def prefixEnd_7840543 : Nat := 4983230072969 + 3 ^ 40 * 7840543 * 2
def baseEnd_7840543 : Nat := 4025967151244822573154505

theorem tailTrace_7840543 : CollatzResearch.WordTrace tailWord_7840543 prefixEnd_7840543 4025967151244822573154505 := by
  unfold tailWord_7840543
  simp only [CollatzResearch.WordTrace]
  refine ⟨285968096434059243981646283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190645397622706162654430855 285968096434059243981646283)
  ·
    refine ⟨428952144651088865972469425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285968096434059243981646283 428952144651088865972469425)
    ·
      refine ⟨321714108488316649479352069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428952144651088865972469425 321714108488316649479352069)
      ·
        refine ⟨60321395341559371777378513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321714108488316649479352069 60321395341559371777378513)
        ·
          refine ⟨45241046506169528833033885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60321395341559371777378513 45241046506169528833033885)
          ·
            refine ⟨16965392439813573312387707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45241046506169528833033885 16965392439813573312387707)
            ·
              refine ⟨25448088659720359968581561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16965392439813573312387707 25448088659720359968581561)
              ·
                refine ⟨19086066494790269976436171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25448088659720359968581561 19086066494790269976436171)
                ·
                  refine ⟨28629099742185404964654257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19086066494790269976436171 28629099742185404964654257)
                  ·
                    refine ⟨21471824806639053723490693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28629099742185404964654257 21471824806639053723490693)
                    ·
                      refine ⟨4025967151244822573154505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21471824806639053723490693 4025967151244822573154505)
                      ·
                        rfl

theorem cell23_7840543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_7840543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840543 prefixEnd_7840543 := by exact prefixLift 7840543
  have htrace : WordTrace (prefixWord ++ tailWord_7840543) baseStart_7840543 baseEnd_7840543 := by
    simpa [prefixWord, tailWord_7840543, baseEnd_7840543] using wordTrace_append hprefix tailTrace_7840543
  have hstable : (prefixWord ++ tailWord_7840543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840543).length < 2 ^ (prefixWord ++ tailWord_7840543).sum := by decide
  have hdescent : baseEnd_7840543 < baseStart_7840543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840547 : List Nat := [1, 1, 1, 4, 2, 1, 1, 7, 1, 2, 2]
def baseStart_7840547 : Nat := 118140960795 + 7840547 * 2 ^ 59
def prefixEnd_7840547 : Nat := 4983230072969 + 3 ^ 40 * 7840547 * 2
def baseEnd_7840547 : Nat := 4025969205167440557504487

theorem tailTrace_7840547 : CollatzResearch.WordTrace tailWord_7840547 prefixEnd_7840547 4025969205167440557504487 := by
  unfold tailWord_7840547
  simp only [CollatzResearch.WordTrace]
  refine ⟨285968242326044752664791895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190645494884029835109861263 285968242326044752664791895)
  ·
    refine ⟨428952363489067128997187843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285968242326044752664791895 428952363489067128997187843)
    ·
      refine ⟨643428545233600693495781765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428952363489067128997187843 643428545233600693495781765)
      ·
        refine ⟨120642852231300130030459081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 643428545233600693495781765 120642852231300130030459081)
        ·
          refine ⟨90482139173475097522844311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120642852231300130030459081 90482139173475097522844311)
          ·
            refine ⟨135723208760212646284266467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90482139173475097522844311 135723208760212646284266467)
            ·
              refine ⟨203584813140318969426399701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 135723208760212646284266467 203584813140318969426399701)
              ·
                refine ⟨4771519057976225845931243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 203584813140318969426399701 4771519057976225845931243)
                ·
                  refine ⟨7157278586964338768896865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4771519057976225845931243 7157278586964338768896865)
                  ·
                    refine ⟨5367958940223254076672649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7157278586964338768896865 5367958940223254076672649)
                    ·
                      refine ⟨4025969205167440557504487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5367958940223254076672649 4025969205167440557504487)
                      ·
                        rfl

theorem cell23_7840547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 7, 1, 2, 2].length) (baseStart_7840547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840547 prefixEnd_7840547 := by exact prefixLift 7840547
  have htrace : WordTrace (prefixWord ++ tailWord_7840547) baseStart_7840547 baseEnd_7840547 := by
    simpa [prefixWord, tailWord_7840547, baseEnd_7840547] using wordTrace_append hprefix tailTrace_7840547
  have hstable : (prefixWord ++ tailWord_7840547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840547).length < 2 ^ (prefixWord ++ tailWord_7840547).sum := by decide
  have hdescent : baseEnd_7840547 < baseStart_7840547 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840570 : List Nat := [3, 1, 1, 1, 7, 1, 1, 8]
def baseStart_7840570 : Nat := 118140960795 + 7840570 * 2 ^ 59
def prefixEnd_7840570 : Nat := 4983230072969 + 3 ^ 40 * 7840570 * 2
def baseEnd_7840570 : Nat := 149110407971203480278403

theorem tailTrace_7840570 : CollatzResearch.WordTrace tailWord_7840570 prefixEnd_7840570 149110407971203480278403 := by
  unfold tailWord_7840570
  simp only [CollatzResearch.WordTrace]
  refine ⟨71492270301240356898219791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190646054136640951728586109 71492270301240356898219791)
  ·
    refine ⟨107238405451860535347329687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71492270301240356898219791 107238405451860535347329687)
    ·
      refine ⟨160857608177790803020994531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107238405451860535347329687 160857608177790803020994531)
      ·
        refine ⟨241286412266686204531491797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160857608177790803020994531 241286412266686204531491797)
        ·
          refine ⟨5655150287500457918706839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 241286412266686204531491797 5655150287500457918706839)
          ·
            refine ⟨8482725431250686878060259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5655150287500457918706839 8482725431250686878060259)
            ·
              refine ⟨12724088146876030317090389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8482725431250686878060259 12724088146876030317090389)
              ·
                refine ⟨149110407971203480278403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12724088146876030317090389 149110407971203480278403)
                ·
                  rfl

theorem cell23_7840570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 8].length) (baseStart_7840570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840570 prefixEnd_7840570 := by exact prefixLift 7840570
  have htrace : WordTrace (prefixWord ++ tailWord_7840570) baseStart_7840570 baseEnd_7840570 := by
    simpa [prefixWord, tailWord_7840570, baseEnd_7840570] using wordTrace_append hprefix tailTrace_7840570
  have hstable : (prefixWord ++ tailWord_7840570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840570).length < 2 ^ (prefixWord ++ tailWord_7840570).sum := by decide
  have hdescent : baseEnd_7840570 < baseStart_7840570 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840577 : List Nat := [1, 2, 5, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_7840577 : Nat := 118140960795 + 7840577 * 2 ^ 59
def prefixEnd_7840577 : Nat := 4983230072969 + 3 ^ 40 * 7840577 * 2
def baseEnd_7840577 : Nat := 4025984609587075440129349

theorem tailTrace_7840577 : CollatzResearch.WordTrace tailWord_7840577 prefixEnd_7840577 4025984609587075440129349 := by
  unfold tailWord_7840577
  simp only [CollatzResearch.WordTrace]
  refine ⟨285969336515936067788383985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190646224343957378525589323 285969336515936067788383985)
  ·
    refine ⟨214477002386952050841287989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285969336515936067788383985 214477002386952050841287989)
    ·
      refine ⟨20107218973776754766370749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 214477002386952050841287989 20107218973776754766370749)
      ·
        refine ⟨7540207115166283037389031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20107218973776754766370749 7540207115166283037389031)
        ·
          refine ⟨11310310672749424556083547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7540207115166283037389031 11310310672749424556083547)
          ·
            refine ⟨16965466009124136834125321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11310310672749424556083547 16965466009124136834125321)
            ·
              refine ⟨12724099506843102625593991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16965466009124136834125321 12724099506843102625593991)
              ·
                refine ⟨19086149260264653938390987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12724099506843102625593991 19086149260264653938390987)
                ·
                  refine ⟨28629223890396980907586481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19086149260264653938390987 28629223890396980907586481)
                  ·
                    refine ⟨21471917917797735680689861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28629223890396980907586481 21471917917797735680689861)
                    ·
                      refine ⟨4025984609587075440129349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21471917917797735680689861 4025984609587075440129349)
                      ·
                        rfl

theorem cell23_7840577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_7840577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840577 prefixEnd_7840577 := by exact prefixLift 7840577
  have htrace : WordTrace (prefixWord ++ tailWord_7840577) baseStart_7840577 baseEnd_7840577 := by
    simpa [prefixWord, tailWord_7840577, baseEnd_7840577] using wordTrace_append hprefix tailTrace_7840577
  have hstable : (prefixWord ++ tailWord_7840577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840577).length < 2 ^ (prefixWord ++ tailWord_7840577).sum := by decide
  have hdescent : baseEnd_7840577 < baseStart_7840577 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840603 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 9, 4, 2]
def baseStart_7840603 : Nat := 118140960795 + 7840603 * 2 ^ 59
def prefixEnd_7840603 : Nat := 4983230072969 + 3 ^ 40 * 7840603 * 2
def baseEnd_7840603 : Nat := 4025997960084092338404229

theorem tailTrace_7840603 : CollatzResearch.WordTrace tailWord_7840603 prefixEnd_7840603 4025997960084092338404229 := by
  unfold tailWord_7840603
  simp only [CollatzResearch.WordTrace]
  refine ⟨285970284813841874228830463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190646856542561249485886975 285970284813841874228830463)
  ·
    refine ⟨428955427220762811343245695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285970284813841874228830463 428955427220762811343245695)
    ·
      refine ⟨643433140831144217014868543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428955427220762811343245695 643433140831144217014868543)
      ·
        refine ⟨965149711246716325522302815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643433140831144217014868543 965149711246716325522302815)
        ·
          refine ⟨1447724566870074488283454223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965149711246716325522302815 1447724566870074488283454223)
          ·
            refine ⟨2171586850305111732425181335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447724566870074488283454223 2171586850305111732425181335)
            ·
              refine ⟨3257380275457667598637772003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2171586850305111732425181335 3257380275457667598637772003)
              ·
                refine ⟨4886070413186501397956658005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3257380275457667598637772003 4886070413186501397956658005)
                ·
                  refine ⟨28629318827264656628652293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4886070413186501397956658005 28629318827264656628652293)
                  ·
                    refine ⟨5367997280112123117872305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28629318827264656628652293 5367997280112123117872305)
                    ·
                      refine ⟨4025997960084092338404229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5367997280112123117872305 4025997960084092338404229)
                      ·
                        rfl

theorem cell23_7840603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 4, 2].length) (baseStart_7840603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840603 prefixEnd_7840603 := by exact prefixLift 7840603
  have htrace : WordTrace (prefixWord ++ tailWord_7840603) baseStart_7840603 baseEnd_7840603 := by
    simpa [prefixWord, tailWord_7840603, baseEnd_7840603] using wordTrace_append hprefix tailTrace_7840603
  have hstable : (prefixWord ++ tailWord_7840603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840603).length < 2 ^ (prefixWord ++ tailWord_7840603).sum := by decide
  have hdescent : baseEnd_7840603 < baseStart_7840603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840630 : List Nat := [5, 1, 1, 3, 1, 1, 2, 1, 2, 6]
def baseStart_7840630 : Nat := 118140960795 + 7840630 * 2 ^ 59
def prefixEnd_7840630 : Nat := 4983230072969 + 3 ^ 40 * 7840630 * 2
def baseEnd_7840630 : Nat := 1342003941353921244255535

theorem tailTrace_7840630 : CollatzResearch.WordTrace tailWord_7840630 prefixEnd_7840630 1342003941353921244255535 := by
  unfold tailWord_7840630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17873204349046503615003959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 190647513056496038560042229 17873204349046503615003959)
  ·
    refine ⟨26809806523569755422505939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17873204349046503615003959 26809806523569755422505939)
    ·
      refine ⟨40214709785354633133758909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26809806523569755422505939 40214709785354633133758909)
      ·
        refine ⟨15080516169507987425159591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40214709785354633133758909 15080516169507987425159591)
        ·
          refine ⟨22620774254261981137739387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15080516169507987425159591 22620774254261981137739387)
          ·
            refine ⟨33931161381392971706609081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22620774254261981137739387 33931161381392971706609081)
            ·
              refine ⟨25448371036044728779956811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33931161381392971706609081 25448371036044728779956811)
              ·
                refine ⟨38172556554067093169935217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25448371036044728779956811 38172556554067093169935217)
                ·
                  refine ⟨28629417415550319877451413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38172556554067093169935217 28629417415550319877451413)
                  ·
                    refine ⟨1342003941353921244255535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28629417415550319877451413 1342003941353921244255535)
                    ·
                      rfl

theorem cell23_7840630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 1, 2, 6].length) (baseStart_7840630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840630 prefixEnd_7840630 := by exact prefixLift 7840630
  have htrace : WordTrace (prefixWord ++ tailWord_7840630) baseStart_7840630 baseEnd_7840630 := by
    simpa [prefixWord, tailWord_7840630, baseEnd_7840630] using wordTrace_append hprefix tailTrace_7840630
  have hstable : (prefixWord ++ tailWord_7840630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840630).length < 2 ^ (prefixWord ++ tailWord_7840630).sum := by decide
  have hdescent : baseEnd_7840630 < baseStart_7840630 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840633 : List Nat := [1, 2, 1, 3, 2, 3, 2, 1, 2, 2, 4]
def baseStart_7840633 : Nat := 118140960795 + 7840633 * 2 ^ 59
def prefixEnd_7840633 : Nat := 4983230072969 + 3 ^ 40 * 7840633 * 2
def baseEnd_7840633 : Nat := 4026013364503727221029091

theorem tailTrace_7840633 : CollatzResearch.WordTrace tailWord_7840633 prefixEnd_7840633 4026013364503727221029091 := by
  unfold tailWord_7840633
  simp only [CollatzResearch.WordTrace]
  refine ⟨285971379003733189352422553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190647586002488792901615035 285971379003733189352422553)
  ·
    refine ⟨214478534252799892014316915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285971379003733189352422553 214478534252799892014316915)
    ·
      refine ⟨321717801379199838021475373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214478534252799892014316915 321717801379199838021475373)
      ·
        refine ⟨120644175517199939258053265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321717801379199838021475373 120644175517199939258053265)
        ·
          refine ⟨90483131637899954443539949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120644175517199939258053265 90483131637899954443539949)
          ·
            refine ⟨33931174364212482916327481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 90483131637899954443539949 33931174364212482916327481)
            ·
              refine ⟨25448380773159362187245611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33931174364212482916327481 25448380773159362187245611)
              ·
                refine ⟨38172571159739043280868417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25448380773159362187245611 38172571159739043280868417)
                ·
                  refine ⟨28629428369804282460651313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38172571159739043280868417 28629428369804282460651313)
                  ·
                    refine ⟨21472071277353211845488485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28629428369804282460651313 21472071277353211845488485)
                    ·
                      refine ⟨4026013364503727221029091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21472071277353211845488485 4026013364503727221029091)
                      ·
                        rfl

theorem cell23_7840633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_7840633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840633 prefixEnd_7840633 := by exact prefixLift 7840633
  have htrace : WordTrace (prefixWord ++ tailWord_7840633) baseStart_7840633 baseEnd_7840633 := by
    simpa [prefixWord, tailWord_7840633, baseEnd_7840633] using wordTrace_append hprefix tailTrace_7840633
  have hstable : (prefixWord ++ tailWord_7840633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840633).length < 2 ^ (prefixWord ++ tailWord_7840633).sum := by decide
  have hdescent : baseEnd_7840633 < baseStart_7840633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840636 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 1, 1, 9]
def baseStart_7840636 : Nat := 118140960795 + 7840636 * 2 ^ 59
def prefixEnd_7840636 : Nat := 4983230072969 + 3 ^ 40 * 7840636 * 2
def baseEnd_7840636 : Nat := 4026014904945690709291577

theorem tailTrace_7840636 : CollatzResearch.WordTrace tailWord_7840636 prefixEnd_7840636 4026014904945690709291577 := by
  unfold tailWord_7840636
  simp only [CollatzResearch.WordTrace]
  refine ⟨142985744211361160432390881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190647658948481547243187841 142985744211361160432390881)
  ·
    refine ⟨107239308158520870324293161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142985744211361160432390881 107239308158520870324293161)
    ·
      refine ⟨80429481118890652743219871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107239308158520870324293161 80429481118890652743219871)
      ·
        refine ⟨120644221678335979114829807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80429481118890652743219871 120644221678335979114829807)
        ·
          refine ⟨180966332517503968672244711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120644221678335979114829807 180966332517503968672244711)
          ·
            refine ⟨271449498776255953008367067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180966332517503968672244711 271449498776255953008367067)
            ·
              refine ⟨407174248164383929512550601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271449498776255953008367067 407174248164383929512550601)
              ·
                refine ⟨305380686123287947134412951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407174248164383929512550601 305380686123287947134412951)
                ·
                  refine ⟨458071029184931920701619427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305380686123287947134412951 458071029184931920701619427)
                  ·
                    refine ⟨687106543777397881052429141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 458071029184931920701619427 687106543777397881052429141)
                    ·
                      refine ⟨4026014904945690709291577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 687106543777397881052429141 4026014904945690709291577)
                      ·
                        rfl

theorem cell23_7840636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_7840636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840636 prefixEnd_7840636 := by exact prefixLift 7840636
  have htrace : WordTrace (prefixWord ++ tailWord_7840636) baseStart_7840636 baseEnd_7840636 := by
    simpa [prefixWord, tailWord_7840636, baseEnd_7840636] using wordTrace_append hprefix tailTrace_7840636
  have hstable : (prefixWord ++ tailWord_7840636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840636).length < 2 ^ (prefixWord ++ tailWord_7840636).sum := by decide
  have hdescent : baseEnd_7840636 < baseStart_7840636 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840637 : List Nat := [1, 4, 1, 1, 2, 1, 2, 5, 2, 2, 2]
def baseStart_7840637 : Nat := 118140960795 + 7840637 * 2 ^ 59
def prefixEnd_7840637 : Nat := 4983230072969 + 3 ^ 40 * 7840637 * 2
def baseEnd_7840637 : Nat := 4026015418426345205379073

theorem tailTrace_7840637 : CollatzResearch.WordTrace tailWord_7840637 prefixEnd_7840637 4026015418426345205379073 := by
  unfold tailWord_7840637
  simp only [CollatzResearch.WordTrace]
  refine ⟨285971524895718698035568165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190647683263812465357045443 285971524895718698035568165)
  ·
    refine ⟨53619660917947255881669031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285971524895718698035568165 53619660917947255881669031)
    ·
      refine ⟨80429491376920883822503547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53619660917947255881669031 80429491376920883822503547)
      ·
        refine ⟨120644237065381325733755321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80429491376920883822503547 120644237065381325733755321)
        ·
          refine ⟨90483177799035994300316491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120644237065381325733755321 90483177799035994300316491)
          ·
            refine ⟨135724766698553991450474737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90483177799035994300316491 135724766698553991450474737)
            ·
              refine ⟨101793575023915493587856053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135724766698553991450474737 101793575023915493587856053)
              ·
                refine ⟨9543147658492077523861505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101793575023915493587856053 9543147658492077523861505)
                ·
                  refine ⟨7157360743869058142896129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9543147658492077523861505 7157360743869058142896129)
                  ·
                    refine ⟨5368020557901793607172097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7157360743869058142896129 5368020557901793607172097)
                    ·
                      refine ⟨4026015418426345205379073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368020557901793607172097 4026015418426345205379073)
                      ·
                        rfl

theorem cell23_7840637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 5, 2, 2, 2].length) (baseStart_7840637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840637 prefixEnd_7840637 := by exact prefixLift 7840637
  have htrace : WordTrace (prefixWord ++ tailWord_7840637) baseStart_7840637 baseEnd_7840637 := by
    simpa [prefixWord, tailWord_7840637, baseEnd_7840637] using wordTrace_append hprefix tailTrace_7840637
  have hstable : (prefixWord ++ tailWord_7840637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840637).length < 2 ^ (prefixWord ++ tailWord_7840637).sum := by decide
  have hdescent : baseEnd_7840637 < baseStart_7840637 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840656 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 5, 7]
def baseStart_7840656 : Nat := 118140960795 + 7840656 * 2 ^ 59
def prefixEnd_7840656 : Nat := 4983230072969 + 3 ^ 40 * 7840656 * 2
def baseEnd_7840656 : Nat := 1342008391519593543680495

theorem tailTrace_7840656 : CollatzResearch.WordTrace tailWord_7840656 prefixEnd_7840656 1342008391519593543680495 := by
  unfold tailWord_7840656
  simp only [CollatzResearch.WordTrace]
  refine ⟨142986108941324932140254911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190648145255099909520339881 142986108941324932140254911)
  ·
    refine ⟨214479163411987398210382367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142986108941324932140254911 214479163411987398210382367)
    ·
      refine ⟨321718745117981097315573551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214479163411987398210382367 321718745117981097315573551)
      ·
        refine ⟨482578117676971645973360327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321718745117981097315573551 482578117676971645973360327)
        ·
          refine ⟨723867176515457468960040491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482578117676971645973360327 723867176515457468960040491)
          ·
            refine ⟨1085800764773186203440060737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723867176515457468960040491 1085800764773186203440060737)
            ·
              refine ⟨814350573579889652580045553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1085800764773186203440060737 814350573579889652580045553)
              ·
                refine ⟨610762930184917239435034165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 814350573579889652580045553 610762930184917239435034165)
                ·
                  refine ⟨57259024704835991197034453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 610762930184917239435034165 57259024704835991197034453)
                  ·
                    refine ⟨1342008391519593543680495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57259024704835991197034453 1342008391519593543680495)
                    ·
                      rfl

theorem cell23_7840656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 5, 7].length) (baseStart_7840656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840656 prefixEnd_7840656 := by exact prefixLift 7840656
  have htrace : WordTrace (prefixWord ++ tailWord_7840656) baseStart_7840656 baseEnd_7840656 := by
    simpa [prefixWord, tailWord_7840656, baseEnd_7840656] using wordTrace_append hprefix tailTrace_7840656
  have hstable : (prefixWord ++ tailWord_7840656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840656).length < 2 ^ (prefixWord ++ tailWord_7840656).sum := by decide
  have hdescent : baseEnd_7840656 < baseStart_7840656 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840754 : List Nat := [3, 2, 1, 5, 1, 1, 1, 2, 3, 4]
def baseStart_7840754 : Nat := 118140960795 + 7840754 * 2 ^ 59
def prefixEnd_7840754 : Nat := 4983230072969 + 3 ^ 40 * 7840754 * 2
def baseEnd_7840754 : Nat := 1342025165220973749205345

theorem tailTrace_7840754 : CollatzResearch.WordTrace tailWord_7840754 prefixEnd_7840754 1342025165220973749205345 := by
  unfold tailWord_7840754
  simp only [CollatzResearch.WordTrace]
  refine ⟨71493948059073706754394329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190650528157529884678384877 71493948059073706754394329)
  ·
    refine ⟨53620461044305280065795747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71493948059073706754394329 53620461044305280065795747)
    ·
      refine ⟨80430691566457920098693621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53620461044305280065795747 80430691566457920098693621)
      ·
        refine ⟨7540377334355430009252527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 80430691566457920098693621 7540377334355430009252527)
        ·
          refine ⟨11310566001533145013878791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7540377334355430009252527 11310566001533145013878791)
          ·
            refine ⟨16965849002299717520818187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11310566001533145013878791 16965849002299717520818187)
            ·
              refine ⟨25448773503449576281227281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16965849002299717520818187 25448773503449576281227281)
              ·
                refine ⟨19086580127587182210920461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25448773503449576281227281 19086580127587182210920461)
                ·
                  refine ⟨7157467547845193329095173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19086580127587182210920461 7157467547845193329095173)
                  ·
                    refine ⟨1342025165220973749205345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7157467547845193329095173 1342025165220973749205345)
                    ·
                      rfl

theorem cell23_7840754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 2, 3, 4].length) (baseStart_7840754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840754 prefixEnd_7840754 := by exact prefixLift 7840754
  have htrace : WordTrace (prefixWord ++ tailWord_7840754) baseStart_7840754 baseEnd_7840754 := by
    simpa [prefixWord, tailWord_7840754, baseEnd_7840754] using wordTrace_append hprefix tailTrace_7840754
  have hstable : (prefixWord ++ tailWord_7840754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840754).length < 2 ^ (prefixWord ++ tailWord_7840754).sum := by decide
  have hdescent : baseEnd_7840754 < baseStart_7840754 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840793 : List Nat := [1, 2, 1, 2, 1, 1, 4, 2, 3, 6]
def baseStart_7840793 : Nat := 118140960795 + 7840793 * 2 ^ 59
def prefixEnd_7840793 : Nat := 4983230072969 + 3 ^ 40 * 7840793 * 2
def baseEnd_7840793 : Nat := 1342031840469482198342785

theorem tailTrace_7840793 : CollatzResearch.WordTrace tailWord_7840793 prefixEnd_7840793 1342031840469482198342785 := by
  unfold tailWord_7840793
  simp only [CollatzResearch.WordTrace]
  refine ⟨285977214683153536678247033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190651476455435691118831355 285977214683153536678247033)
  ·
    refine ⟨214482911012365152508685275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285977214683153536678247033 214482911012365152508685275)
    ·
      refine ⟨321724366518547728763027913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214482911012365152508685275 321724366518547728763027913)
      ·
        refine ⟨241293274888910796572270935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321724366518547728763027913 241293274888910796572270935)
        ·
          refine ⟨361939912333366194858406403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241293274888910796572270935 361939912333366194858406403)
          ·
            refine ⟨542909868500049292287609605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361939912333366194858406403 542909868500049292287609605)
            ·
              refine ⟨101795600343759242303926801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 542909868500049292287609605 101795600343759242303926801)
              ·
                refine ⟨76346700257819431727945101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101795600343759242303926801 76346700257819431727945101)
                ·
                  refine ⟨28630012596682286897979413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 76346700257819431727945101 28630012596682286897979413)
                  ·
                    refine ⟨1342031840469482198342785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28630012596682286897979413 1342031840469482198342785)
                    ·
                      rfl

theorem cell23_7840793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 6].length) (baseStart_7840793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840793 prefixEnd_7840793 := by exact prefixLift 7840793
  have htrace : WordTrace (prefixWord ++ tailWord_7840793) baseStart_7840793 baseEnd_7840793 := by
    simpa [prefixWord, tailWord_7840793, baseEnd_7840793] using wordTrace_append hprefix tailTrace_7840793
  have hstable : (prefixWord ++ tailWord_7840793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840793).length < 2 ^ (prefixWord ++ tailWord_7840793).sum := by decide
  have hdescent : baseEnd_7840793 < baseStart_7840793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840794 : List Nat := [3, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3]
def baseStart_7840794 : Nat := 118140960795 + 7840794 * 2 ^ 59
def prefixEnd_7840794 : Nat := 4983230072969 + 3 ^ 40 * 7840794 * 2
def baseEnd_7840794 : Nat := 4026096034889101091115851

theorem tailTrace_7840794 : CollatzResearch.WordTrace tailWord_7840794 prefixEnd_7840794 4026096034889101091115851 := by
  unfold tailWord_7840794
  simp only [CollatzResearch.WordTrace]
  refine ⟨71494312789037478462258359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190651500770766609232688957 71494312789037478462258359)
  ·
    refine ⟨107241469183556217693387539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71494312789037478462258359 107241469183556217693387539)
    ·
      refine ⟨160862203775334326540081309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107241469183556217693387539 160862203775334326540081309)
      ·
        refine ⟨60323326415750372452530491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160862203775334326540081309 60323326415750372452530491)
        ·
          refine ⟨90484989623625558678795737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60323326415750372452530491 90484989623625558678795737)
          ·
            refine ⟨67863742217719169009096803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90484989623625558678795737 67863742217719169009096803)
            ·
              refine ⟨101795613326578753513645205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67863742217719169009096803 101795613326578753513645205)
              ·
                refine ⟨4771669374683379070952119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 101795613326578753513645205 4771669374683379070952119)
                ·
                  refine ⟨7157504062025068606428179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4771669374683379070952119 7157504062025068606428179)
                  ·
                    refine ⟨10736256093037602909642269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7157504062025068606428179 10736256093037602909642269)
                    ·
                      refine ⟨4026096034889101091115851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10736256093037602909642269 4026096034889101091115851)
                      ·
                        rfl

theorem cell23_7840794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_7840794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840794 prefixEnd_7840794 := by exact prefixLift 7840794
  have htrace : WordTrace (prefixWord ++ tailWord_7840794) baseStart_7840794 baseEnd_7840794 := by
    simpa [prefixWord, tailWord_7840794, baseEnd_7840794] using wordTrace_append hprefix tailTrace_7840794
  have hstable : (prefixWord ++ tailWord_7840794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840794).length < 2 ^ (prefixWord ++ tailWord_7840794).sum := by decide
  have hdescent : baseEnd_7840794 < baseStart_7840794 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840817 : List Nat := [1, 2, 2, 3, 1, 2, 4, 2, 1, 1, 4]
def baseStart_7840817 : Nat := 118140960795 + 7840817 * 2 ^ 59
def prefixEnd_7840817 : Nat := 4983230072969 + 3 ^ 40 * 7840817 * 2
def baseEnd_7840817 : Nat := 4026107844944154501128245

theorem tailTrace_7840817 : CollatzResearch.WordTrace tailWord_7840817 prefixEnd_7840817 4026107844944154501128245 := by
  unfold tailWord_7840817
  simp only [CollatzResearch.WordTrace]
  refine ⟨285978090035066588777120705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190652060023377725851413803 285978090035066588777120705)
  ·
    refine ⟨214483567526299941582840529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285978090035066588777120705 214483567526299941582840529)
    ·
      refine ⟨160862675644724956187130397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214483567526299941582840529 160862675644724956187130397)
      ·
        refine ⟨60323503366771858570173899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160862675644724956187130397 60323503366771858570173899)
        ·
          refine ⟨90485255050157787855260849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60323503366771858570173899 90485255050157787855260849)
          ·
            refine ⟨67863941287618340891445637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90485255050157787855260849 67863941287618340891445637)
            ·
              refine ⟨12724488991428438917146057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67863941287618340891445637 12724488991428438917146057)
              ·
                refine ⟨9543366743571329187859543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12724488991428438917146057 9543366743571329187859543)
                ·
                  refine ⟨14315050115356993781789315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9543366743571329187859543 14315050115356993781789315)
                  ·
                    refine ⟨21472575173035490672683973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14315050115356993781789315 21472575173035490672683973)
                    ·
                      refine ⟨4026107844944154501128245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21472575173035490672683973 4026107844944154501128245)
                      ·
                        rfl

theorem cell23_7840817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 4, 2, 1, 1, 4].length) (baseStart_7840817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840817 prefixEnd_7840817 := by exact prefixLift 7840817
  have htrace : WordTrace (prefixWord ++ tailWord_7840817) baseStart_7840817 baseEnd_7840817 := by
    simpa [prefixWord, tailWord_7840817, baseEnd_7840817] using wordTrace_append hprefix tailTrace_7840817
  have hstable : (prefixWord ++ tailWord_7840817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840817).length < 2 ^ (prefixWord ++ tailWord_7840817).sum := by decide
  have hdescent : baseEnd_7840817 < baseStart_7840817 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840837 : List Nat := [1, 3, 1, 1, 1, 3, 4, 3, 1, 2, 3]
def baseStart_7840837 : Nat := 118140960795 + 7840837 * 2 ^ 59
def prefixEnd_7840837 : Nat := 4983230072969 + 3 ^ 40 * 7840837 * 2
def baseEnd_7840837 : Nat := 4026118114557244422878153

theorem tailTrace_7840837 : CollatzResearch.WordTrace tailWord_7840837 prefixEnd_7840837 4026118114557244422878153 := by
  unfold tailWord_7840837
  simp only [CollatzResearch.WordTrace]
  refine ⟨285978819494994132192848765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190652546329996088128565843 285978819494994132192848765)
  ·
    refine ⟨107242057310622799572318287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285978819494994132192848765 107242057310622799572318287)
    ·
      refine ⟨160863085965934199358477431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107242057310622799572318287 160863085965934199358477431)
      ·
        refine ⟨241294628948901299037716147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160863085965934199358477431 241294628948901299037716147)
        ·
          refine ⟨361941943423351948556574221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241294628948901299037716147 361941943423351948556574221)
          ·
            refine ⟨135728228783756980708715333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361941943423351948556574221 135728228783756980708715333)
            ·
              refine ⟨25449042896954433882884125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135728228783756980708715333 25449042896954433882884125)
              ·
                refine ⟨9543391086357912706081547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25449042896954433882884125 9543391086357912706081547)
                ·
                  refine ⟨14315086629536869059122321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9543391086357912706081547 14315086629536869059122321)
                  ·
                    refine ⟨10736314972152651794341741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14315086629536869059122321 10736314972152651794341741)
                    ·
                      refine ⟨4026118114557244422878153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10736314972152651794341741 4026118114557244422878153)
                      ·
                        rfl

theorem cell23_7840837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 1, 2, 3].length) (baseStart_7840837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840837 prefixEnd_7840837 := by exact prefixLift 7840837
  have htrace : WordTrace (prefixWord ++ tailWord_7840837) baseStart_7840837 baseEnd_7840837 := by
    simpa [prefixWord, tailWord_7840837, baseEnd_7840837] using wordTrace_append hprefix tailTrace_7840837
  have hstable : (prefixWord ++ tailWord_7840837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840837).length < 2 ^ (prefixWord ++ tailWord_7840837).sum := by decide
  have hdescent : baseEnd_7840837 < baseStart_7840837 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840843 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 6]
def baseStart_7840843 : Nat := 118140960795 + 7840843 * 2 ^ 59
def prefixEnd_7840843 : Nat := 4983230072969 + 3 ^ 40 * 7840843 * 2
def baseEnd_7840843 : Nat := 4026121195441171399403125

theorem tailTrace_7840843 : CollatzResearch.WordTrace tailWord_7840843 prefixEnd_7840843 4026121195441171399403125 := by
  unfold tailWord_7840843
  simp only [CollatzResearch.WordTrace]
  refine ⟨285979038332972395217567183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190652692221981596811711455 285979038332972395217567183)
  ·
    refine ⟨428968557499458592826350775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285979038332972395217567183 428968557499458592826350775)
    ·
      refine ⟨643452836249187889239526163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428968557499458592826350775 643452836249187889239526163)
      ·
        refine ⟨965179254373781833859289245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643452836249187889239526163 965179254373781833859289245)
        ·
          refine ⟨361942220390168187697233467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 965179254373781833859289245 361942220390168187697233467)
          ·
            refine ⟨542913330585252281545850201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361942220390168187697233467 542913330585252281545850201)
            ·
              refine ⟨407184997938939211159387651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542913330585252281545850201 407184997938939211159387651)
              ·
                refine ⟨610777496908408816739081477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407184997938939211159387651 610777496908408816739081477)
                ·
                  refine ⟨114520780670326653138577777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 610777496908408816739081477 114520780670326653138577777)
                  ·
                    refine ⟨85890585502744989853933333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114520780670326653138577777 85890585502744989853933333)
                    ·
                      refine ⟨4026121195441171399403125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85890585502744989853933333 4026121195441171399403125)
                      ·
                        rfl

theorem cell23_7840843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 4, 2, 6].length) (baseStart_7840843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840843 prefixEnd_7840843 := by exact prefixLift 7840843
  have htrace : WordTrace (prefixWord ++ tailWord_7840843) baseStart_7840843 baseEnd_7840843 := by
    simpa [prefixWord, tailWord_7840843, baseEnd_7840843] using wordTrace_append hprefix tailTrace_7840843
  have hstable : (prefixWord ++ tailWord_7840843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840843).length < 2 ^ (prefixWord ++ tailWord_7840843).sum := by decide
  have hdescent : baseEnd_7840843 < baseStart_7840843 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840860 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 2, 2, 6]
def baseStart_7840860 : Nat := 118140960795 + 7840860 * 2 ^ 59
def prefixEnd_7840860 : Nat := 4983230072969 + 3 ^ 40 * 7840860 * 2
def baseEnd_7840860 : Nat := 4026129924612297832890547

theorem tailTrace_7840860 : CollatzResearch.WordTrace tailWord_7840860 prefixEnd_7840860 4026129924612297832890547 := by
  unfold tailWord_7840860
  simp only [CollatzResearch.WordTrace]
  refine ⟨142989829186955403560468017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190653105582607204747290689 142989829186955403560468017)
  ·
    refine ⟨107242371890216552670351013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142989829186955403560468017 107242371890216552670351013)
    ·
      refine ⟨20107944729415603625690815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107242371890216552670351013 20107944729415603625690815)
      ·
        refine ⟨30161917094123405438536223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20107944729415603625690815 30161917094123405438536223)
        ·
          refine ⟨45242875641185108157804335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30161917094123405438536223 45242875641185108157804335)
          ·
            refine ⟨67864313461777662236706503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45242875641185108157804335 67864313461777662236706503)
            ·
              refine ⟨101796470192666493355059755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67864313461777662236706503 101796470192666493355059755)
              ·
                refine ⟨152694705288999740032589633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101796470192666493355059755 152694705288999740032589633)
                ·
                  refine ⟨114521028966749805024442225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152694705288999740032589633 114521028966749805024442225)
                  ·
                    refine ⟨85890771725062353768331669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114521028966749805024442225 85890771725062353768331669)
                    ·
                      refine ⟨4026129924612297832890547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85890771725062353768331669 4026129924612297832890547)
                      ·
                        rfl

theorem cell23_7840860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_7840860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840860 prefixEnd_7840860 := by exact prefixLift 7840860
  have htrace : WordTrace (prefixWord ++ tailWord_7840860) baseStart_7840860 baseEnd_7840860 := by
    simpa [prefixWord, tailWord_7840860, baseEnd_7840860] using wordTrace_append hprefix tailTrace_7840860
  have hstable : (prefixWord ++ tailWord_7840860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840860).length < 2 ^ (prefixWord ++ tailWord_7840860).sum := by decide
  have hdescent : baseEnd_7840860 < baseStart_7840860 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840861 : List Nat := [1, 4, 4, 1, 2, 1, 1, 3, 2, 4]
def baseStart_7840861 : Nat := 118140960795 + 7840861 * 2 ^ 59
def prefixEnd_7840861 : Nat := 4983230072969 + 3 ^ 40 * 7840861 * 2
def baseEnd_7840861 : Nat := 1342043479364317442992681

theorem tailTrace_7840861 : CollatzResearch.WordTrace tailWord_7840861 prefixEnd_7840861 1342043479364317442992681 := by
  unfold tailWord_7840861
  simp only [CollatzResearch.WordTrace]
  refine ⟨285979694846907184291722437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190653129897938122861148291 285979694846907184291722437)
  ·
    refine ⟨53621192783795097054697957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285979694846907184291722437 53621192783795097054697957)
    ·
      refine ⟨10053973646961580697755867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 53621192783795097054697957 10053973646961580697755867)
      ·
        refine ⟨15080960470442371046633801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10053973646961580697755867 15080960470442371046633801)
        ·
          refine ⟨11310720352831778284975351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15080960470442371046633801 11310720352831778284975351)
          ·
            refine ⟨16966080529247667427463027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11310720352831778284975351 16966080529247667427463027)
            ·
              refine ⟨25449120793871501141194541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16966080529247667427463027 25449120793871501141194541)
              ·
                refine ⟨9543420297701812927947953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25449120793871501141194541 9543420297701812927947953)
                ·
                  refine ⟨7157565223276359695960965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9543420297701812927947953 7157565223276359695960965)
                  ·
                    refine ⟨1342043479364317442992681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7157565223276359695960965 1342043479364317442992681)
                    ·
                      rfl

theorem cell23_7840861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_7840861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840861 prefixEnd_7840861 := by exact prefixLift 7840861
  have htrace : WordTrace (prefixWord ++ tailWord_7840861) baseStart_7840861 baseEnd_7840861 := by
    simpa [prefixWord, tailWord_7840861, baseEnd_7840861] using wordTrace_append hprefix tailTrace_7840861
  have hstable : (prefixWord ++ tailWord_7840861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840861).length < 2 ^ (prefixWord ++ tailWord_7840861).sum := by decide
  have hdescent : baseEnd_7840861 < baseStart_7840861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840901 : List Nat := [1, 3, 1, 1, 6, 1, 2, 2, 2, 1, 3]
def baseStart_7840901 : Nat := 118140960795 + 7840901 * 2 ^ 59
def prefixEnd_7840901 : Nat := 4983230072969 + 3 ^ 40 * 7840901 * 2
def baseEnd_7840901 : Nat := 4026150977319132172477859

theorem tailTrace_7840901 : CollatzResearch.WordTrace tailWord_7840901 prefixEnd_7840901 4026150977319132172477859 := by
  unfold tailWord_7840901
  simp only [CollatzResearch.WordTrace]
  refine ⟨285981153766762271123178557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190654102511174847415452371 285981153766762271123178557)
  ·
    refine ⟨107242932662535851671191959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285981153766762271123178557 107242932662535851671191959)
    ·
      refine ⟨160864398993803777506787939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107242932662535851671191959 160864398993803777506787939)
      ·
        refine ⟨241296598490705666260181909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160864398993803777506787939 241296598490705666260181909)
        ·
          refine ⟨11310778054251828105946027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 241296598490705666260181909 11310778054251828105946027)
          ·
            refine ⟨16966167081377742158919041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11310778054251828105946027 16966167081377742158919041)
            ·
              refine ⟨12724625311033306619189281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16966167081377742158919041 12724625311033306619189281)
              ·
                refine ⟨9543468983274979964391961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12724625311033306619189281 9543468983274979964391961)
                ·
                  refine ⟨7157601737456234973293971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9543468983274979964391961 7157601737456234973293971)
                  ·
                    refine ⟨10736402606184352459940957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7157601737456234973293971 10736402606184352459940957)
                    ·
                      refine ⟨4026150977319132172477859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10736402606184352459940957 4026150977319132172477859)
                      ·
                        rfl

theorem cell23_7840901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 2, 2, 2, 1, 3].length) (baseStart_7840901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840901 prefixEnd_7840901 := by exact prefixLift 7840901
  have htrace : WordTrace (prefixWord ++ tailWord_7840901) baseStart_7840901 baseEnd_7840901 := by
    simpa [prefixWord, tailWord_7840901, baseEnd_7840901] using wordTrace_append hprefix tailTrace_7840901
  have hstable : (prefixWord ++ tailWord_7840901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840901).length < 2 ^ (prefixWord ++ tailWord_7840901).sum := by decide
  have hdescent : baseEnd_7840901 < baseStart_7840901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840924 : List Nat := [2, 2, 3, 2, 1, 2, 1, 3, 1, 4, 2]
def baseStart_7840924 : Nat := 118140960795 + 7840924 * 2 ^ 59
def prefixEnd_7840924 : Nat := 4983230072969 + 3 ^ 40 * 7840924 * 2
def baseEnd_7840924 : Nat := 4026162787374185582490253

theorem tailTrace_7840924 : CollatzResearch.WordTrace tailWord_7840924 prefixEnd_7840924 4026162787374185582490253 := by
  unfold tailWord_7840924
  simp only [CollatzResearch.WordTrace]
  refine ⟨142990996322839473025632913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190654661763785964034177217 142990996322839473025632913)
  ·
    refine ⟨107243247242129604769224685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142990996322839473025632913 107243247242129604769224685)
    ·
      refine ⟨40216217715798601788459257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107243247242129604769224685 40216217715798601788459257)
      ·
        refine ⟨30162163286848951341344443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40216217715798601788459257 30162163286848951341344443)
        ·
          refine ⟨45243244930273427012016665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30162163286848951341344443 45243244930273427012016665)
          ·
            refine ⟨33932433697705070259012499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45243244930273427012016665 33932433697705070259012499)
            ·
              refine ⟨50898650546557605388518749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33932433697705070259012499 50898650546557605388518749)
              ·
                refine ⟨19086993954959102020694531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50898650546557605388518749 19086993954959102020694531)
                ·
                  refine ⟨28630490932438653031041797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19086993954959102020694531 28630490932438653031041797)
                  ·
                    refine ⟨5368217049832247443320337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28630490932438653031041797 5368217049832247443320337)
                    ·
                      refine ⟨4026162787374185582490253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368217049832247443320337 4026162787374185582490253)
                      ·
                        rfl

theorem cell23_7840924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_7840924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840924 prefixEnd_7840924 := by exact prefixLift 7840924
  have htrace : WordTrace (prefixWord ++ tailWord_7840924) baseStart_7840924 baseEnd_7840924 := by
    simpa [prefixWord, tailWord_7840924, baseEnd_7840924] using wordTrace_append hprefix tailTrace_7840924
  have hstable : (prefixWord ++ tailWord_7840924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840924).length < 2 ^ (prefixWord ++ tailWord_7840924).sum := by decide
  have hdescent : baseEnd_7840924 < baseStart_7840924 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840947 : List Nat := [1, 1, 1, 2, 3, 2, 3, 5, 5]
def baseStart_7840947 : Nat := 118140960795 + 7840947 * 2 ^ 59
def prefixEnd_7840947 : Nat := 4983230072969 + 3 ^ 40 * 7840947 * 2
def baseEnd_7840947 : Nat := 447352733047693221389183

theorem tailTrace_7840947 : CollatzResearch.WordTrace tailWord_7840947 prefixEnd_7840947 447352733047693221389183 := by
  unfold tailWord_7840947
  simp only [CollatzResearch.WordTrace]
  refine ⟨285982831524595620979353095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190655221016397080652902063 285982831524595620979353095)
  ·
    refine ⟨428974247286893431469029643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285982831524595620979353095 428974247286893431469029643)
    ·
      refine ⟨643461370930340147203544465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 428974247286893431469029643 643461370930340147203544465)
      ·
        refine ⟨482596028197755110402658349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643461370930340147203544465 482596028197755110402658349)
        ·
          refine ⟨180973510574158166400996881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482596028197755110402658349 180973510574158166400996881)
          ·
            refine ⟨135730132930618624800747661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180973510574158166400996881 135730132930618624800747661)
            ·
              refine ⟨50898799848981984300280373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135730132930618624800747661 50898799848981984300280373)
              ·
                refine ⟨4771762485842061028151285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50898799848981984300280373 4771762485842061028151285)
                ·
                  refine ⟨447352733047693221389183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4771762485842061028151285 447352733047693221389183)
                  ·
                    rfl

theorem cell23_7840947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5, 5].length) (baseStart_7840947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840947 prefixEnd_7840947 := by exact prefixLift 7840947
  have htrace : WordTrace (prefixWord ++ tailWord_7840947) baseStart_7840947 baseEnd_7840947 := by
    simpa [prefixWord, tailWord_7840947, baseEnd_7840947] using wordTrace_append hprefix tailTrace_7840947
  have hstable : (prefixWord ++ tailWord_7840947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840947).length < 2 ^ (prefixWord ++ tailWord_7840947).sum := by decide
  have hdescent : baseEnd_7840947 < baseStart_7840947 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840957 : List Nat := [1, 4, 1, 2, 1, 1, 3, 2, 2, 3, 3]
def baseStart_7840957 : Nat := 118140960795 + 7840957 * 2 ^ 59
def prefixEnd_7840957 : Nat := 4983230072969 + 3 ^ 40 * 7840957 * 2
def baseEnd_7840957 : Nat := 4026179732235783953377601

theorem tailTrace_7840957 : CollatzResearch.WordTrace tailWord_7840957 prefixEnd_7840957 4026179732235783953377601 := by
  unfold tailWord_7840957
  simp only [CollatzResearch.WordTrace]
  refine ⟨285983196254559392687217125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190655464169706261791478083 285983196254559392687217125)
  ·
    refine ⟨53621849297729886128853211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285983196254559392687217125 53621849297729886128853211)
    ·
      refine ⟨80432773946594829193279817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53621849297729886128853211 80432773946594829193279817)
      ·
        refine ⟨60324580459946121894959863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80432773946594829193279817 60324580459946121894959863)
        ·
          refine ⟨90486870689919182842439795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60324580459946121894959863 90486870689919182842439795)
          ·
            refine ⟨135730306034878774263659693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90486870689919182842439795 135730306034878774263659693)
            ·
              refine ⟨50898864763079540348872385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135730306034878774263659693 50898864763079540348872385)
              ·
                refine ⟨38174148572309655261654289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50898864763079540348872385 38174148572309655261654289)
                ·
                  refine ⟨28630611429232241446240717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38174148572309655261654289 28630611429232241446240717)
                  ·
                    refine ⟨10736479285962090542340269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28630611429232241446240717 10736479285962090542340269)
                    ·
                      refine ⟨4026179732235783953377601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10736479285962090542340269 4026179732235783953377601)
                      ·
                        rfl

theorem cell23_7840957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 3, 3].length) (baseStart_7840957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840957 prefixEnd_7840957 := by exact prefixLift 7840957
  have htrace : WordTrace (prefixWord ++ tailWord_7840957) baseStart_7840957 baseEnd_7840957 := by
    simpa [prefixWord, tailWord_7840957, baseEnd_7840957] using wordTrace_append hprefix tailTrace_7840957
  have hstable : (prefixWord ++ tailWord_7840957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840957).length < 2 ^ (prefixWord ++ tailWord_7840957).sum := by decide
  have hdescent : baseEnd_7840957 < baseStart_7840957 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840958 : List Nat := [4, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_7840958 : Nat := 118140960795 + 7840958 * 2 ^ 59
def prefixEnd_7840958 : Nat := 4983230072969 + 3 ^ 40 * 7840958 * 2
def baseEnd_7840958 : Nat := 4026180245716438449465097

theorem tailTrace_7840958 : CollatzResearch.WordTrace tailWord_7840958 prefixEnd_7840958 4026180245716438449465097 := by
  unfold tailWord_7840958
  simp only [CollatzResearch.WordTrace]
  refine ⟨35747904090944471232250441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190655488485037179905335685 35747904090944471232250441)
  ·
    refine ⟨26810928068208353424187831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 35747904090944471232250441 26810928068208353424187831)
    ·
      refine ⟨40216392102312530136281747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26810928068208353424187831 40216392102312530136281747)
      ·
        refine ⟨60324588153468795204422621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40216392102312530136281747 60324588153468795204422621)
        ·
          refine ⟨22621720557550798201658483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60324588153468795204422621 22621720557550798201658483)
          ·
            refine ⟨33932580836326197302487725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22621720557550798201658483 33932580836326197302487725)
            ·
              refine ⟨12724717813622323988432897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33932580836326197302487725 12724717813622323988432897)
              ·
                refine ⟨9543538360216742991324673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12724717813622323988432897 9543538360216742991324673)
                ·
                  refine ⟨7157653770162557243493505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9543538360216742991324673 7157653770162557243493505)
                  ·
                    refine ⟨5368240327621917932620129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7157653770162557243493505 5368240327621917932620129)
                    ·
                      refine ⟨4026180245716438449465097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368240327621917932620129 4026180245716438449465097)
                      ·
                        rfl

theorem cell23_7840958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_7840958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840958 prefixEnd_7840958 := by exact prefixLift 7840958
  have htrace : WordTrace (prefixWord ++ tailWord_7840958) baseStart_7840958 baseEnd_7840958 := by
    simpa [prefixWord, tailWord_7840958, baseEnd_7840958] using wordTrace_append hprefix tailTrace_7840958
  have hstable : (prefixWord ++ tailWord_7840958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840958).length < 2 ^ (prefixWord ++ tailWord_7840958).sum := by decide
  have hdescent : baseEnd_7840958 < baseStart_7840958 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840964 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 7]
def baseStart_7840964 : Nat := 118140960795 + 7840964 * 2 ^ 59
def prefixEnd_7840964 : Nat := 4983230072969 + 3 ^ 40 * 7840964 * 2
def baseEnd_7840964 : Nat := 447353702955596158443341

theorem tailTrace_7840964 : CollatzResearch.WordTrace tailWord_7840964 prefixEnd_7840964 447353702955596158443341 := by
  unfold tailWord_7840964
  simp only [CollatzResearch.WordTrace]
  refine ⟨142991725782767016441360973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190655634377022688588481297 142991725782767016441360973)
  ·
    refine ⟨53621897168537631165510365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 142991725782767016441360973 53621897168537631165510365)
    ·
      refine ⟨20108211438201611687066387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53621897168537631165510365 20108211438201611687066387)
      ·
        refine ⟨30162317157302417530599581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20108211438201611687066387 30162317157302417530599581)
        ·
          refine ⟨11310868933988406573974843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30162317157302417530599581 11310868933988406573974843)
          ·
            refine ⟨16966303400982609860962265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11310868933988406573974843 16966303400982609860962265)
            ·
              refine ⟨12724727550736957395721699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16966303400982609860962265 12724727550736957395721699)
              ·
                refine ⟨19087091326105436093582549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12724727550736957395721699 19087091326105436093582549)
                ·
                  refine ⟨447353702955596158443341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19087091326105436093582549 447353702955596158443341)
                  ·
                    rfl

theorem cell23_7840964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 7].length) (baseStart_7840964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840964 prefixEnd_7840964 := by exact prefixLift 7840964
  have htrace : WordTrace (prefixWord ++ tailWord_7840964) baseStart_7840964 baseEnd_7840964 := by
    simpa [prefixWord, tailWord_7840964, baseEnd_7840964] using wordTrace_append hprefix tailTrace_7840964
  have hstable : (prefixWord ++ tailWord_7840964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840964).length < 2 ^ (prefixWord ++ tailWord_7840964).sum := by decide
  have hdescent : baseEnd_7840964 < baseStart_7840964 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7840967 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 1, 7, 2]
def baseStart_7840967 : Nat := 118140960795 + 7840967 * 2 ^ 59
def prefixEnd_7840967 : Nat := 4983230072969 + 3 ^ 40 * 7840967 * 2
def baseEnd_7840967 : Nat := 4026184867042328914252555

theorem tailTrace_7840967 : CollatzResearch.WordTrace tailWord_7840967 prefixEnd_7840967 4026184867042328914252555 := by
  unfold tailWord_7840967
  simp only [CollatzResearch.WordTrace]
  refine ⟨285983560984523164395081155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190655707323015442930054103 285983560984523164395081155)
  ·
    refine ⟨428975341476784746592621733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285983560984523164395081155 428975341476784746592621733)
    ·
      refine ⟨80432876526897139986116575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 428975341476784746592621733 80432876526897139986116575)
      ·
        refine ⟨120649314790345709979174863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80432876526897139986116575 120649314790345709979174863)
        ·
          refine ⟨180973972185518564968762295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120649314790345709979174863 180973972185518564968762295)
          ·
            refine ⟨271460958278277847453143443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180973972185518564968762295 271460958278277847453143443)
            ·
              refine ⟨407191437417416771179715165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271460958278277847453143443 407191437417416771179715165)
              ·
                refine ⟨152696789031531289192393187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407191437417416771179715165 152696789031531289192393187)
                ·
                  refine ⟨229045183547296933788589781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 152696789031531289192393187 229045183547296933788589781)
                  ·
                    refine ⟨5368246489389771885670073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 229045183547296933788589781 5368246489389771885670073)
                    ·
                      refine ⟨4026184867042328914252555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368246489389771885670073 4026184867042328914252555)
                      ·
                        rfl

theorem cell23_7840967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 7, 2].length) (baseStart_7840967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7840967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7840967 prefixEnd_7840967 := by exact prefixLift 7840967
  have htrace : WordTrace (prefixWord ++ tailWord_7840967) baseStart_7840967 baseEnd_7840967 := by
    simpa [prefixWord, tailWord_7840967, baseEnd_7840967] using wordTrace_append hprefix tailTrace_7840967
  have hstable : (prefixWord ++ tailWord_7840967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7840967).length < 2 ^ (prefixWord ++ tailWord_7840967).sum := by decide
  have hdescent : baseEnd_7840967 < baseStart_7840967 := by decide
  rcases family_descends (prefixWord ++ tailWord_7840967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841040 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 8]
def baseStart_7841040 : Nat := 118140960795 + 7841040 * 2 ^ 59
def prefixEnd_7841040 : Nat := 4983230072969 + 3 ^ 40 * 7841040 * 2
def baseEnd_7841040 : Nat := 4026222351130107128639719

theorem tailTrace_7841040 : CollatzResearch.WordTrace tailWord_7841040 prefixEnd_7841040 4026222351130107128639719 := by
  unfold tailWord_7841040
  simp only [CollatzResearch.WordTrace]
  refine ⟨142993111756629348931244287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190657482342172465241659049 142993111756629348931244287)
  ·
    refine ⟨214489667634944023396866431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142993111756629348931244287 214489667634944023396866431)
    ·
      refine ⟨321734501452416035095299647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214489667634944023396866431 321734501452416035095299647)
      ·
        refine ⟨482601752178624052642949471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321734501452416035095299647 482601752178624052642949471)
        ·
          refine ⟨723902628267936078964424207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482601752178624052642949471 723902628267936078964424207)
          ·
            refine ⟨1085853942401904118446636311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723902628267936078964424207 1085853942401904118446636311)
            ·
              refine ⟨1628780913602856177669954467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085853942401904118446636311 1628780913602856177669954467)
              ·
                refine ⟨2443171370404284266504931701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1628780913602856177669954467 2443171370404284266504931701)
                ·
                  refine ⟨229047315975401649984837347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2443171370404284266504931701 229047315975401649984837347)
                  ·
                    refine ⟨343570973963102474977256021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 229047315975401649984837347 343570973963102474977256021)
                    ·
                      refine ⟨4026222351130107128639719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 343570973963102474977256021 4026222351130107128639719)
                      ·
                        rfl

theorem cell23_7841040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 8].length) (baseStart_7841040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841040 prefixEnd_7841040 := by exact prefixLift 7841040
  have htrace : WordTrace (prefixWord ++ tailWord_7841040) baseStart_7841040 baseEnd_7841040 := by
    simpa [prefixWord, tailWord_7841040, baseEnd_7841040] using wordTrace_append hprefix tailTrace_7841040
  have hstable : (prefixWord ++ tailWord_7841040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841040).length < 2 ^ (prefixWord ++ tailWord_7841040).sum := by decide
  have hdescent : baseEnd_7841040 < baseStart_7841040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841097 : List Nat := [1, 2, 1, 1, 2, 3, 3, 3, 1, 6]
def baseStart_7841097 : Nat := 118140960795 + 7841097 * 2 ^ 59
def prefixEnd_7841097 : Nat := 4983230072969 + 3 ^ 40 * 7841097 * 2
def baseEnd_7841097 : Nat := 1342083873175804468542319

theorem tailTrace_7841097 : CollatzResearch.WordTrace tailWord_7841097 prefixEnd_7841097 1342083873175804468542319 := by
  unfold tailWord_7841097
  simp only [CollatzResearch.WordTrace]
  refine ⟨285988302474052196597313545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190658868316034797731542363 285988302474052196597313545)
  ·
    refine ⟨214491226855539147447985159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285988302474052196597313545 214491226855539147447985159)
    ·
      refine ⟨321736840283308721171977739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214491226855539147447985159 321736840283308721171977739)
      ·
        refine ⟨482605260424963081757966609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321736840283308721171977739 482605260424963081757966609)
        ·
          refine ⟨361953945318722311318474957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482605260424963081757966609 361953945318722311318474957)
          ·
            refine ⟨135732729494520866744428109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361953945318722311318474957 135732729494520866744428109)
            ·
              refine ⟨50899773560445325029160541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135732729494520866744428109 50899773560445325029160541)
              ·
                refine ⟨19087415085166996885935203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50899773560445325029160541 19087415085166996885935203)
                ·
                  refine ⟨28631122627750495328902805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19087415085166996885935203 28631122627750495328902805)
                  ·
                    refine ⟨1342083873175804468542319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28631122627750495328902805 1342083873175804468542319)
                    ·
                      rfl

theorem cell23_7841097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 6].length) (baseStart_7841097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841097 prefixEnd_7841097 := by exact prefixLift 7841097
  have htrace : WordTrace (prefixWord ++ tailWord_7841097) baseStart_7841097 baseEnd_7841097 := by
    simpa [prefixWord, tailWord_7841097, baseEnd_7841097] using wordTrace_append hprefix tailTrace_7841097
  have hstable : (prefixWord ++ tailWord_7841097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841097).length < 2 ^ (prefixWord ++ tailWord_7841097).sum := by decide
  have hdescent : baseEnd_7841097 < baseStart_7841097 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841104 : List Nat := [2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 4]
def baseStart_7841104 : Nat := 118140960795 + 7841104 * 2 ^ 59
def prefixEnd_7841104 : Nat := 4983230072969 + 3 ^ 40 * 7841104 * 2
def baseEnd_7841104 : Nat := 4026255213891994878239425

theorem tailTrace_7841104 : CollatzResearch.WordTrace tailWord_7841104 prefixEnd_7841104 4026255213891994878239425 := by
  unfold tailWord_7841104
  simp only [CollatzResearch.WordTrace]
  refine ⟨142994278892513418396409183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190659038523351224528545577 142994278892513418396409183)
  ·
    refine ⟨214491418338770127594613775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 142994278892513418396409183 214491418338770127594613775)
    ·
      refine ⟨321737127508155191391920663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214491418338770127594613775 321737127508155191391920663)
      ·
        refine ⟨482605691262232787087880995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321737127508155191391920663 482605691262232787087880995)
        ·
          refine ⟨723908536893349180631821493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482605691262232787087880995 723908536893349180631821493)
          ·
            refine ⟨67866425333751485684233265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 723908536893349180631821493 67866425333751485684233265)
            ·
              refine ⟨50899819000313614263174949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67866425333751485684233265 50899819000313614263174949)
              ·
                refine ⟨9543716062558802674345303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50899819000313614263174949 9543716062558802674345303)
                ·
                  refine ⟨14315574093838204011517955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9543716062558802674345303 14315574093838204011517955)
                  ·
                    refine ⟨21473361140757306017276933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14315574093838204011517955 21473361140757306017276933)
                    ·
                      refine ⟨4026255213891994878239425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21473361140757306017276933 4026255213891994878239425)
                      ·
                        rfl

theorem cell23_7841104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 4].length) (baseStart_7841104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841104 prefixEnd_7841104 := by exact prefixLift 7841104
  have htrace : WordTrace (prefixWord ++ tailWord_7841104) baseStart_7841104 baseEnd_7841104 := by
    simpa [prefixWord, tailWord_7841104, baseEnd_7841104] using wordTrace_append hprefix tailTrace_7841104
  have hstable : (prefixWord ++ tailWord_7841104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841104).length < 2 ^ (prefixWord ++ tailWord_7841104).sum := by decide
  have hdescent : baseEnd_7841104 < baseStart_7841104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841138 : List Nat := [3, 2, 1, 2, 1, 2, 4, 1, 3, 2, 2]
def baseStart_7841138 : Nat := 118140960795 + 7841138 * 2 ^ 59
def prefixEnd_7841138 : Nat := 4983230072969 + 3 ^ 40 * 7841138 * 2
def baseEnd_7841138 : Nat := 4026272672234247745214269

theorem tailTrace_7841138 : CollatzResearch.WordTrace tailWord_7841138 prefixEnd_7841138 4026272672234247745214269 := by
  unfold tailWord_7841138
  simp only [CollatzResearch.WordTrace]
  refine ⟨71497449466725915149889017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190659865244602440399704045 71497449466725915149889017)
  ·
    refine ⟨53623087100044436362416763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71497449466725915149889017 53623087100044436362416763)
    ·
      refine ⟨80434630650066654543625145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53623087100044436362416763 80434630650066654543625145)
      ·
        refine ⟨60325972987549990907718859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80434630650066654543625145 60325972987549990907718859)
        ·
          refine ⟨90488959481324986361578289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60325972987549990907718859 90488959481324986361578289)
          ·
            refine ⟨67866719610993739771183717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90488959481324986361578289 67866719610993739771183717)
            ·
              refine ⟨12725009927061326207096947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 67866719610993739771183717 12725009927061326207096947)
              ·
                refine ⟨19087514890591989310645421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12725009927061326207096947 19087514890591989310645421)
                ·
                  refine ⟨7157818083971995991492033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19087514890591989310645421 7157818083971995991492033)
                  ·
                    refine ⟨5368363562978996993619025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7157818083971995991492033 5368363562978996993619025)
                    ·
                      refine ⟨4026272672234247745214269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368363562978996993619025 4026272672234247745214269)
                      ·
                        rfl

theorem cell23_7841138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_7841138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841138 prefixEnd_7841138 := by exact prefixLift 7841138
  have htrace : WordTrace (prefixWord ++ tailWord_7841138) baseStart_7841138 baseEnd_7841138 := by
    simpa [prefixWord, tailWord_7841138, baseEnd_7841138] using wordTrace_append hprefix tailTrace_7841138
  have hstable : (prefixWord ++ tailWord_7841138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841138).length < 2 ^ (prefixWord ++ tailWord_7841138).sum := by decide
  have hdescent : baseEnd_7841138 < baseStart_7841138 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841141 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_7841141 : Nat := 118140960795 + 7841141 * 2 ^ 59
def prefixEnd_7841141 : Nat := 4983230072969 + 3 ^ 40 * 7841141 * 2
def baseEnd_7841141 : Nat := 4026274212676211233476755

theorem tailTrace_7841141 : CollatzResearch.WordTrace tailWord_7841141 prefixEnd_7841141 4026274212676211233476755 := by
  unfold tailWord_7841141
  simp only [CollatzResearch.WordTrace]
  refine ⟨285989907285892792111915277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190659938190595194741276851 285989907285892792111915277)
  ·
    refine ⟨107246215232209797041968229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285989907285892792111915277 107246215232209797041968229)
    ·
      refine ⟨20108665356039336945369043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 107246215232209797041968229 20108665356039336945369043)
      ·
        refine ⟨30162998034059005418053565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20108665356039336945369043 30162998034059005418053565)
        ·
          refine ⟨11311124262772127031770087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30162998034059005418053565 11311124262772127031770087)
          ·
            refine ⟨16966686394158190547655131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311124262772127031770087 16966686394158190547655131)
            ·
              refine ⟨25450029591237285821482697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16966686394158190547655131 25450029591237285821482697)
              ·
                refine ⟨19087522193427964366112023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25450029591237285821482697 19087522193427964366112023)
                ·
                  refine ⟨28631283290141946549168035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19087522193427964366112023 28631283290141946549168035)
                  ·
                    refine ⟨42946924935212919823752053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28631283290141946549168035 42946924935212919823752053)
                    ·
                      refine ⟨4026274212676211233476755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42946924935212919823752053 4026274212676211233476755)
                      ·
                        rfl

theorem cell23_7841141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_7841141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841141 prefixEnd_7841141 := by exact prefixLift 7841141
  have htrace : WordTrace (prefixWord ++ tailWord_7841141) baseStart_7841141 baseEnd_7841141 := by
    simpa [prefixWord, tailWord_7841141, baseEnd_7841141] using wordTrace_append hprefix tailTrace_7841141
  have hstable : (prefixWord ++ tailWord_7841141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841141).length < 2 ^ (prefixWord ++ tailWord_7841141).sum := by decide
  have hdescent : baseEnd_7841141 < baseStart_7841141 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841157 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 2, 7]
def baseStart_7841157 : Nat := 118140960795 + 7841157 * 2 ^ 59
def prefixEnd_7841157 : Nat := 4983230072969 + 3 ^ 40 * 7841157 * 2
def baseEnd_7841157 : Nat := 1342094142788894390292227

theorem tailTrace_7841157 : CollatzResearch.WordTrace tailWord_7841157 prefixEnd_7841157 1342094142788894390292227 := by
  unfold tailWord_7841157
  simp only [CollatzResearch.WordTrace]
  refine ⟨285990490853834826844497725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190660327235889884562998483 285990490853834826844497725)
  ·
    refine ⟨107246434070188060066686647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285990490853834826844497725 107246434070188060066686647)
    ·
      refine ⟨160869651105282090100029971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107246434070188060066686647 160869651105282090100029971)
      ·
        refine ⟨241304476657923135150044957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160869651105282090100029971 241304476657923135150044957)
        ·
          refine ⟨90489178746721175681266859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241304476657923135150044957 90489178746721175681266859)
          ·
            refine ⟨135733768120081763521900289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90489178746721175681266859 135733768120081763521900289)
            ·
              refine ⟨101800326090061322641425217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135733768120081763521900289 101800326090061322641425217)
              ·
                refine ⟨76350244567545991981068913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 101800326090061322641425217 76350244567545991981068913)
                ·
                  refine ⟨57262683425659493985801685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 76350244567545991981068913 57262683425659493985801685)
                  ·
                    refine ⟨1342094142788894390292227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57262683425659493985801685 1342094142788894390292227)
                    ·
                      rfl

theorem cell23_7841157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 7].length) (baseStart_7841157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841157 prefixEnd_7841157 := by exact prefixLift 7841157
  have htrace : WordTrace (prefixWord ++ tailWord_7841157) baseStart_7841157 baseEnd_7841157 := by
    simpa [prefixWord, tailWord_7841157, baseEnd_7841157] using wordTrace_append hprefix tailTrace_7841157
  have hstable : (prefixWord ++ tailWord_7841157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841157).length < 2 ^ (prefixWord ++ tailWord_7841157).sum := by decide
  have hdescent : baseEnd_7841157 < baseStart_7841157 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841161 : List Nat := [1, 2, 1, 1, 7, 2, 2, 7]
def baseStart_7841161 : Nat := 118140960795 + 7841161 * 2 ^ 59
def prefixEnd_7841161 : Nat := 4983230072969 + 3 ^ 40 * 7841161 * 2
def baseEnd_7841161 : Nat := 149121647492196339082469

theorem tailTrace_7841161 : CollatzResearch.WordTrace tailWord_7841161 prefixEnd_7841161 149121647492196339082469 := by
  unfold tailWord_7841161
  simp only [CollatzResearch.WordTrace]
  refine ⟨285990636745820335527643337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190660424497213557018428891 285990636745820335527643337)
  ·
    refine ⟨214492977559365251645732503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285990636745820335527643337 214492977559365251645732503)
    ·
      refine ⟨321739466339047877468598755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214492977559365251645732503 321739466339047877468598755)
      ·
        refine ⟨482609199508571816202898133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321739466339047877468598755 482609199508571816202898133)
        ·
          refine ⟨11311153113482151942255425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 482609199508571816202898133 11311153113482151942255425)
          ·
            refine ⟨8483364835111613956691569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11311153113482151942255425 8483364835111613956691569)
            ·
              refine ⟨6362523626333710467518677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8483364835111613956691569 6362523626333710467518677)
              ·
                refine ⟨149121647492196339082469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6362523626333710467518677 149121647492196339082469)
                ·
                  rfl

theorem cell23_7841161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 7].length) (baseStart_7841161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841161 prefixEnd_7841161 := by exact prefixLift 7841161
  have htrace : WordTrace (prefixWord ++ tailWord_7841161) baseStart_7841161 baseEnd_7841161 := by
    simpa [prefixWord, tailWord_7841161, baseEnd_7841161] using wordTrace_append hprefix tailTrace_7841161
  have hstable : (prefixWord ++ tailWord_7841161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841161).length < 2 ^ (prefixWord ++ tailWord_7841161).sum := by decide
  have hdescent : baseEnd_7841161 < baseStart_7841161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841172 : List Nat := [2, 4, 2, 1, 2, 1, 3, 3, 1, 2, 2]
def baseStart_7841172 : Nat := 118140960795 + 7841172 * 2 ^ 59
def prefixEnd_7841172 : Nat := 4983230072969 + 3 ^ 40 * 7841172 * 2
def baseEnd_7841172 : Nat := 4026290130576500612189113

theorem tailTrace_7841172 : CollatzResearch.WordTrace tailWord_7841172 prefixEnd_7841172 4026290130576500612189113 := by
  unfold tailWord_7841172
  simp only [CollatzResearch.WordTrace]
  refine ⟨142995518974390242203146885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190660691965853656270862513 142995518974390242203146885)
  ·
    refine ⟨26811659807698170413090041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 142995518974390242203146885 26811659807698170413090041)
    ·
      refine ⟨20108744855773627809817531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 26811659807698170413090041 20108744855773627809817531)
      ·
        refine ⟨30163117283660441714726297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20108744855773627809817531 30163117283660441714726297)
        ·
          refine ⟨22622337962745331286044723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30163117283660441714726297 22622337962745331286044723)
          ·
            refine ⟨33933506944117996929067085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22622337962745331286044723 33933506944117996929067085)
            ·
              refine ⟨12725065104044248848400157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33933506944117996929067085 12725065104044248848400157)
              ·
                refine ⟨4771899414016593318150059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12725065104044248848400157 4771899414016593318150059)
                ·
                  refine ⟨7157849121024889977225089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4771899414016593318150059 7157849121024889977225089)
                  ·
                    refine ⟨5368386840768667482918817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7157849121024889977225089 5368386840768667482918817)
                    ·
                      refine ⟨4026290130576500612189113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368386840768667482918817 4026290130576500612189113)
                      ·
                        rfl

theorem cell23_7841172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_7841172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841172 prefixEnd_7841172 := by exact prefixLift 7841172
  have htrace : WordTrace (prefixWord ++ tailWord_7841172) baseStart_7841172 baseEnd_7841172 := by
    simpa [prefixWord, tailWord_7841172, baseEnd_7841172] using wordTrace_append hprefix tailTrace_7841172
  have hstable : (prefixWord ++ tailWord_7841172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841172).length < 2 ^ (prefixWord ++ tailWord_7841172).sum := by decide
  have hdescent : baseEnd_7841172 < baseStart_7841172 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841205 : List Nat := [1, 3, 3, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_7841205 : Nat := 118140960795 + 7841205 * 2 ^ 59
def prefixEnd_7841205 : Nat := 4983230072969 + 3 ^ 40 * 7841205 * 2
def baseEnd_7841205 : Nat := 4026307075438098983076461

theorem tailTrace_7841205 : CollatzResearch.WordTrace tailWord_7841205 prefixEnd_7841205 4026307075438098983076461 := by
  unfold tailWord_7841205
  simp only [CollatzResearch.WordTrace]
  refine ⟨285992241557660931042245069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190661494371773954028163379 285992241557660931042245069)
  ·
    refine ⟨107247090584122849140841901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 285992241557660931042245069 107247090584122849140841901)
    ·
      refine ⟨40217658969046068427815713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107247090584122849140841901 40217658969046068427815713)
      ·
        refine ⟨30163244226784551320861785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 40217658969046068427815713 30163244226784551320861785)
        ·
          refine ⟨22622433170088413490646339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30163244226784551320861785 22622433170088413490646339)
          ·
            refine ⟨33933649755132620235969509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22622433170088413490646339 33933649755132620235969509)
            ·
              refine ⟨6362559329087366294244283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33933649755132620235969509 6362559329087366294244283)
              ·
                refine ⟨9543838993631049441366425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6362559329087366294244283 9543838993631049441366425)
                ·
                  refine ⟨7157879245223287081024819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9543838993631049441366425 7157879245223287081024819)
                  ·
                    refine ⟨10736818867834930621537229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7157879245223287081024819 10736818867834930621537229)
                    ·
                      refine ⟨4026307075438098983076461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10736818867834930621537229 4026307075438098983076461)
                      ·
                        rfl

theorem cell23_7841205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_7841205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841205 prefixEnd_7841205 := by exact prefixLift 7841205
  have htrace : WordTrace (prefixWord ++ tailWord_7841205) baseStart_7841205 baseEnd_7841205 := by
    simpa [prefixWord, tailWord_7841205, baseEnd_7841205] using wordTrace_append hprefix tailTrace_7841205
  have hstable : (prefixWord ++ tailWord_7841205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841205).length < 2 ^ (prefixWord ++ tailWord_7841205).sum := by decide
  have hdescent : baseEnd_7841205 < baseStart_7841205 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841228 : List Nat := [2, 2, 1, 4, 2, 2, 1, 2, 1, 4, 2]
def baseStart_7841228 : Nat := 118140960795 + 7841228 * 2 ^ 59
def prefixEnd_7841228 : Nat := 4983230072969 + 3 ^ 40 * 7841228 * 2
def baseEnd_7841228 : Nat := 4026318885493152393088855

theorem tailTrace_7841228 : CollatzResearch.WordTrace tailWord_7841228 prefixEnd_7841228 4026318885493152393088855 := by
  unfold tailWord_7841228
  simp only [CollatzResearch.WordTrace]
  refine ⟨142996540218288802985166169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190662053624385070646888225 142996540218288802985166169)
  ·
    refine ⟨107247405163716602238874627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 142996540218288802985166169 107247405163716602238874627)
    ·
      refine ⟨160871107745574903358311941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107247405163716602238874627 160871107745574903358311941)
      ·
        refine ⟨30163332702295294379683489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 160871107745574903358311941 30163332702295294379683489)
        ·
          refine ⟨22622499526721470784762617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30163332702295294379683489 22622499526721470784762617)
          ·
            refine ⟨16966874645041103088571963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22622499526721470784762617 16966874645041103088571963)
            ·
              refine ⟨25450311967561654632857945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16966874645041103088571963 25450311967561654632857945)
              ·
                refine ⟨19087733975671240974643459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25450311967561654632857945 19087733975671240974643459)
                ·
                  refine ⟨28631600963506861461965189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19087733975671240974643459 28631600963506861461965189)
                  ·
                    refine ⟨5368425180657536524118473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28631600963506861461965189 5368425180657536524118473)
                    ·
                      refine ⟨4026318885493152393088855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368425180657536524118473 4026318885493152393088855)
                      ·
                        rfl

theorem cell23_7841228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_7841228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841228 prefixEnd_7841228 := by exact prefixLift 7841228
  have htrace : WordTrace (prefixWord ++ tailWord_7841228) baseStart_7841228 baseEnd_7841228 := by
    simpa [prefixWord, tailWord_7841228, baseEnd_7841228] using wordTrace_append hprefix tailTrace_7841228
  have hstable : (prefixWord ++ tailWord_7841228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841228).length < 2 ^ (prefixWord ++ tailWord_7841228).sum := by decide
  have hdescent : baseEnd_7841228 < baseStart_7841228 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841245 : List Nat := [1, 4, 3, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_7841245 : Nat := 118140960795 + 7841245 * 2 ^ 59
def prefixEnd_7841245 : Nat := 4983230072969 + 3 ^ 40 * 7841245 * 2
def baseEnd_7841245 : Nat := 4026327614664278826576277

theorem tailTrace_7841245 : CollatzResearch.WordTrace tailWord_7841245 prefixEnd_7841245 4026327614664278826576277 := by
  unfold tailWord_7841245
  simp only [CollatzResearch.WordTrace]
  refine ⟨285993700477516017873701189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190662466985010678582467459 285993700477516017873701189)
  ·
    refine ⟨53623818839534253351318973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285993700477516017873701189 53623818839534253351318973)
    ·
      refine ⟨20108932064825345006744615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 53623818839534253351318973 20108932064825345006744615)
      ·
        refine ⟨30163398097238017510116923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20108932064825345006744615 30163398097238017510116923)
        ·
          refine ⟨45245097145857026265175385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30163398097238017510116923 45245097145857026265175385)
          ·
            refine ⟨33933822859392769698881539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45245097145857026265175385 33933822859392769698881539)
            ·
              refine ⟨50900734289089154548322309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33933822859392769698881539 50900734289089154548322309)
              ·
                refine ⟨9543887679204216477810433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50900734289089154548322309 9543887679204216477810433)
                ·
                  refine ⟨7157915759403162358357825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9543887679204216477810433 7157915759403162358357825)
                  ·
                    refine ⟨5368436819552371768768369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7157915759403162358357825 5368436819552371768768369)
                    ·
                      refine ⟨4026327614664278826576277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368436819552371768768369 4026327614664278826576277)
                      ·
                        rfl

theorem cell23_7841245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_7841245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841245 prefixEnd_7841245 := by exact prefixLift 7841245
  have htrace : WordTrace (prefixWord ++ tailWord_7841245) baseStart_7841245 baseEnd_7841245 := by
    simpa [prefixWord, tailWord_7841245, baseEnd_7841245] using wordTrace_append hprefix tailTrace_7841245
  have hstable : (prefixWord ++ tailWord_7841245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841245).length < 2 ^ (prefixWord ++ tailWord_7841245).sum := by decide
  have hdescent : baseEnd_7841245 < baseStart_7841245 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841281 : List Nat := [1, 2, 4, 1, 4, 1, 1, 1, 1, 7]
def baseStart_7841281 : Nat := 118140960795 + 7841281 * 2 ^ 59
def prefixEnd_7841281 : Nat := 4983230072969 + 3 ^ 40 * 7841281 * 2
def baseEnd_7841281 : Nat := 1342115366655946895242037

theorem tailTrace_7841281 : CollatzResearch.WordTrace tailWord_7841281 prefixEnd_7841281 1342115366655946895242037 := by
  unfold tailWord_7841281
  simp only [CollatzResearch.WordTrace]
  refine ⟨285995013505385596022011697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190663342336923730681341131 285995013505385596022011697)
  ·
    refine ⟨214496260129039197016508773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285995013505385596022011697 214496260129039197016508773)
    ·
      refine ⟨40218048774194849440595395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 214496260129039197016508773 40218048774194849440595395)
      ·
        refine ⟨60327073161292274160893093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40218048774194849440595395 60327073161292274160893093)
        ·
          refine ⟨11311326217742301405167455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60327073161292274160893093 11311326217742301405167455)
          ·
            refine ⟨16966989326613452107751183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311326217742301405167455 16966989326613452107751183)
            ·
              refine ⟨25450483989920178161626775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16966989326613452107751183 25450483989920178161626775)
              ·
                refine ⟨38175725984880267242440163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25450483989920178161626775 38175725984880267242440163)
                ·
                  refine ⟨57263588977320400863660245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38175725984880267242440163 57263588977320400863660245)
                  ·
                    refine ⟨1342115366655946895242037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57263588977320400863660245 1342115366655946895242037)
                    ·
                      rfl

theorem cell23_7841281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 7].length) (baseStart_7841281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841281 prefixEnd_7841281 := by exact prefixLift 7841281
  have htrace : WordTrace (prefixWord ++ tailWord_7841281) baseStart_7841281 baseEnd_7841281 := by
    simpa [prefixWord, tailWord_7841281, baseEnd_7841281] using wordTrace_append hprefix tailTrace_7841281
  have hstable : (prefixWord ++ tailWord_7841281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841281).length < 2 ^ (prefixWord ++ tailWord_7841281).sum := by decide
  have hdescent : baseEnd_7841281 < baseStart_7841281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841311 : List Nat := [1, 1, 2, 4, 1, 1, 3, 3, 3, 4]
def baseStart_7841311 : Nat := 118140960795 + 7841311 * 2 ^ 59
def prefixEnd_7841311 : Nat := 4983230072969 + 3 ^ 40 * 7841311 * 2
def baseEnd_7841311 : Nat := 1342120501462491856116991

theorem tailTrace_7841311 : CollatzResearch.WordTrace tailWord_7841311 prefixEnd_7841311 1342120501462491856116991 := by
  unfold tailWord_7841311
  simp only [CollatzResearch.WordTrace]
  refine ⟨285996107695276911145603787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190664071796851274097069191 285996107695276911145603787)
  ·
    refine ⟨428994161542915366718405681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 285996107695276911145603787 428994161542915366718405681)
    ·
      refine ⟨321745621157186525038804261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 428994161542915366718405681 321745621157186525038804261)
      ·
        refine ⟨60327303966972473444775799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 321745621157186525038804261 60327303966972473444775799)
        ·
          refine ⟨90490955950458710167163699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60327303966972473444775799 90490955950458710167163699)
          ·
            refine ⟨135736433925688065250745549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90490955950458710167163699 135736433925688065250745549)
            ·
              refine ⟨50901162722133024469029581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135736433925688065250745549 50901162722133024469029581)
              ·
                refine ⟨19087936020799884175886093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 50901162722133024469029581 19087936020799884175886093)
                ·
                  refine ⟨7157976007799956565957285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19087936020799884175886093 7157976007799956565957285)
                  ·
                    refine ⟨1342120501462491856116991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7157976007799956565957285 1342120501462491856116991)
                    ·
                      rfl

theorem cell23_7841311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 3, 3, 4].length) (baseStart_7841311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841311 prefixEnd_7841311 := by exact prefixLift 7841311
  have htrace : WordTrace (prefixWord ++ tailWord_7841311) baseStart_7841311 baseEnd_7841311 := by
    simpa [prefixWord, tailWord_7841311, baseEnd_7841311] using wordTrace_append hprefix tailTrace_7841311
  have hstable : (prefixWord ++ tailWord_7841311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841311).length < 2 ^ (prefixWord ++ tailWord_7841311).sum := by decide
  have hdescent : baseEnd_7841311 < baseStart_7841311 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841362 : List Nat := [3, 2, 2, 1, 2, 3, 3, 2, 1, 4]
def baseStart_7841362 : Nat := 118140960795 + 7841362 * 2 ^ 59
def prefixEnd_7841362 : Nat := 4983230072969 + 3 ^ 40 * 7841362 * 2
def baseEnd_7841362 : Nat := 1342129230633618289604413

theorem tailTrace_7841362 : CollatzResearch.WordTrace tailWord_7841362 prefixEnd_7841362 1342129230633618289604413 := by
  unfold tailWord_7841362
  simp only [CollatzResearch.WordTrace]
  refine ⟨71499491954523036713927585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190665311878728097903806893 71499491954523036713927585)
  ·
    refine ⟨53624618965892277535445689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71499491954523036713927585 53624618965892277535445689)
    ·
      refine ⟨40218464224419208151584267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53624618965892277535445689 40218464224419208151584267)
      ·
        refine ⟨60327696336628812227376401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40218464224419208151584267 60327696336628812227376401)
        ·
          refine ⟨45245772252471609170532301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60327696336628812227376401 45245772252471609170532301)
          ·
            refine ⟨16967164594676853438949613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45245772252471609170532301 16967164594676853438949613)
            ·
              refine ⟨6362686723003820039606105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16967164594676853438949613 6362686723003820039606105)
              ·
                refine ⟨4772015042252865029704579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6362686723003820039606105 4772015042252865029704579)
                ·
                  refine ⟨7158022563379297544556869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772015042252865029704579 7158022563379297544556869)
                  ·
                    refine ⟨1342129230633618289604413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7158022563379297544556869 1342129230633618289604413)
                    ·
                      rfl

theorem cell23_7841362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_7841362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841362 prefixEnd_7841362 := by exact prefixLift 7841362
  have htrace : WordTrace (prefixWord ++ tailWord_7841362) baseStart_7841362 baseEnd_7841362 := by
    simpa [prefixWord, tailWord_7841362, baseEnd_7841362] using wordTrace_append hprefix tailTrace_7841362
  have hstable : (prefixWord ++ tailWord_7841362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841362).length < 2 ^ (prefixWord ++ tailWord_7841362).sum := by decide
  have hdescent : baseEnd_7841362 < baseStart_7841362 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841401 : List Nat := [1, 2, 1, 3, 3, 1, 3, 2, 1, 6]
def baseStart_7841401 : Nat := 118140960795 + 7841401 * 2 ^ 59
def prefixEnd_7841401 : Nat := 4983230072969 + 3 ^ 40 * 7841401 * 2
def baseEnd_7841401 : Nat := 1342135905882126738741853

theorem tailTrace_7841401 : CollatzResearch.WordTrace tailWord_7841401 prefixEnd_7841401 1342135905882126738741853 := by
  unfold tailWord_7841401
  simp only [CollatzResearch.WordTrace]
  refine ⟨285999390264950856516380057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190666260176633904344253371 285999390264950856516380057)
  ·
    refine ⟨214499542698713142387285043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 285999390264950856516380057 214499542698713142387285043)
    ·
      refine ⟨321749314048069713580927565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214499542698713142387285043 321749314048069713580927565)
      ·
        refine ⟨120655992768026142592847837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321749314048069713580927565 120655992768026142592847837)
        ·
          refine ⟨45245997288009803472317939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120655992768026142592847837 45245997288009803472317939)
          ·
            refine ⟨67868995932014705208476909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45245997288009803472317939 67868995932014705208476909)
            ·
              refine ⟨25450873474505514453178841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67868995932014705208476909 25450873474505514453178841)
              ·
                refine ⟨19088155105879135839884131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25450873474505514453178841 19088155105879135839884131)
                ·
                  refine ⟨28632232658818703759826197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19088155105879135839884131 28632232658818703759826197)
                  ·
                    refine ⟨1342135905882126738741853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 28632232658818703759826197 1342135905882126738741853)
                    ·
                      rfl

theorem cell23_7841401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 6].length) (baseStart_7841401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841401 prefixEnd_7841401 := by exact prefixLift 7841401
  have htrace : WordTrace (prefixWord ++ tailWord_7841401) baseStart_7841401 baseEnd_7841401 := by
    simpa [prefixWord, tailWord_7841401, baseEnd_7841401] using wordTrace_append hprefix tailTrace_7841401
  have hstable : (prefixWord ++ tailWord_7841401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841401).length < 2 ^ (prefixWord ++ tailWord_7841401).sum := by decide
  have hdescent : baseEnd_7841401 < baseStart_7841401 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841405 : List Nat := [1, 4, 1, 1, 4, 2, 3, 1, 1, 5]
def baseStart_7841405 : Nat := 118140960795 + 7841405 * 2 ^ 59
def prefixEnd_7841405 : Nat := 4983230072969 + 3 ^ 40 * 7841405 * 2
def baseEnd_7841405 : Nat := 1342136590522999400191847

theorem tailTrace_7841405 : CollatzResearch.WordTrace tailWord_7841405 prefixEnd_7841405 1342136590522999400191847 := by
  unfold tailWord_7841405
  simp only [CollatzResearch.WordTrace]
  refine ⟨285999536156936365199525669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190666357437957576799683779 285999536156936365199525669)
  ·
    refine ⟨53624913029425568474911063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 285999536156936365199525669 53624913029425568474911063)
    ·
      refine ⟨80437369544138352712366595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53624913029425568474911063 80437369544138352712366595)
      ·
        refine ⟨120656054316207529068549893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80437369544138352712366595 120656054316207529068549893)
        ·
          refine ⟨22623010184288911700353105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 120656054316207529068549893 22623010184288911700353105)
          ·
            refine ⟨16967257638216683775264829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 22623010184288911700353105 16967257638216683775264829)
            ·
              refine ⟨6362721614331256415724311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16967257638216683775264829 6362721614331256415724311)
              ·
                refine ⟨9544082421496884623586467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6362721614331256415724311 9544082421496884623586467)
                ·
                  refine ⟨14316123632245326935379701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9544082421496884623586467 14316123632245326935379701)
                  ·
                    refine ⟨1342136590522999400191847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14316123632245326935379701 1342136590522999400191847)
                    ·
                      rfl

theorem cell23_7841405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_7841405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841405 prefixEnd_7841405 := by exact prefixLift 7841405
  have htrace : WordTrace (prefixWord ++ tailWord_7841405) baseStart_7841405 baseEnd_7841405 := by
    simpa [prefixWord, tailWord_7841405, baseEnd_7841405] using wordTrace_append hprefix tailTrace_7841405
  have hstable : (prefixWord ++ tailWord_7841405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841405).length < 2 ^ (prefixWord ++ tailWord_7841405).sum := by decide
  have hdescent : baseEnd_7841405 < baseStart_7841405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841431 : List Nat := [1, 1, 3, 3, 2, 2, 3, 8]
def baseStart_7841431 : Nat := 118140960795 + 7841431 * 2 ^ 59
def prefixEnd_7841431 : Nat := 4983230072969 + 3 ^ 40 * 7841431 * 2
def baseEnd_7841431 : Nat := 149126782298741299957423

theorem tailTrace_7841431 : CollatzResearch.WordTrace tailWord_7841431 prefixEnd_7841431 149126782298741299957423 := by
  unfold tailWord_7841431
  simp only [CollatzResearch.WordTrace]
  refine ⟨286000484454842171639972147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190666989636561447759981431 286000484454842171639972147)
  ·
    refine ⟨429000726682263257459958221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286000484454842171639972147 429000726682263257459958221)
    ·
      refine ⟨160875272505848721547484333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 429000726682263257459958221 160875272505848721547484333)
      ·
        refine ⟨60328227189693270580306625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 160875272505848721547484333 60328227189693270580306625)
        ·
          refine ⟨45246170392269952935229969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 60328227189693270580306625 45246170392269952935229969)
          ·
            refine ⟨33934627794202464701422477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45246170392269952935229969 33934627794202464701422477)
            ·
              refine ⟨12725485422825924263033429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33934627794202464701422477 12725485422825924263033429)
              ·
                refine ⟨149126782298741299957423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12725485422825924263033429 149126782298741299957423)
                ·
                  rfl

theorem cell23_7841431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 3, 8].length) (baseStart_7841431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841431 prefixEnd_7841431 := by exact prefixLift 7841431
  have htrace : WordTrace (prefixWord ++ tailWord_7841431) baseStart_7841431 baseEnd_7841431 := by
    simpa [prefixWord, tailWord_7841431, baseEnd_7841431] using wordTrace_append hprefix tailTrace_7841431
  have hstable : (prefixWord ++ tailWord_7841431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841431).length < 2 ^ (prefixWord ++ tailWord_7841431).sum := by decide
  have hdescent : baseEnd_7841431 < baseStart_7841431 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841458 : List Nat := [3, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3]
def baseStart_7841458 : Nat := 118140960795 + 7841458 * 2 ^ 59
def prefixEnd_7841458 : Nat := 4983230072969 + 3 ^ 40 * 7841458 * 2
def baseEnd_7841458 : Nat := 4026436986043686493212797

theorem tailTrace_7841458 : CollatzResearch.WordTrace tailWord_7841458 prefixEnd_7841458 4026436986043686493212797 := by
  unfold tailWord_7841458
  simp only [CollatzResearch.WordTrace]
  refine ⟨71500367306436088812801257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190667646150496236834136685 71500367306436088812801257)
  ·
    refine ⟨53625275479827066609600943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71500367306436088812801257 53625275479827066609600943)
    ·
      refine ⟨80437913219740599914401415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53625275479827066609600943 80437913219740599914401415)
      ·
        refine ⟨120656869829610899871602123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80437913219740599914401415 120656869829610899871602123)
        ·
          refine ⟨180985304744416349807403185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120656869829610899871602123 180985304744416349807403185)
          ·
            refine ⟨135738978558312262355552389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 180985304744416349807403185 135738978558312262355552389)
            ·
              refine ⟨25451058479683549191666073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135738978558312262355552389 25451058479683549191666073)
              ·
                refine ⟨19088293859762661893749555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25451058479683549191666073 19088293859762661893749555)
                ·
                  refine ⟨28632440789643992840624333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19088293859762661893749555 28632440789643992840624333)
                  ·
                    refine ⟨10737165296116497315234125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28632440789643992840624333 10737165296116497315234125)
                    ·
                      refine ⟨4026436986043686493212797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10737165296116497315234125 4026436986043686493212797)
                      ·
                        rfl

theorem cell23_7841458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 4, 2, 1, 3, 3].length) (baseStart_7841458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841458 prefixEnd_7841458 := by exact prefixLift 7841458
  have htrace : WordTrace (prefixWord ++ tailWord_7841458) baseStart_7841458 baseEnd_7841458 := by
    simpa [prefixWord, tailWord_7841458, baseEnd_7841458] using wordTrace_append hprefix tailTrace_7841458
  have hstable : (prefixWord ++ tailWord_7841458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841458).length < 2 ^ (prefixWord ++ tailWord_7841458).sum := by decide
  have hdescent : baseEnd_7841458 < baseStart_7841458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841492 : List Nat := [2, 4, 1, 3, 1, 3, 1, 1, 1, 3, 3]
def baseStart_7841492 : Nat := 118140960795 + 7841492 * 2 ^ 59
def prefixEnd_7841492 : Nat := 4983230072969 + 3 ^ 40 * 7841492 * 2
def baseEnd_7841492 : Nat := 4026454444385939360187641

theorem tailTrace_7841492 : CollatzResearch.WordTrace tailWord_7841492 prefixEnd_7841492 4026454444385939360187641 := by
  unfold tailWord_7841492
  simp only [CollatzResearch.WordTrace]
  refine ⟨143001354653810589528971365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190668472871747452705295153 143001354653810589528971365)
  ·
    refine ⟨26812753997589485536682131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 143001354653810589528971365 26812753997589485536682131)
    ·
      refine ⟨40219130996384228305023197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26812753997589485536682131 40219130996384228305023197)
      ·
        refine ⟨15082174123644085614383699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40219130996384228305023197 15082174123644085614383699)
        ·
          refine ⟨22623261185466128421575549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15082174123644085614383699 22623261185466128421575549)
          ·
            refine ⟨8483722944549798158090831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 22623261185466128421575549 8483722944549798158090831)
            ·
              refine ⟨12725584416824697237136247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8483722944549798158090831 12725584416824697237136247)
              ·
                refine ⟨19088376625237045855704371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12725584416824697237136247 19088376625237045855704371)
                ·
                  refine ⟨28632564937855568783556557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19088376625237045855704371 28632564937855568783556557)
                  ·
                    refine ⟨10737211851695838293833709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28632564937855568783556557 10737211851695838293833709)
                    ·
                      refine ⟨4026454444385939360187641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10737211851695838293833709 4026454444385939360187641)
                      ·
                        rfl

theorem cell23_7841492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 1, 1, 1, 3, 3].length) (baseStart_7841492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841492 prefixEnd_7841492 := by exact prefixLift 7841492
  have htrace : WordTrace (prefixWord ++ tailWord_7841492) baseStart_7841492 baseEnd_7841492 := by
    simpa [prefixWord, tailWord_7841492, baseEnd_7841492] using wordTrace_append hprefix tailTrace_7841492
  have hstable : (prefixWord ++ tailWord_7841492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841492).length < 2 ^ (prefixWord ++ tailWord_7841492).sum := by decide
  have hdescent : baseEnd_7841492 < baseStart_7841492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841515 : List Nat := [1, 1, 1, 1, 2, 4, 3, 2, 4, 2, 2]
def baseStart_7841515 : Nat := 118140960795 + 7841515 * 2 ^ 59
def prefixEnd_7841515 : Nat := 4983230072969 + 3 ^ 40 * 7841515 * 2
def baseEnd_7841515 : Nat := 4026466254440992770200035

theorem tailTrace_7841515 : CollatzResearch.WordTrace tailWord_7841515 prefixEnd_7841515 4026466254440992770200035 := by
  unfold tailWord_7841515
  simp only [CollatzResearch.WordTrace]
  refine ⟨286003548186537853986029999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190669032124358569324019999 286003548186537853986029999)
  ·
    refine ⟨429005322279806780979044999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286003548186537853986029999 429005322279806780979044999)
    ·
      refine ⟨643507983419710171468567499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429005322279806780979044999 643507983419710171468567499)
      ·
        refine ⟨965261975129565257202851249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643507983419710171468567499 965261975129565257202851249)
        ·
          refine ⟨723946481347173942902138437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965261975129565257202851249 723946481347173942902138437)
          ·
            refine ⟨135739965252595114294150957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 723946481347173942902138437 135739965252595114294150957)
            ·
              refine ⟨50902486969723167860306609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 135739965252595114294150957 50902486969723167860306609)
              ·
                refine ⟨38176865227292375895229957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50902486969723167860306609 38176865227292375895229957)
                ·
                  refine ⟨7158162230117320480355617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 38176865227292375895229957 7158162230117320480355617)
                  ·
                    refine ⟨5368621672587990360266713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7158162230117320480355617 5368621672587990360266713)
                    ·
                      refine ⟨4026466254440992770200035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368621672587990360266713 4026466254440992770200035)
                      ·
                        rfl

theorem cell23_7841515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 2, 2].length) (baseStart_7841515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841515 prefixEnd_7841515 := by exact prefixLift 7841515
  have htrace : WordTrace (prefixWord ++ tailWord_7841515) baseStart_7841515 baseEnd_7841515 := by
    simpa [prefixWord, tailWord_7841515, baseEnd_7841515] using wordTrace_append hprefix tailTrace_7841515
  have hstable : (prefixWord ++ tailWord_7841515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841515).length < 2 ^ (prefixWord ++ tailWord_7841515).sum := by decide
  have hdescent : baseEnd_7841515 < baseStart_7841515 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841518 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5]
def baseStart_7841518 : Nat := 118140960795 + 7841518 * 2 ^ 59
def prefixEnd_7841518 : Nat := 4983230072969 + 3 ^ 40 * 7841518 * 2
def baseEnd_7841518 : Nat := 4026467794882956258462521

theorem tailTrace_7841518 : CollatzResearch.WordTrace tailWord_7841518 prefixEnd_7841518 4026467794882956258462521 := by
  unfold tailWord_7841518
  simp only [CollatzResearch.WordTrace]
  refine ⟨35750457200690873187298651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190669105070351323665592805 35750457200690873187298651)
  ·
    refine ⟨53625685801036309780947977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 35750457200690873187298651 53625685801036309780947977)
    ·
      refine ⟨40219264350777232335710983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53625685801036309780947977 40219264350777232335710983)
      ·
        refine ⟨60328896526165848503566475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40219264350777232335710983 60328896526165848503566475)
        ·
          refine ⟨90493344789248772755349713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60328896526165848503566475 90493344789248772755349713)
          ·
            refine ⟨67870008591936579566512285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90493344789248772755349713 67870008591936579566512285)
            ·
              refine ⟨25451253221976217337442107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67870008591936579566512285 25451253221976217337442107)
              ·
                refine ⟨38176879832964326006163161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25451253221976217337442107 38176879832964326006163161)
                ·
                  refine ⟨28632659874723244504622371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38176879832964326006163161 28632659874723244504622371)
                  ·
                    refine ⟨42948989812084866756933557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28632659874723244504622371 42948989812084866756933557)
                    ·
                      refine ⟨4026467794882956258462521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42948989812084866756933557 4026467794882956258462521)
                      ·
                        rfl

theorem cell23_7841518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_7841518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841518 prefixEnd_7841518 := by exact prefixLift 7841518
  have htrace : WordTrace (prefixWord ++ tailWord_7841518) baseStart_7841518 baseEnd_7841518 := by
    simpa [prefixWord, tailWord_7841518, baseEnd_7841518] using wordTrace_append hprefix tailTrace_7841518
  have hstable : (prefixWord ++ tailWord_7841518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841518).length < 2 ^ (prefixWord ++ tailWord_7841518).sum := by decide
  have hdescent : baseEnd_7841518 < baseStart_7841518 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841532 : List Nat := [2, 2, 2, 1, 3, 1, 2, 4, 2, 2, 2]
def baseStart_7841532 : Nat := 118140960795 + 7841532 * 2 ^ 59
def prefixEnd_7841532 : Nat := 4983230072969 + 3 ^ 40 * 7841532 * 2
def baseEnd_7841532 : Nat := 4026474983612119203687457

theorem tailTrace_7841532 : CollatzResearch.WordTrace tailWord_7841532 prefixEnd_7841532 4026474983612119203687457 := by
  unfold tailWord_7841532
  simp only [CollatzResearch.WordTrace]
  refine ⟨143002084113738132944699425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190669445484984177259599233 143002084113738132944699425)
  ·
    refine ⟨107251563085303599708524569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143002084113738132944699425 107251563085303599708524569)
    ·
      refine ⟨80438672313977699781393427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107251563085303599708524569 80438672313977699781393427)
      ·
        refine ⟨120658008470966549672090141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80438672313977699781393427 120658008470966549672090141)
        ·
          refine ⟨45246753176612456127033803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120658008470966549672090141 45246753176612456127033803)
          ·
            refine ⟨67870129764918684190550705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 45246753176612456127033803 67870129764918684190550705)
            ·
              refine ⟨50902597323689013142913029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 67870129764918684190550705 50902597323689013142913029)
              ·
                refine ⟨9544236998191689964296193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 50902597323689013142913029 9544236998191689964296193)
                ·
                  refine ⟨7158177748643767473222145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9544236998191689964296193 7158177748643767473222145)
                  ·
                    refine ⟨5368633311482825604916609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7158177748643767473222145 5368633311482825604916609)
                    ·
                      refine ⟨4026474983612119203687457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368633311482825604916609 4026474983612119203687457)
                      ·
                        rfl

theorem cell23_7841532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 2, 2, 2].length) (baseStart_7841532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841532 prefixEnd_7841532 := by exact prefixLift 7841532
  have htrace : WordTrace (prefixWord ++ tailWord_7841532) baseStart_7841532 baseEnd_7841532 := by
    simpa [prefixWord, tailWord_7841532, baseEnd_7841532] using wordTrace_append hprefix tailTrace_7841532
  have hstable : (prefixWord ++ tailWord_7841532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841532).length < 2 ^ (prefixWord ++ tailWord_7841532).sum := by decide
  have hdescent : baseEnd_7841532 < baseStart_7841532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841548 : List Nat := [2, 2, 1, 2, 2, 1, 2, 3, 2, 3, 3]
def baseStart_7841548 : Nat := 118140960795 + 7841548 * 2 ^ 59
def prefixEnd_7841548 : Nat := 4983230072969 + 3 ^ 40 * 7841548 * 2
def baseEnd_7841548 : Nat := 4026483199302591141087383

theorem tailTrace_7841548 : CollatzResearch.WordTrace tailWord_7841548 prefixEnd_7841548 4026483199302591141087383 := by
  unfold tailWord_7841548
  simp only [CollatzResearch.WordTrace]
  refine ⟨143002375897709150310990649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190669834530278867081320865 143002375897709150310990649)
  ·
    refine ⟨107251781923281862733242987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143002375897709150310990649 107251781923281862733242987)
    ·
      refine ⟨160877672884922794099864481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107251781923281862733242987 160877672884922794099864481)
      ·
        refine ⟨120658254663692095574898361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 160877672884922794099864481 120658254663692095574898361)
        ·
          refine ⟨90493690997769071681173771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120658254663692095574898361 90493690997769071681173771)
          ·
            refine ⟨135740536496653607521760657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90493690997769071681173771 135740536496653607521760657)
            ·
              refine ⟨101805402372490205641320493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135740536496653607521760657 101805402372490205641320493)
              ·
                refine ⟨38177025889683827115495185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 101805402372490205641320493 38177025889683827115495185)
                ·
                  refine ⟨28632769417262870336621389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38177025889683827115495185 28632769417262870336621389)
                  ·
                    refine ⟨10737288531473576376233021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 28632769417262870336621389 10737288531473576376233021)
                    ·
                      refine ⟨4026483199302591141087383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10737288531473576376233021 4026483199302591141087383)
                      ·
                        rfl

theorem cell23_7841548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_7841548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841548 prefixEnd_7841548 := by exact prefixLift 7841548
  have htrace : WordTrace (prefixWord ++ tailWord_7841548) baseStart_7841548 baseEnd_7841548 := by
    simpa [prefixWord, tailWord_7841548, baseEnd_7841548] using wordTrace_append hprefix tailTrace_7841548
  have hstable : (prefixWord ++ tailWord_7841548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841548).length < 2 ^ (prefixWord ++ tailWord_7841548).sum := by decide
  have hdescent : baseEnd_7841548 < baseStart_7841548 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841551 : List Nat := [1, 1, 2, 1, 1, 1, 4, 4, 1, 7]
def baseStart_7841551 : Nat := 118140960795 + 7841551 * 2 ^ 59
def prefixEnd_7841551 : Nat := 4983230072969 + 3 ^ 40 * 7841551 * 2
def baseEnd_7841551 : Nat := 1342161579914851543116623

theorem tailTrace_7841551 : CollatzResearch.WordTrace tailWord_7841551 prefixEnd_7841551 1342161579914851543116623 := by
  unfold tailWord_7841551
  simp only [CollatzResearch.WordTrace]
  refine ⟨286004861214407432134340507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190669907476271621422893671 286004861214407432134340507)
  ·
    refine ⟨429007291821611148201510761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286004861214407432134340507 429007291821611148201510761)
    ·
      refine ⟨321755468866208361151133071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429007291821611148201510761 321755468866208361151133071)
      ·
        refine ⟨482633203299312541726699607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321755468866208361151133071 482633203299312541726699607)
        ·
          refine ⟨723949804948968812590049411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482633203299312541726699607 723949804948968812590049411)
          ·
            refine ⟨1085924707423453218885074117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723949804948968812590049411 1085924707423453218885074117)
            ·
              refine ⟨203610882641897478540951397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1085924707423453218885074117 203610882641897478540951397)
              ·
                refine ⟨38177040495355777226428387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 203610882641897478540951397 38177040495355777226428387)
                ·
                  refine ⟨57265560743033665839642581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38177040495355777226428387 57265560743033665839642581)
                  ·
                    refine ⟨1342161579914851543116623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57265560743033665839642581 1342161579914851543116623)
                    ·
                      rfl

theorem cell23_7841551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 7].length) (baseStart_7841551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841551 prefixEnd_7841551 := by exact prefixLift 7841551
  have htrace : WordTrace (prefixWord ++ tailWord_7841551) baseStart_7841551 baseEnd_7841551 := by
    simpa [prefixWord, tailWord_7841551, baseEnd_7841551] using wordTrace_append hprefix tailTrace_7841551
  have hstable : (prefixWord ++ tailWord_7841551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841551).length < 2 ^ (prefixWord ++ tailWord_7841551).sum := by decide
  have hdescent : baseEnd_7841551 < baseStart_7841551 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841566 : List Nat := [4, 3, 2, 2, 1, 1, 1, 2, 1, 4, 2]
def baseStart_7841566 : Nat := 118140960795 + 7841566 * 2 ^ 59
def prefixEnd_7841566 : Nat := 4983230072969 + 3 ^ 40 * 7841566 * 2
def baseEnd_7841566 : Nat := 4026492441954372070662301

theorem tailTrace_7841566 : CollatzResearch.WordTrace tailWord_7841566 prefixEnd_7841566 4026492441954372070662301 := by
  unfold tailWord_7841566
  simp only [CollatzResearch.WordTrace]
  refine ⟨35750676038669136212017069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 190670272206235393130757701 35750676038669136212017069)
  ·
    refine ⟨13406503514500926079506401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 35750676038669136212017069 13406503514500926079506401)
    ·
      refine ⟨10054877635875694559629801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13406503514500926079506401 10054877635875694559629801)
      ·
        refine ⟨7541158226906770919722351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10054877635875694559629801 7541158226906770919722351)
        ·
          refine ⟨11311737340360156379583527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7541158226906770919722351 11311737340360156379583527)
          ·
            refine ⟨16967606010540234569375291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311737340360156379583527 16967606010540234569375291)
            ·
              refine ⟨25451409015810351854062937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16967606010540234569375291 25451409015810351854062937)
              ·
                refine ⟨19088556761857763890547203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25451409015810351854062937 19088556761857763890547203)
                ·
                  refine ⟨28632835142786645835820805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19088556761857763890547203 28632835142786645835820805)
                  ·
                    refine ⟨5368656589272496094216401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28632835142786645835820805 5368656589272496094216401)
                    ·
                      refine ⟨4026492441954372070662301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368656589272496094216401 4026492441954372070662301)
                      ·
                        rfl

theorem cell23_7841566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_7841566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841566 prefixEnd_7841566 := by exact prefixLift 7841566
  have htrace : WordTrace (prefixWord ++ tailWord_7841566) baseStart_7841566 baseEnd_7841566 := by
    simpa [prefixWord, tailWord_7841566, baseEnd_7841566] using wordTrace_append hprefix tailTrace_7841566
  have hstable : (prefixWord ++ tailWord_7841566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841566).length < 2 ^ (prefixWord ++ tailWord_7841566).sum := by decide
  have hdescent : baseEnd_7841566 < baseStart_7841566 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841589 : List Nat := [1, 3, 3, 1, 4, 2, 2, 2, 5]
def baseStart_7841589 : Nat := 118140960795 + 7841589 * 2 ^ 59
def prefixEnd_7841589 : Nat := 4983230072969 + 3 ^ 40 * 7841589 * 2
def baseEnd_7841589 : Nat := 447389361334380608963855

theorem tailTrace_7841589 : CollatzResearch.WordTrace tailWord_7841589 prefixEnd_7841589 447389361334380608963855 := by
  unfold tailWord_7841589
  simp only [CollatzResearch.WordTrace]
  refine ⟨286006247188269764624223821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190670831458846509749482547 286006247188269764624223821)
  ·
    refine ⟨107252342695601161734083933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286006247188269764624223821 107252342695601161734083933)
    ·
      refine ⟨40219628510850435650281475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107252342695601161734083933 40219628510850435650281475)
      ·
        refine ⟨60329442766275653475422213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40219628510850435650281475 60329442766275653475422213)
        ·
          refine ⟨11311770518676685026641665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 60329442766275653475422213 11311770518676685026641665)
          ·
            refine ⟨8483827889007513769981249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11311770518676685026641665 8483827889007513769981249)
            ·
              refine ⟨6362870916755635327485937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8483827889007513769981249 6362870916755635327485937)
              ·
                refine ⟨4772153187566726495614453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6362870916755635327485937 4772153187566726495614453)
                ·
                  refine ⟨447389361334380608963855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4772153187566726495614453 447389361334380608963855)
                  ·
                    rfl

theorem cell23_7841589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 2, 2, 5].length) (baseStart_7841589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841589 prefixEnd_7841589 := by exact prefixLift 7841589
  have htrace : WordTrace (prefixWord ++ tailWord_7841589) baseStart_7841589 baseEnd_7841589 := by
    simpa [prefixWord, tailWord_7841589, baseEnd_7841589] using wordTrace_append hprefix tailTrace_7841589
  have hstable : (prefixWord ++ tailWord_7841589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841589).length < 2 ^ (prefixWord ++ tailWord_7841589).sum := by decide
  have hdescent : baseEnd_7841589 < baseStart_7841589 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841605 : List Nat := [1, 3, 1, 1, 1, 2, 5, 1, 2, 4, 2]
def baseStart_7841605 : Nat := 118140960795 + 7841605 * 2 ^ 59
def prefixEnd_7841605 : Nat := 4983230072969 + 3 ^ 40 * 7841605 * 2
def baseEnd_7841605 : Nat := 4026512467699897418074621

theorem tailTrace_7841605 : CollatzResearch.WordTrace tailWord_7841605 prefixEnd_7841605 4026512467699897418074621 := by
  unfold tailWord_7841605
  simp only [CollatzResearch.WordTrace]
  refine ⟨286006830756211799356806269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190671220504141199571204179 286006830756211799356806269)
  ·
    refine ⟨107252561533579424758802351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286006830756211799356806269 107252561533579424758802351)
    ·
      refine ⟨160878842300369137138203527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107252561533579424758802351 160878842300369137138203527)
      ·
        refine ⟨241318263450553705707305291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160878842300369137138203527 241318263450553705707305291)
        ·
          refine ⟨361977395175830558560957937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241318263450553705707305291 361977395175830558560957937)
          ·
            refine ⟨271483046381872918920718453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361977395175830558560957937 271483046381872918920718453)
            ·
              refine ⟨25451535598300586148817355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 271483046381872918920718453 25451535598300586148817355)
              ·
                refine ⟨38177303397450879223226033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25451535598300586148817355 38177303397450879223226033)
                ·
                  refine ⟨28632977548088159417419525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38177303397450879223226033 28632977548088159417419525)
                  ·
                    refine ⟨5368683290266529890766161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 28632977548088159417419525 5368683290266529890766161)
                    ·
                      refine ⟨4026512467699897418074621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368683290266529890766161 4026512467699897418074621)
                      ·
                        rfl

theorem cell23_7841605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 4, 2].length) (baseStart_7841605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841605 prefixEnd_7841605 := by exact prefixLift 7841605
  have htrace : WordTrace (prefixWord ++ tailWord_7841605) baseStart_7841605 baseEnd_7841605 := by
    simpa [prefixWord, tailWord_7841605, baseEnd_7841605] using wordTrace_append hprefix tailTrace_7841605
  have hstable : (prefixWord ++ tailWord_7841605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841605).length < 2 ^ (prefixWord ++ tailWord_7841605).sum := by decide
  have hdescent : baseEnd_7841605 < baseStart_7841605 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841632 : List Nat := [2, 1, 1, 3, 3, 2, 1, 5, 1, 4]
def baseStart_7841632 : Nat := 118140960795 + 7841632 * 2 ^ 59
def prefixEnd_7841632 : Nat := 4983230072969 + 3 ^ 40 * 7841632 * 2
def baseEnd_7841632 : Nat := 1342175443892522937478999

theorem tailTrace_7841632 : CollatzResearch.WordTrace tailWord_7841632 prefixEnd_7841632 1342175443892522937478999 := by
  unfold tailWord_7841632
  simp only [CollatzResearch.WordTrace]
  refine ⟨143003907763556991484019575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190671877018075988645359433 143003907763556991484019575)
  ·
    refine ⟨214505861645335487226029363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143003907763556991484019575 214505861645335487226029363)
    ·
      refine ⟨321758792468003230839044045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214505861645335487226029363 321758792468003230839044045)
      ·
        refine ⟨120659547175501211564641517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321758792468003230839044045 120659547175501211564641517)
        ·
          refine ⟨45247330190812954336740569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 120659547175501211564641517 45247330190812954336740569)
          ·
            refine ⟨33935497643109715752555427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45247330190812954336740569 33935497643109715752555427)
            ·
              refine ⟨50903246464664573628833141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33935497643109715752555427 50903246464664573628833141)
              ·
                refine ⟨4772179356062303777703107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 50903246464664573628833141 4772179356062303777703107)
                ·
                  refine ⟨7158269034093455666554661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772179356062303777703107 7158269034093455666554661)
                  ·
                    refine ⟨1342175443892522937478999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7158269034093455666554661 1342175443892522937478999)
                    ·
                      rfl

theorem cell23_7841632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 5, 1, 4].length) (baseStart_7841632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841632 prefixEnd_7841632 := by exact prefixLift 7841632
  have htrace : WordTrace (prefixWord ++ tailWord_7841632) baseStart_7841632 baseEnd_7841632 := by
    simpa [prefixWord, tailWord_7841632, baseEnd_7841632] using wordTrace_append hprefix tailTrace_7841632
  have hstable : (prefixWord ++ tailWord_7841632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841632).length < 2 ^ (prefixWord ++ tailWord_7841632).sum := by decide
  have hdescent : baseEnd_7841632 < baseStart_7841632 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841645 : List Nat := [1, 5, 1, 1, 1, 1, 5, 2, 6]
def baseStart_7841645 : Nat := 118140960795 + 7841645 * 2 ^ 59
def prefixEnd_7841645 : Nat := 4983230072969 + 3 ^ 40 * 7841645 * 2
def baseEnd_7841645 : Nat := 447392556325119695730493

theorem tailTrace_7841645 : CollatzResearch.WordTrace tailWord_7841645 prefixEnd_7841645 447392556325119695730493 := by
  unfold tailWord_7841645
  simp only [CollatzResearch.WordTrace]
  refine ⟨286008289676066886188262389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190672193117377924125508259 286008289676066886188262389)
  ·
    refine ⟨26813277157131270580149599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 286008289676066886188262389 26813277157131270580149599)
    ·
      refine ⟨40219915735696905870224399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 26813277157131270580149599 40219915735696905870224399)
      ·
        refine ⟨60329873603545358805336599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40219915735696905870224399 60329873603545358805336599)
        ·
          refine ⟨90494810405318038208004899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60329873603545358805336599 90494810405318038208004899)
          ·
            refine ⟨135742215607977057312007349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90494810405318038208004899 135742215607977057312007349)
            ·
              refine ⟨12725832713247849123000689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135742215607977057312007349 12725832713247849123000689)
              ·
                refine ⟨9544374534935886842250517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12725832713247849123000689 9544374534935886842250517)
                ·
                  refine ⟨447392556325119695730493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9544374534935886842250517 447392556325119695730493)
                  ·
                    rfl

theorem cell23_7841645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_7841645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841645 prefixEnd_7841645 := by exact prefixLift 7841645
  have htrace : WordTrace (prefixWord ++ tailWord_7841645) baseStart_7841645 baseEnd_7841645 := by
    simpa [prefixWord, tailWord_7841645, baseEnd_7841645] using wordTrace_append hprefix tailTrace_7841645
  have hstable : (prefixWord ++ tailWord_7841645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841645).length < 2 ^ (prefixWord ++ tailWord_7841645).sum := by decide
  have hdescent : baseEnd_7841645 < baseStart_7841645 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841658 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 5, 5]
def baseStart_7841658 : Nat := 118140960795 + 7841658 * 2 ^ 59
def prefixEnd_7841658 : Nat := 4983230072969 + 3 ^ 40 * 7841658 * 2
def baseEnd_7841658 : Nat := 1342179894058195236903959

theorem tailTrace_7841658 : CollatzResearch.WordTrace tailWord_7841658 prefixEnd_7841658 1342179894058195236903959 := by
  unfold tailWord_7841658
  simp only [CollatzResearch.WordTrace]
  refine ⟨71502190956254947352121407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190672509216679859605657085 71502190956254947352121407)
  ·
    refine ⟨107253286434382421028182111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 71502190956254947352121407 107253286434382421028182111)
    ·
      refine ⟨160879929651573631542273167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107253286434382421028182111 160879929651573631542273167)
      ·
        refine ⟨241319894477360447313409751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160879929651573631542273167 241319894477360447313409751)
        ·
          refine ⟨361979841716040670970114627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241319894477360447313409751 361979841716040670970114627)
          ·
            refine ⟨542969762574061006455171941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361979841716040670970114627 542969762574061006455171941)
            ·
              refine ⟨101806830482636438710344739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 542969762574061006455171941 101806830482636438710344739)
              ·
                refine ⟨152710245723954658065517109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101806830482636438710344739 152710245723954658065517109)
                ·
                  refine ⟨14316585536620749193642229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 152710245723954658065517109 14316585536620749193642229)
                  ·
                    refine ⟨1342179894058195236903959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14316585536620749193642229 1342179894058195236903959)
                    ·
                      rfl

theorem cell23_7841658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 5, 5].length) (baseStart_7841658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841658 prefixEnd_7841658 := by exact prefixLift 7841658
  have htrace : WordTrace (prefixWord ++ tailWord_7841658) baseStart_7841658 baseEnd_7841658 := by
    simpa [prefixWord, tailWord_7841658, baseEnd_7841658] using wordTrace_append hprefix tailTrace_7841658
  have hstable : (prefixWord ++ tailWord_7841658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841658).length < 2 ^ (prefixWord ++ tailWord_7841658).sum := by decide
  have hdescent : baseEnd_7841658 < baseStart_7841658 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841668 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 2, 1, 7]
def baseStart_7841668 : Nat := 118140960795 + 7841668 * 2 ^ 59
def prefixEnd_7841668 : Nat := 4983230072969 + 3 ^ 40 * 7841668 * 2
def baseEnd_7841668 : Nat := 4026544816981130671586831

theorem tailTrace_7841668 : CollatzResearch.WordTrace tailWord_7841668 prefixEnd_7841668 4026544816981130671586831 := by
  unfold tailWord_7841668
  simp only [CollatzResearch.WordTrace]
  refine ⟨143004564277491780558174829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190672752369989040744233105 143004564277491780558174829)
  ·
    refine ⟨53626711604059417709315561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 143004564277491780558174829 53626711604059417709315561)
    ·
      refine ⟨40220033703044563281986671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53626711604059417709315561 40220033703044563281986671)
      ·
        refine ⟨60330050554566844922980007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 40220033703044563281986671 60330050554566844922980007)
        ·
          refine ⟨90495075831850267384470011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 60330050554566844922980007 90495075831850267384470011)
          ·
            refine ⟨135742613747775401076705017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90495075831850267384470011 135742613747775401076705017)
            ·
              refine ⟨101806960310831550807528763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135742613747775401076705017 101806960310831550807528763)
              ·
                refine ⟨152710440466247326211293145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 101806960310831550807528763 152710440466247326211293145)
                ·
                  refine ⟨114532830349685494658469859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 152710440466247326211293145 114532830349685494658469859)
                  ·
                    refine ⟨171799245524528241987704789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 114532830349685494658469859 171799245524528241987704789)
                    ·
                      refine ⟨4026544816981130671586831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 171799245524528241987704789 4026544816981130671586831)
                      ·
                        rfl

theorem cell23_7841668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_7841668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841668 prefixEnd_7841668 := by exact prefixLift 7841668
  have htrace : WordTrace (prefixWord ++ tailWord_7841668) baseStart_7841668 baseEnd_7841668 := by
    simpa [prefixWord, tailWord_7841668, baseEnd_7841668] using wordTrace_append hprefix tailTrace_7841668
  have hstable : (prefixWord ++ tailWord_7841668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841668).length < 2 ^ (prefixWord ++ tailWord_7841668).sum := by decide
  have hdescent : baseEnd_7841668 < baseStart_7841668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841689 : List Nat := [1, 2, 1, 2, 1, 3, 5, 3, 1, 1, 3]
def baseStart_7841689 : Nat := 118140960795 + 7841689 * 2 ^ 59
def prefixEnd_7841689 : Nat := 4983230072969 + 3 ^ 40 * 7841689 * 2
def baseEnd_7841689 : Nat := 4026555600074875089424235

theorem tailTrace_7841689 : CollatzResearch.WordTrace tailWord_7841689 prefixEnd_7841689 4026555600074875089424235 := by
  unfold tailWord_7841689
  simp only [CollatzResearch.WordTrace]
  refine ⟨286009894487907481702864121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190673262991938321135242747 286009894487907481702864121)
  ·
    refine ⟨214507420865930611277148091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286009894487907481702864121 214507420865930611277148091)
    ·
      refine ⟨321761131298895916915722137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214507420865930611277148091 321761131298895916915722137)
      ·
        refine ⟨241320848474171937686791603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321761131298895916915722137 241320848474171937686791603)
        ·
          refine ⟨361981272711257906530187405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241320848474171937686791603 361981272711257906530187405)
          ·
            refine ⟨135742977266721714948820277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 361981272711257906530187405 135742977266721714948820277)
            ·
              refine ⟨12725904118755160776451901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 135742977266721714948820277 12725904118755160776451901)
              ·
                refine ⟨4772214044533185291169463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12725904118755160776451901 4772214044533185291169463)
                ·
                  refine ⟨7158321066799777936754195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772214044533185291169463 7158321066799777936754195)
                  ·
                    refine ⟨10737481600199666905131293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7158321066799777936754195 10737481600199666905131293)
                    ·
                      refine ⟨4026555600074875089424235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10737481600199666905131293 4026555600074875089424235)
                      ·
                        rfl

theorem cell23_7841689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 3, 1, 1, 3].length) (baseStart_7841689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841689 prefixEnd_7841689 := by exact prefixLift 7841689
  have htrace : WordTrace (prefixWord ++ tailWord_7841689) baseStart_7841689 baseEnd_7841689 := by
    simpa [prefixWord, tailWord_7841689, baseEnd_7841689] using wordTrace_append hprefix tailTrace_7841689
  have hstable : (prefixWord ++ tailWord_7841689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841689).length < 2 ^ (prefixWord ++ tailWord_7841689).sum := by decide
  have hdescent : baseEnd_7841689 < baseStart_7841689 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841692 : List Nat := [2, 2, 3, 3, 1, 1, 2, 3, 1, 5]
def baseStart_7841692 : Nat := 118140960795 + 7841692 * 2 ^ 59
def prefixEnd_7841692 : Nat := 4983230072969 + 3 ^ 40 * 7841692 * 2
def baseEnd_7841692 : Nat := 1342185713505612859228907

theorem tailTrace_7841692 : CollatzResearch.WordTrace tailWord_7841692 prefixEnd_7841692 1342185713505612859228907 := by
  unfold tailWord_7841692
  simp only [CollatzResearch.WordTrace]
  refine ⟨143005001953448306607611665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190673335937931075476815553 143005001953448306607611665)
  ·
    refine ⟨107253751465086229955708749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143005001953448306607611665 107253751465086229955708749)
    ·
      refine ⟨40220156799407336233390781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 107253751465086229955708749 40220156799407336233390781)
      ·
        refine ⟨15082558799777751087521543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40220156799407336233390781 15082558799777751087521543)
        ·
          refine ⟨22623838199666626631282315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15082558799777751087521543 22623838199666626631282315)
          ·
            refine ⟨33935757299499939946923473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22623838199666626631282315 33935757299499939946923473)
            ·
              refine ⟨25451817974624954960192605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33935757299499939946923473 25451817974624954960192605)
              ·
                refine ⟨9544431740484358110072227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 25451817974624954960192605 9544431740484358110072227)
                ·
                  refine ⟨14316647610726537165108341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9544431740484358110072227 14316647610726537165108341)
                  ·
                    refine ⟨1342185713505612859228907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14316647610726537165108341 1342185713505612859228907)
                    ·
                      rfl

theorem cell23_7841692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_7841692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841692 prefixEnd_7841692 := by exact prefixLift 7841692
  have htrace : WordTrace (prefixWord ++ tailWord_7841692) baseStart_7841692 baseEnd_7841692 := by
    simpa [prefixWord, tailWord_7841692, baseEnd_7841692] using wordTrace_append hprefix tailTrace_7841692
  have hstable : (prefixWord ++ tailWord_7841692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841692).length < 2 ^ (prefixWord ++ tailWord_7841692).sum := by decide
  have hdescent : baseEnd_7841692 < baseStart_7841692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841708 : List Nat := [2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 4]
def baseStart_7841708 : Nat := 118140960795 + 7841708 * 2 ^ 59
def prefixEnd_7841708 : Nat := 4983230072969 + 3 ^ 40 * 7841708 * 2
def baseEnd_7841708 : Nat := 4026565356207310515086647

theorem tailTrace_7841708 : CollatzResearch.WordTrace tailWord_7841708 prefixEnd_7841708 4026565356207310515086647 := by
  unfold tailWord_7841708
  simp only [CollatzResearch.WordTrace]
  refine ⟨143005293737419323973902889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190673724983225765298537185 143005293737419323973902889)
  ·
    refine ⟨107253970303064492980427167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 143005293737419323973902889 107253970303064492980427167)
    ·
      refine ⟨160880955454596739470640751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 107253970303064492980427167 160880955454596739470640751)
      ·
        refine ⟨241321433181895109205961127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160880955454596739470640751 241321433181895109205961127)
        ·
          refine ⟨361982149772842663808941691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 241321433181895109205961127 361982149772842663808941691)
          ·
            refine ⟨542973224659263995713412537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 361982149772842663808941691 542973224659263995713412537)
            ·
              refine ⟨407229918494447996785059403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542973224659263995713412537 407229918494447996785059403)
              ·
                refine ⟨610844877741671995177589105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407229918494447996785059403 610844877741671995177589105)
                ·
                  refine ⟨458133658306253996383191829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 610844877741671995177589105 458133658306253996383191829)
                  ·
                    refine ⟨21475015233105656080462117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 458133658306253996383191829 21475015233105656080462117)
                    ·
                      refine ⟨4026565356207310515086647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21475015233105656080462117 4026565356207310515086647)
                      ·
                        rfl

theorem cell23_7841708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 4].length) (baseStart_7841708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841708 prefixEnd_7841708 := by exact prefixLift 7841708
  have htrace : WordTrace (prefixWord ++ tailWord_7841708) baseStart_7841708 baseEnd_7841708 := by
    simpa [prefixWord, tailWord_7841708, baseEnd_7841708] using wordTrace_append hprefix tailTrace_7841708
  have hstable : (prefixWord ++ tailWord_7841708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841708).length < 2 ^ (prefixWord ++ tailWord_7841708).sum := by decide
  have hdescent : baseEnd_7841708 < baseStart_7841708 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841715 : List Nat := [1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 3]
def baseStart_7841715 : Nat := 118140960795 + 7841715 * 2 ^ 59
def prefixEnd_7841715 : Nat := 4983230072969 + 3 ^ 40 * 7841715 * 2
def baseEnd_7841715 : Nat := 4026568950571891987699115

theorem tailTrace_7841715 : CollatzResearch.WordTrace tailWord_7841715 prefixEnd_7841715 4026568950571891987699115 := by
  unfold tailWord_7841715
  simp only [CollatzResearch.WordTrace]
  refine ⟨286010842785813288143310599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190673895190542192095540399 286010842785813288143310599)
  ·
    refine ⟨429016264178719932214965899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286010842785813288143310599 429016264178719932214965899)
    ·
      refine ⟨643524396268079898322448849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429016264178719932214965899 643524396268079898322448849)
      ·
        refine ⟨482643297201059923741836637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 643524396268079898322448849 482643297201059923741836637)
        ·
          refine ⟨180991236450397471403188739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 482643297201059923741836637 180991236450397471403188739)
          ·
            refine ⟨271486854675596207104783109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 180991236450397471403188739 271486854675596207104783109)
            ·
              refine ⟨50903785251674288832146833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271486854675596207104783109 50903785251674288832146833)
              ·
                refine ⟨38177838938755716624110125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50903785251674288832146833 38177838938755716624110125)
                ·
                  refine ⟨14316689602033393734041297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 38177838938755716624110125 14316689602033393734041297)
                  ·
                    refine ⟨10737517201525045300530973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14316689602033393734041297 10737517201525045300530973)
                    ·
                      refine ⟨4026568950571891987699115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10737517201525045300530973 4026568950571891987699115)
                      ·
                        rfl

theorem cell23_7841715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 2, 3, 2, 3].length) (baseStart_7841715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841715 prefixEnd_7841715 := by exact prefixLift 7841715
  have htrace : WordTrace (prefixWord ++ tailWord_7841715) baseStart_7841715 baseEnd_7841715 := by
    simpa [prefixWord, tailWord_7841715, baseEnd_7841715] using wordTrace_append hprefix tailTrace_7841715
  have hstable : (prefixWord ++ tailWord_7841715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841715).length < 2 ^ (prefixWord ++ tailWord_7841715).sum := by decide
  have hdescent : baseEnd_7841715 < baseStart_7841715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841725 : List Nat := [1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 6]
def baseStart_7841725 : Nat := 118140960795 + 7841725 * 2 ^ 59
def prefixEnd_7841725 : Nat := 4983230072969 + 3 ^ 40 * 7841725 * 2
def baseEnd_7841725 : Nat := 4026574085378436948574069

theorem tailTrace_7841725 : CollatzResearch.WordTrace tailWord_7841725 prefixEnd_7841725 4026574085378436948574069 := by
  unfold tailWord_7841725
  simp only [CollatzResearch.WordTrace]
  refine ⟨286011207515777059851174629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190674138343851373234116419 286011207515777059851174629)
  ·
    refine ⟨53627101409208198722095243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 286011207515777059851174629 53627101409208198722095243)
    ·
      refine ⟨80440652113812298083142865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 53627101409208198722095243 80440652113812298083142865)
      ·
        refine ⟨60330489085359223562357149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 80440652113812298083142865 60330489085359223562357149)
        ·
          refine ⟨22623933407009708835883931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 60330489085359223562357149 22623933407009708835883931)
          ·
            refine ⟨33935900110514563253825897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22623933407009708835883931 33935900110514563253825897)
            ·
              refine ⟨25451925082885922440369423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 33935900110514563253825897 25451925082885922440369423)
              ·
                refine ⟨38177887624328883660554135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25451925082885922440369423 38177887624328883660554135)
                ·
                  refine ⟨57266831436493325490831203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38177887624328883660554135 57266831436493325490831203)
                  ·
                    refine ⟨85900247154739988236246805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 57266831436493325490831203 85900247154739988236246805)
                    ·
                      refine ⟨4026574085378436948574069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85900247154739988236246805 4026574085378436948574069)
                      ·
                        rfl

theorem cell23_7841725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 2, 1, 1, 1, 6].length) (baseStart_7841725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841725 prefixEnd_7841725 := by exact prefixLift 7841725
  have htrace : WordTrace (prefixWord ++ tailWord_7841725) baseStart_7841725 baseEnd_7841725 := by
    simpa [prefixWord, tailWord_7841725, baseEnd_7841725] using wordTrace_append hprefix tailTrace_7841725
  have hstable : (prefixWord ++ tailWord_7841725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841725).length < 2 ^ (prefixWord ++ tailWord_7841725).sum := by decide
  have hdescent : baseEnd_7841725 < baseStart_7841725 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841746 : List Nat := [3, 2, 2, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_7841746 : Nat := 118140960795 + 7841746 * 2 ^ 59
def prefixEnd_7841746 : Nat := 4983230072969 + 3 ^ 40 * 7841746 * 2
def baseEnd_7841746 : Nat := 4026584868472181366411473

theorem tailTrace_7841746 : CollatzResearch.WordTrace tailWord_7841746 prefixEnd_7841746 4026584868472181366411473 := by
  unfold tailWord_7841746
  simp only [CollatzResearch.WordTrace]
  refine ⟨71502993362175245109422273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190674648965800653625126061 71502993362175245109422273)
  ·
    refine ⟨53627245021631433832066705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 71502993362175245109422273 53627245021631433832066705)
    ·
      refine ⟨40220433766223575374050029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 53627245021631433832066705 40220433766223575374050029)
      ·
        refine ⟨15082662662333840765268761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 40220433766223575374050029 15082662662333840765268761)
        ·
          refine ⟨11311996996750380573951571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15082662662333840765268761 11311996996750380573951571)
          ·
            refine ⟨16967995495125570860927357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11311996996750380573951571 16967995495125570860927357)
            ·
              refine ⟨6362998310672089072847759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16967995495125570860927357 6362998310672089072847759)
              ·
                refine ⟨9544497466008133609271639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6362998310672089072847759 9544497466008133609271639)
                ·
                  refine ⟨14316746199012200413907459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9544497466008133609271639 14316746199012200413907459)
                  ·
                    refine ⟨21475119298518300620861189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14316746199012200413907459 21475119298518300620861189)
                    ·
                      refine ⟨4026584868472181366411473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21475119298518300620861189 4026584868472181366411473)
                      ·
                        rfl

theorem cell23_7841746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_7841746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841746 prefixEnd_7841746 := by exact prefixLift 7841746
  have htrace : WordTrace (prefixWord ++ tailWord_7841746) baseStart_7841746 baseEnd_7841746 := by
    simpa [prefixWord, tailWord_7841746, baseEnd_7841746] using wordTrace_append hprefix tailTrace_7841746
  have hstable : (prefixWord ++ tailWord_7841746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841746).length < 2 ^ (prefixWord ++ tailWord_7841746).sum := by decide
  have hdescent : baseEnd_7841746 < baseStart_7841746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841763 : List Nat := [1, 1, 1, 6, 1, 2, 4, 2, 1, 2, 2]
def baseStart_7841763 : Nat := 118140960795 + 7841763 * 2 ^ 59
def prefixEnd_7841763 : Nat := 4983230072969 + 3 ^ 40 * 7841763 * 2
def baseEnd_7841763 : Nat := 4026593597643307799898895

theorem tailTrace_7841763 : CollatzResearch.WordTrace tailWord_7841763 prefixEnd_7841763 4026593597643307799898895 := by
  unfold tailWord_7841763
  simp only [CollatzResearch.WordTrace]
  refine ⟨286012593489639392341057943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190675062326426261560705295 286012593489639392341057943)
  ·
    refine ⟨429018890234459088511586915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286012593489639392341057943 429018890234459088511586915)
    ·
      refine ⟨643528335351688632767380373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429018890234459088511586915 643528335351688632767380373)
      ·
        refine ⟨30165390719610404660970955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 643528335351688632767380373 30165390719610404660970955)
        ·
          refine ⟨45248086079415606991456433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30165390719610404660970955 45248086079415606991456433)
          ·
            refine ⟨33936064559561705243592325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 45248086079415606991456433 33936064559561705243592325)
            ·
              refine ⟨6363012104917819733173561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 33936064559561705243592325 6363012104917819733173561)
              ·
                refine ⟨4772259078688364799880171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6363012104917819733173561 4772259078688364799880171)
                ·
                  refine ⟨7158388618032547199820257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772259078688364799880171 7158388618032547199820257)
                  ·
                    refine ⟨5368791463524410399865193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7158388618032547199820257 5368791463524410399865193)
                    ·
                      refine ⟨4026593597643307799898895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368791463524410399865193 4026593597643307799898895)
                      ·
                        rfl

theorem cell23_7841763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_7841763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841763 prefixEnd_7841763 := by exact prefixLift 7841763
  have htrace : WordTrace (prefixWord ++ tailWord_7841763) baseStart_7841763 baseEnd_7841763 := by
    simpa [prefixWord, tailWord_7841763, baseEnd_7841763] using wordTrace_append hprefix tailTrace_7841763
  have hstable : (prefixWord ++ tailWord_7841763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841763).length < 2 ^ (prefixWord ++ tailWord_7841763).sum := by decide
  have hdescent : baseEnd_7841763 < baseStart_7841763 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841813 : List Nat := [1, 3, 2, 1, 6, 1, 1, 2, 2, 1, 3]
def baseStart_7841813 : Nat := 118140960795 + 7841813 * 2 ^ 59
def prefixEnd_7841813 : Nat := 4983230072969 + 3 ^ 40 * 7841813 * 2
def baseEnd_7841813 : Nat := 4026619271676032604273665

theorem tailTrace_7841813 : CollatzResearch.WordTrace tailWord_7841813 prefixEnd_7841813 4026619271676032604273665 := by
  unfold tailWord_7841813
  simp only [CollatzResearch.WordTrace]
  refine ⟨286014417139458250880378093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190676278092972167253585395 286014417139458250880378093)
  ·
    refine ⟨107255406427296844080141785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 286014417139458250880378093 107255406427296844080141785)
    ·
      refine ⟨80441554820472633060106339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 107255406427296844080141785 80441554820472633060106339)
      ·
        refine ⟨120662332230708949590159509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80441554820472633060106339 120662332230708949590159509)
        ·
          refine ⟨5656046823314482012038727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 120662332230708949590159509 5656046823314482012038727)
          ·
            refine ⟨8484070234971723018058091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5656046823314482012038727 8484070234971723018058091)
            ·
              refine ⟨12726105352457584527087137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8484070234971723018058091 12726105352457584527087137)
              ·
                refine ⟨9544579014343188395315353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12726105352457584527087137 9544579014343188395315353)
                ·
                  refine ⟨7158434260757391296486515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9544579014343188395315353 7158434260757391296486515)
                  ·
                    refine ⟨10737651391136086944729773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7158434260757391296486515 10737651391136086944729773)
                    ·
                      refine ⟨4026619271676032604273665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10737651391136086944729773 4026619271676032604273665)
                      ·
                        rfl

theorem cell23_7841813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 6, 1, 1, 2, 2, 1, 3].length) (baseStart_7841813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841813 prefixEnd_7841813 := by exact prefixLift 7841813
  have htrace : WordTrace (prefixWord ++ tailWord_7841813) baseStart_7841813 baseEnd_7841813 := by
    simpa [prefixWord, tailWord_7841813, baseEnd_7841813] using wordTrace_append hprefix tailTrace_7841813
  have hstable : (prefixWord ++ tailWord_7841813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841813).length < 2 ^ (prefixWord ++ tailWord_7841813).sum := by decide
  have hdescent : baseEnd_7841813 < baseStart_7841813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841819 : List Nat := [1, 1, 1, 1, 1, 1, 3, 8, 2, 2, 2]
def baseStart_7841819 : Nat := 118140960795 + 7841819 * 2 ^ 59
def prefixEnd_7841819 : Nat := 4983230072969 + 3 ^ 40 * 7841819 * 2
def baseEnd_7841819 : Nat := 4026622352559959580798637

theorem tailTrace_7841819 : CollatzResearch.WordTrace tailWord_7841819 prefixEnd_7841819 4026622352559959580798637 := by
  unfold tailWord_7841819
  simp only [CollatzResearch.WordTrace]
  refine ⟨286014635977436513905096511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190676423984957675936731007 286014635977436513905096511)
  ·
    refine ⟨429021953966154770857644767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286014635977436513905096511 429021953966154770857644767)
    ·
      refine ⟨643532930949232156286467151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429021953966154770857644767 643532930949232156286467151)
      ·
        refine ⟨965299396423848234429700727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643532930949232156286467151 965299396423848234429700727)
        ·
          refine ⟨1447949094635772351644551091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965299396423848234429700727 1447949094635772351644551091)
          ·
            refine ⟨2171923641953658527466826637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1447949094635772351644551091 2171923641953658527466826637)
            ·
              refine ⟨814471365732621947800059989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2171923641953658527466826637 814471365732621947800059989)
              ·
                refine ⟨9544586317179163450781953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 814471365732621947800059989 9544586317179163450781953)
                ·
                  refine ⟨7158439737884372588086465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9544586317179163450781953 7158439737884372588086465)
                  ·
                    refine ⟨5368829803413279441064849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7158439737884372588086465 5368829803413279441064849)
                    ·
                      refine ⟨4026622352559959580798637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368829803413279441064849 4026622352559959580798637)
                      ·
                        rfl

theorem cell23_7841819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2, 2, 2].length) (baseStart_7841819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841819 prefixEnd_7841819 := by exact prefixLift 7841819
  have htrace : WordTrace (prefixWord ++ tailWord_7841819) baseStart_7841819 baseEnd_7841819 := by
    simpa [prefixWord, tailWord_7841819, baseEnd_7841819] using wordTrace_append hprefix tailTrace_7841819
  have hstable : (prefixWord ++ tailWord_7841819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841819).length < 2 ^ (prefixWord ++ tailWord_7841819).sum := by decide
  have hdescent : baseEnd_7841819 < baseStart_7841819 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841835 : List Nat := [1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 3]
def baseStart_7841835 : Nat := 118140960795 + 7841835 * 2 ^ 59
def prefixEnd_7841835 : Nat := 4983230072969 + 3 ^ 40 * 7841835 * 2
def baseEnd_7841835 : Nat := 4026630568250431518198563

theorem tailTrace_7841835 : CollatzResearch.WordTrace tailWord_7841835 prefixEnd_7841835 4026630568250431518198563 := by
  unfold tailWord_7841835
  simp only [CollatzResearch.WordTrace]
  refine ⟨286015219545378548637678959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190676813030252365758452639 286015219545378548637678959)
  ·
    refine ⟨429022829318067822956518439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286015219545378548637678959 429022829318067822956518439)
    ·
      refine ⟨643534243977101734434777659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429022829318067822956518439 643534243977101734434777659)
      ·
        refine ⟨965301365965652601652166489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 643534243977101734434777659 965301365965652601652166489)
        ·
          refine ⟨723976024474239451239124867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965301365965652601652166489 723976024474239451239124867)
          ·
            refine ⟨1085964036711359176858687301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723976024474239451239124867 1085964036711359176858687301)
            ·
              refine ⟨203618256883379845661003869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1085964036711359176858687301 203618256883379845661003869)
              ·
                refine ⟨76356846331267442122876451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 203618256883379845661003869 76356846331267442122876451)
                ·
                  refine ⟨114535269496901163184314677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76356846331267442122876451 114535269496901163184314677)
                  ·
                    refine ⟨10737681515334484048529501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 114535269496901163184314677 10737681515334484048529501)
                    ·
                      refine ⟨4026630568250431518198563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10737681515334484048529501 4026630568250431518198563)
                      ·
                        rfl

theorem cell23_7841835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 5, 3].length) (baseStart_7841835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841835 prefixEnd_7841835 := by exact prefixLift 7841835
  have htrace : WordTrace (prefixWord ++ tailWord_7841835) baseStart_7841835 baseEnd_7841835 := by
    simpa [prefixWord, tailWord_7841835, baseEnd_7841835] using wordTrace_append hprefix tailTrace_7841835
  have hstable : (prefixWord ++ tailWord_7841835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841835).length < 2 ^ (prefixWord ++ tailWord_7841835).sum := by decide
  have hdescent : baseEnd_7841835 < baseStart_7841835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841855 : List Nat := [1, 1, 2, 2, 3, 1, 4, 1, 1, 7]
def baseStart_7841855 : Nat := 118140960795 + 7841855 * 2 ^ 59
def prefixEnd_7841855 : Nat := 4983230072969 + 3 ^ 40 * 7841855 * 2
def baseEnd_7841855 : Nat := 1342213612621173813316157

theorem tailTrace_7841855 : CollatzResearch.WordTrace tailWord_7841855 prefixEnd_7841855 1342213612621173813316157 := by
  unfold tailWord_7841855
  simp only [CollatzResearch.WordTrace]
  refine ⟨286015949005306092053407019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190677299336870728035604679 286015949005306092053407019)
  ·
    refine ⟨429023923507959138080110529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286015949005306092053407019 429023923507959138080110529)
    ·
      refine ⟨321767942630969353560082897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 429023923507959138080110529 321767942630969353560082897)
      ·
        refine ⟨241325956973227015170062173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321767942630969353560082897 241325956973227015170062173)
        ·
          refine ⟨90497233864960130688773315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241325956973227015170062173 90497233864960130688773315)
          ·
            refine ⟨135745850797440196033159973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90497233864960130688773315 135745850797440196033159973)
            ·
              refine ⟨25452347024520036756217495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 135745850797440196033159973 25452347024520036756217495)
              ·
                refine ⟨38178520536780055134326243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25452347024520036756217495 38178520536780055134326243)
                ·
                  refine ⟨57267780805170082701489365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38178520536780055134326243 57267780805170082701489365)
                  ·
                    refine ⟨1342213612621173813316157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 57267780805170082701489365 1342213612621173813316157)
                    ·
                      rfl

theorem cell23_7841855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 7].length) (baseStart_7841855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841855 prefixEnd_7841855 := by exact prefixLift 7841855
  have htrace : WordTrace (prefixWord ++ tailWord_7841855) baseStart_7841855 baseEnd_7841855 := by
    simpa [prefixWord, tailWord_7841855, baseEnd_7841855] using wordTrace_append hprefix tailTrace_7841855
  have hstable : (prefixWord ++ tailWord_7841855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841855).length < 2 ^ (prefixWord ++ tailWord_7841855).sum := by decide
  have hdescent : baseEnd_7841855 < baseStart_7841855 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841865 : List Nat := [1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 5]
def baseStart_7841865 : Nat := 118140960795 + 7841865 * 2 ^ 59
def prefixEnd_7841865 : Nat := 4983230072969 + 3 ^ 40 * 7841865 * 2
def baseEnd_7841865 : Nat := 4026645972670066400823425

theorem tailTrace_7841865 : CollatzResearch.WordTrace tailWord_7841865 prefixEnd_7841865 4026645972670066400823425 := by
  unfold tailWord_7841865
  simp only [CollatzResearch.WordTrace]
  refine ⟨286016313735269863761271049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190677542490179909174180699 286016313735269863761271049)
  ·
    refine ⟨214512235301452397820953287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286016313735269863761271049 214512235301452397820953287)
    ·
      refine ⟨321768352952178596731429931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214512235301452397820953287 321768352952178596731429931)
      ·
        refine ⟨482652529428267895097144897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321768352952178596731429931 482652529428267895097144897)
        ·
          refine ⟨361989397071200921322858673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482652529428267895097144897 361989397071200921322858673)
          ·
            refine ⟨271492047803400690992144005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 361989397071200921322858673 271492047803400690992144005)
            ·
              refine ⟨50904758963137629561027001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 271492047803400690992144005 50904758963137629561027001)
              ·
                refine ⟨38178569222353222170770251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 50904758963137629561027001 38178569222353222170770251)
                ·
                  refine ⟨57267853833529833256155377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 38178569222353222170770251 57267853833529833256155377)
                  ·
                    refine ⟨42950890375147374942116533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 57267853833529833256155377 42950890375147374942116533)
                    ·
                      refine ⟨4026645972670066400823425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42950890375147374942116533 4026645972670066400823425)
                      ·
                        rfl

theorem cell23_7841865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 2, 5].length) (baseStart_7841865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841865 prefixEnd_7841865 := by exact prefixLift 7841865
  have htrace : WordTrace (prefixWord ++ tailWord_7841865) baseStart_7841865 baseEnd_7841865 := by
    simpa [prefixWord, tailWord_7841865, baseEnd_7841865] using wordTrace_append hprefix tailTrace_7841865
  have hstable : (prefixWord ++ tailWord_7841865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841865).length < 2 ^ (prefixWord ++ tailWord_7841865).sum := by decide
  have hdescent : baseEnd_7841865 < baseStart_7841865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7841986 : List Nat := [3, 5, 1, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_7841986 : Nat := 118140960795 + 7841986 * 2 ^ 59
def prefixEnd_7841986 : Nat := 4983230072969 + 3 ^ 40 * 7841986 * 2
def baseEnd_7841986 : Nat := 4026708103829260427410369

theorem tailTrace_7841986 : CollatzResearch.WordTrace tailWord_7841986 prefixEnd_7841986 4026708103829260427410369 := by
  unfold tailWord_7841986
  simp only [CollatzResearch.WordTrace]
  refine ⟨71505181741957875356606453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190680484645221000950950541 71505181741957875356606453)
  ·
    refine ⟨6703610788308550814681855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 71505181741957875356606453 6703610788308550814681855)
    ·
      refine ⟨10055416182462826222022783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6703610788308550814681855 10055416182462826222022783)
      ·
        refine ⟨15083124273694239333034175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10055416182462826222022783 15083124273694239333034175)
        ·
          refine ⟨22624686410541358999551263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15083124273694239333034175 22624686410541358999551263)
          ·
            refine ⟨33937029615812038499326895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22624686410541358999551263 33937029615812038499326895)
            ·
              refine ⟨50905544423718057748990343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 33937029615812038499326895 50905544423718057748990343)
              ·
                refine ⟨76358316635577086623485515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 50905544423718057748990343 76358316635577086623485515)
                ·
                  refine ⟨114537474953365629935228273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 76358316635577086623485515 114537474953365629935228273)
                  ·
                    refine ⟨85903106215024222451421205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 114537474953365629935228273 85903106215024222451421205)
                    ·
                      refine ⟨4026708103829260427410369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 85903106215024222451421205 4026708103829260427410369)
                      ·
                        rfl

theorem cell23_7841986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_7841986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7841986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7841986 prefixEnd_7841986 := by exact prefixLift 7841986
  have htrace : WordTrace (prefixWord ++ tailWord_7841986) baseStart_7841986 baseEnd_7841986 := by
    simpa [prefixWord, tailWord_7841986, baseEnd_7841986] using wordTrace_append hprefix tailTrace_7841986
  have hstable : (prefixWord ++ tailWord_7841986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7841986).length < 2 ^ (prefixWord ++ tailWord_7841986).sum := by decide
  have hdescent : baseEnd_7841986 < baseStart_7841986 := by decide
  rcases family_descends (prefixWord ++ tailWord_7841986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842009 : List Nat := [1, 2, 1, 2, 3, 1, 2, 5, 2, 4]
def baseStart_7842009 : Nat := 118140960795 + 7842009 * 2 ^ 59
def prefixEnd_7842009 : Nat := 4983230072969 + 3 ^ 40 * 7842009 * 2
def baseEnd_7842009 : Nat := 1342239971294771279140921

theorem tailTrace_7842009 : CollatzResearch.WordTrace tailWord_7842009 prefixEnd_7842009 1342239971294771279140921 := by
  unfold tailWord_7842009
  simp only [CollatzResearch.WordTrace]
  refine ⟨286021565846748176354513081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190681043897832117569675387 286021565846748176354513081)
  ·
    refine ⟨214516174385061132265884811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286021565846748176354513081 214516174385061132265884811)
    ·
      refine ⟨321774261577591698398827217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214516174385061132265884811 321774261577591698398827217)
      ·
        refine ⟨241330696183193773799120413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 321774261577591698398827217 241330696183193773799120413)
        ·
          refine ⟨90499011068697665174670155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 241330696183193773799120413 90499011068697665174670155)
          ·
            refine ⟨135748516603046497762005233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 90499011068697665174670155 135748516603046497762005233)
            ·
              refine ⟨101811387452284873321503925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 135748516603046497762005233 101811387452284873321503925)
              ·
                refine ⟨9544817573651706873890993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 101811387452284873321503925 9544817573651706873890993)
                ·
                  refine ⟨7158613180238780155418245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9544817573651706873890993 7158613180238780155418245)
                  ·
                    refine ⟨1342239971294771279140921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7158613180238780155418245 1342239971294771279140921)
                    ·
                      rfl

theorem cell23_7842009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 5, 2, 4].length) (baseStart_7842009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842009 prefixEnd_7842009 := by exact prefixLift 7842009
  have htrace : WordTrace (prefixWord ++ tailWord_7842009) baseStart_7842009 baseEnd_7842009 := by
    simpa [prefixWord, tailWord_7842009, baseEnd_7842009] using wordTrace_append hprefix tailTrace_7842009
  have hstable : (prefixWord ++ tailWord_7842009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842009).length < 2 ^ (prefixWord ++ tailWord_7842009).sum := by decide
  have hdescent : baseEnd_7842009 < baseStart_7842009 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842016 : List Nat := [2, 1, 1, 3, 1, 3, 1, 4, 3, 2, 2]
def baseStart_7842016 : Nat := 118140960795 + 7842016 * 2 ^ 59
def prefixEnd_7842016 : Nat := 4983230072969 + 3 ^ 40 * 7842016 * 2
def baseEnd_7842016 : Nat := 4026723508248895310035231

theorem tailTrace_7842016 : CollatzResearch.WordTrace tailWord_7842016 prefixEnd_7842016 4026723508248895310035231 := by
  unfold tailWord_7842016
  simp only [CollatzResearch.WordTrace]
  refine ⟨143010910578861408275008951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190681214105148544366678601 143010910578861408275008951)
  ·
    refine ⟨214516365868292112412513427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 143010910578861408275008951 214516365868292112412513427)
    ·
      refine ⟨321774548802438168618770141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 214516365868292112412513427 321774548802438168618770141)
      ·
        refine ⟨120665455800914313232038803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 321774548802438168618770141 120665455800914313232038803)
        ·
          refine ⟨180998183701371469848058205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 120665455800914313232038803 180998183701371469848058205)
          ·
            refine ⟨67874318888014301193021827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 180998183701371469848058205 67874318888014301193021827)
            ·
              refine ⟨101811478332021451789532741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67874318888014301193021827 101811478332021451789532741)
              ·
                refine ⟨19089652187254022210537389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101811478332021451789532741 19089652187254022210537389)
                ·
                  refine ⟨7158619570220258328951521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19089652187254022210537389 7158619570220258328951521)
                  ·
                    refine ⟨5368964677665193746713641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7158619570220258328951521 5368964677665193746713641)
                    ·
                      refine ⟨4026723508248895310035231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368964677665193746713641 4026723508248895310035231)
                      ·
                        rfl

theorem cell23_7842016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 4, 3, 2, 2].length) (baseStart_7842016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842016 prefixEnd_7842016 := by exact prefixLift 7842016
  have htrace : WordTrace (prefixWord ++ tailWord_7842016) baseStart_7842016 baseEnd_7842016 := by
    simpa [prefixWord, tailWord_7842016, baseEnd_7842016] using wordTrace_append hprefix tailTrace_7842016
  have hstable : (prefixWord ++ tailWord_7842016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842016).length < 2 ^ (prefixWord ++ tailWord_7842016).sum := by decide
  have hdescent : baseEnd_7842016 < baseStart_7842016 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842050 : List Nat := [3, 4, 1, 1, 2, 1, 3, 1, 3, 2, 2]
def baseStart_7842050 : Nat := 118140960795 + 7842050 * 2 ^ 59
def prefixEnd_7842050 : Nat := 4983230072969 + 3 ^ 40 * 7842050 * 2
def baseEnd_7842050 : Nat := 4026740966591148177010075

theorem tailTrace_7842050 : CollatzResearch.WordTrace tailWord_7842050 prefixEnd_7842050 4026740966591148177010075 := by
  unfold tailWord_7842050
  simp only [CollatzResearch.WordTrace]
  refine ⟨71505765309899910089188901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190682040826399760237837069 71505765309899910089188901)
  ·
    refine ⟨13407330995606233141722919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 71505765309899910089188901 13407330995606233141722919)
    ·
      refine ⟨20110996493409349712584379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13407330995606233141722919 20110996493409349712584379)
      ·
        refine ⟨30166494740114024568876569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20110996493409349712584379 30166494740114024568876569)
        ·
          refine ⟨22624871055085518426657427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30166494740114024568876569 22624871055085518426657427)
          ·
            refine ⟨33937306582628277639986141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 22624871055085518426657427 33937306582628277639986141)
            ·
              refine ⟨12726489968485604114994803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 33937306582628277639986141 12726489968485604114994803)
              ·
                refine ⟨19089734952728406172492205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12726489968485604114994803 19089734952728406172492205)
                ·
                  refine ⟨7158650607273152314684577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19089734952728406172492205 7158650607273152314684577)
                  ·
                    refine ⟨5368987955454864236013433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7158650607273152314684577 5368987955454864236013433)
                    ·
                      refine ⟨4026740966591148177010075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5368987955454864236013433 4026740966591148177010075)
                      ·
                        rfl

theorem cell23_7842050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 3, 1, 3, 2, 2].length) (baseStart_7842050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842050 prefixEnd_7842050 := by exact prefixLift 7842050
  have htrace : WordTrace (prefixWord ++ tailWord_7842050) baseStart_7842050 baseEnd_7842050 := by
    simpa [prefixWord, tailWord_7842050, baseEnd_7842050] using wordTrace_append hprefix tailTrace_7842050
  have hstable : (prefixWord ++ tailWord_7842050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842050).length < 2 ^ (prefixWord ++ tailWord_7842050).sum := by decide
  have hdescent : baseEnd_7842050 < baseStart_7842050 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842087 : List Nat := [1, 1, 8, 1, 2, 1, 1, 1, 1, 1, 5]
def baseStart_7842087 : Nat := 118140960795 + 7842087 * 2 ^ 59
def prefixEnd_7842087 : Nat := 4983230072969 + 3 ^ 40 * 7842087 * 2
def baseEnd_7842087 : Nat := 4026759965375364532247405

theorem tailTrace_7842087 : CollatzResearch.WordTrace tailWord_7842087 prefixEnd_7842087 4026759965375364532247405 := by
  unfold tailWord_7842087
  simp only [CollatzResearch.WordTrace]
  refine ⟨286024410740465595675852515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190682940493643730450568343 286024410740465595675852515)
  ·
    refine ⟨429036616110698393513778773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286024410740465595675852515 429036616110698393513778773)
    ·
      refine ⟨5027772845047246798989595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 429036616110698393513778773 5027772845047246798989595)
      ·
        refine ⟨7541659267570870198484393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5027772845047246798989595 7541659267570870198484393)
        ·
          refine ⟨5656244450678152648863295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7541659267570870198484393 5656244450678152648863295)
          ·
            refine ⟨8484366676017228973294943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5656244450678152648863295 8484366676017228973294943)
            ·
              refine ⟨12726550014025843459942415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8484366676017228973294943 12726550014025843459942415)
              ·
                refine ⟨19089825021038765189913623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12726550014025843459942415 19089825021038765189913623)
                ·
                  refine ⟨28634737531558147784870435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19089825021038765189913623 28634737531558147784870435)
                  ·
                    refine ⟨42952106297337221677305653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 28634737531558147784870435 42952106297337221677305653)
                    ·
                      refine ⟨4026759965375364532247405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 42952106297337221677305653 4026759965375364532247405)
                      ·
                        rfl

theorem cell23_7842087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 2, 1, 1, 1, 1, 1, 5].length) (baseStart_7842087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842087 prefixEnd_7842087 := by exact prefixLift 7842087
  have htrace : WordTrace (prefixWord ++ tailWord_7842087) baseStart_7842087 baseEnd_7842087 := by
    simpa [prefixWord, tailWord_7842087, baseEnd_7842087] using wordTrace_append hprefix tailTrace_7842087
  have hstable : (prefixWord ++ tailWord_7842087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842087).length < 2 ^ (prefixWord ++ tailWord_7842087).sum := by decide
  have hdescent : baseEnd_7842087 < baseStart_7842087 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842100 : List Nat := [2, 5, 1, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_7842100 : Nat := 118140960795 + 7842100 * 2 ^ 59
def prefixEnd_7842100 : Nat := 4983230072969 + 3 ^ 40 * 7842100 * 2
def baseEnd_7842100 : Nat := 4026766640623872981384845

theorem tailTrace_7842100 : CollatzResearch.WordTrace tailWord_7842100 prefixEnd_7842100 4026766640623872981384845 := by
  unfold tailWord_7842100
  simp only [CollatzResearch.WordTrace]
  refine ⟨143012442444709249448037877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 190683256592945665930717169 143012442444709249448037877)
  ·
    refine ⟨13407416479191492135753551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 143012442444709249448037877 13407416479191492135753551)
    ·
      refine ⟨20111124718787238203630327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13407416479191492135753551 20111124718787238203630327)
      ·
        refine ⟨30166687078180857305445491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20111124718787238203630327 30166687078180857305445491)
        ·
          refine ⟨45250030617271285958168237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30166687078180857305445491 45250030617271285958168237)
          ·
            refine ⟨16968761481476732234313089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45250030617271285958168237 16968761481476732234313089)
            ·
              refine ⟨12726571111107549175734817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16968761481476732234313089 12726571111107549175734817)
              ·
                refine ⟨9544928333330661881801113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12726571111107549175734817 9544928333330661881801113)
                ·
                  refine ⟨7158696249997996411350835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9544928333330661881801113 7158696249997996411350835)
                  ·
                    refine ⟨10738044374996994617026253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7158696249997996411350835 10738044374996994617026253)
                    ·
                      refine ⟨4026766640623872981384845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 10738044374996994617026253 4026766640623872981384845)
                      ·
                        rfl

theorem cell23_7842100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_7842100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842100 prefixEnd_7842100 := by exact prefixLift 7842100
  have htrace : WordTrace (prefixWord ++ tailWord_7842100) baseStart_7842100 baseEnd_7842100 := by
    simpa [prefixWord, tailWord_7842100, baseEnd_7842100] using wordTrace_append hprefix tailTrace_7842100
  have hstable : (prefixWord ++ tailWord_7842100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842100).length < 2 ^ (prefixWord ++ tailWord_7842100).sum := by decide
  have hdescent : baseEnd_7842100 < baseStart_7842100 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842119 : List Nat := [1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_7842119 : Nat := 118140960795 + 7842119 * 2 ^ 59
def prefixEnd_7842119 : Nat := 4983230072969 + 3 ^ 40 * 7842119 * 2
def baseEnd_7842119 : Nat := 4026776396756308407047257

theorem tailTrace_7842119 : CollatzResearch.WordTrace tailWord_7842119 prefixEnd_7842119 4026776396756308407047257 := by
  unfold tailWord_7842119
  simp only [CollatzResearch.WordTrace]
  refine ⟨286025577876349665141017411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190683718584233110094011607 286025577876349665141017411)
  ·
    refine ⟨429038366814524497711526117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 286025577876349665141017411 429038366814524497711526117)
    ·
      refine ⟨80444693777723343320911147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 429038366814524497711526117 80444693777723343320911147)
      ·
        refine ⟨120667040666585014981366721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80444693777723343320911147 120667040666585014981366721)
        ·
          refine ⟨90500280499938761236025041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120667040666585014981366721 90500280499938761236025041)
          ·
            refine ⟨67875210374954070927018781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90500280499938761236025041 67875210374954070927018781)
            ·
              refine ⟨25453203890607776597632043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 67875210374954070927018781 25453203890607776597632043)
              ·
                refine ⟨38179805835911664896448065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 25453203890607776597632043 38179805835911664896448065)
                ·
                  refine ⟨28634854376933748672336049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 38179805835911664896448065 28634854376933748672336049)
                  ·
                    refine ⟨21476140782700311504252037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 28634854376933748672336049 21476140782700311504252037)
                    ·
                      refine ⟨4026776396756308407047257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 21476140782700311504252037 4026776396756308407047257)
                      ·
                        rfl

theorem cell23_7842119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_7842119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842119 prefixEnd_7842119 := by exact prefixLift 7842119
  have htrace : WordTrace (prefixWord ++ tailWord_7842119) baseStart_7842119 baseEnd_7842119 := by
    simpa [prefixWord, tailWord_7842119, baseEnd_7842119] using wordTrace_append hprefix tailTrace_7842119
  have hstable : (prefixWord ++ tailWord_7842119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842119).length < 2 ^ (prefixWord ++ tailWord_7842119).sum := by decide
  have hdescent : baseEnd_7842119 < baseStart_7842119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842129 : List Nat := [1, 2, 2, 1, 4, 3, 1, 2, 7]
def baseStart_7842129 : Nat := 118140960795 + 7842129 * 2 ^ 59
def prefixEnd_7842129 : Nat := 4983230072969 + 3 ^ 40 * 7842129 * 2
def baseEnd_7842129 : Nat := 447420170173650374213579

theorem tailTrace_7842129 : CollatzResearch.WordTrace tailWord_7842129 prefixEnd_7842129 447420170173650374213579 := by
  unfold tailWord_7842129
  simp only [CollatzResearch.WordTrace]
  refine ⟨286025942606313436848881441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190683961737542291232587627 286025942606313436848881441)
  ·
    refine ⟨214519456954735077636661081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286025942606313436848881441 214519456954735077636661081)
    ·
      refine ⟨160889592716051308227495811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 214519456954735077636661081 160889592716051308227495811)
      ·
        refine ⟨241334389074076962341243717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 160889592716051308227495811 241334389074076962341243717)
        ·
          refine ⟨45250197951389430438983197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 241334389074076962341243717 45250197951389430438983197)
          ·
            refine ⟨16968824231771036414618699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 45250197951389430438983197 16968824231771036414618699)
            ·
              refine ⟨25453236347656554621928049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16968824231771036414618699 25453236347656554621928049)
              ·
                refine ⟨19089927260742415966446037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 25453236347656554621928049 19089927260742415966446037)
                ·
                  refine ⟨447420170173650374213579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19089927260742415966446037 447420170173650374213579)
                  ·
                    rfl

theorem cell23_7842129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 2, 7].length) (baseStart_7842129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842129 prefixEnd_7842129 := by exact prefixLift 7842129
  have htrace : WordTrace (prefixWord ++ tailWord_7842129) baseStart_7842129 baseEnd_7842129 := by
    simpa [prefixWord, tailWord_7842129, baseEnd_7842129] using wordTrace_append hprefix tailTrace_7842129
  have hstable : (prefixWord ++ tailWord_7842129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842129).length < 2 ^ (prefixWord ++ tailWord_7842129).sum := by decide
  have hdescent : baseEnd_7842129 < baseStart_7842129 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842273 : List Nat := [1, 2, 3, 1, 2, 2, 1, 4, 2, 3, 2]
def baseStart_7842273 : Nat := 118140960795 + 7842273 * 2 ^ 59
def prefixEnd_7842273 : Nat := 4983230072969 + 3 ^ 40 * 7842273 * 2
def baseEnd_7842273 : Nat := 4026855472777100804521549

theorem tailTrace_7842273 : CollatzResearch.WordTrace tailWord_7842273 prefixEnd_7842273 4026855472777100804521549 := by
  unfold tailWord_7842273
  simp only [CollatzResearch.WordTrace]
  refine ⟨286031194717791749442123473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 190687463145194499628082315 286031194717791749442123473)
  ·
    refine ⟨214523396038343812081592605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 286031194717791749442123473 214523396038343812081592605)
    ·
      refine ⟨80446273514378929530597227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 214523396038343812081592605 80446273514378929530597227)
      ·
        refine ⟨120669410271568394295895841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 80446273514378929530597227 120669410271568394295895841)
        ·
          refine ⟨90502057703676295721921881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 120669410271568394295895841 90502057703676295721921881)
          ·
            refine ⟨67876543277757221791441411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 90502057703676295721921881 67876543277757221791441411)
            ·
              refine ⟨101814814916635832687162117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 67876543277757221791441411 101814814916635832687162117)
              ·
                refine ⟨19090277796869218628842897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 101814814916635832687162117 19090277796869218628842897)
                ·
                  refine ⟨14317708347651913971632173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19090277796869218628842897 14317708347651913971632173)
                  ·
                    refine ⟨5369140630369467739362065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14317708347651913971632173 5369140630369467739362065)
                    ·
                      refine ⟨4026855472777100804521549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5369140630369467739362065 4026855472777100804521549)
                      ·
                        rfl

theorem cell23_7842273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 3, 2].length) (baseStart_7842273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842273 prefixEnd_7842273 := by exact prefixLift 7842273
  have htrace : WordTrace (prefixWord ++ tailWord_7842273) baseStart_7842273 baseEnd_7842273 := by
    simpa [prefixWord, tailWord_7842273, baseEnd_7842273] using wordTrace_append hprefix tailTrace_7842273
  have hstable : (prefixWord ++ tailWord_7842273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842273).length < 2 ^ (prefixWord ++ tailWord_7842273).sum := by decide
  have hdescent : baseEnd_7842273 < baseStart_7842273 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7842274 : List Nat := [3, 3, 3, 2, 1, 1, 1, 4, 1, 4]
def baseStart_7842274 : Nat := 118140960795 + 7842274 * 2 ^ 59
def prefixEnd_7842274 : Nat := 4983230072969 + 3 ^ 40 * 7842274 * 2
def baseEnd_7842274 : Nat := 1342285328752585100203015

theorem tailTrace_7842274 : CollatzResearch.WordTrace tailWord_7842274 prefixEnd_7842274 1342285328752585100203015 := by
  unfold tailWord_7842274
  simp only [CollatzResearch.WordTrace]
  refine ⟨71507807797697031653227469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 190687487460525417741939917 71507807797697031653227469)
  ·
    refine ⟨26815427924136386869960301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 71507807797697031653227469 26815427924136386869960301)
    ·
      refine ⟨10055785471551145076235113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 26815427924136386869960301 10055785471551145076235113)
      ·
        refine ⟨7541839103663358807176335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10055785471551145076235113 7541839103663358807176335)
        ·
          refine ⟨11312758655495038210764503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7541839103663358807176335 11312758655495038210764503)
          ·
            refine ⟨16969137983242557316146755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11312758655495038210764503 16969137983242557316146755)
            ·
              refine ⟨25453706974863835974220133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16969137983242557316146755 25453706974863835974220133)
              ·
                refine ⟨4772570057786969245166275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 25453706974863835974220133 4772570057786969245166275)
                ·
                  refine ⟨7158855086680453867749413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4772570057786969245166275 7158855086680453867749413)
                  ·
                    refine ⟨1342285328752585100203015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7158855086680453867749413 1342285328752585100203015)
                    ·
                      rfl

theorem cell23_7842274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 4, 1, 4].length) (baseStart_7842274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7842274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7842274 prefixEnd_7842274 := by exact prefixLift 7842274
  have htrace : WordTrace (prefixWord ++ tailWord_7842274) baseStart_7842274 baseEnd_7842274 := by
    simpa [prefixWord, tailWord_7842274, baseEnd_7842274] using wordTrace_append hprefix tailTrace_7842274
  have hstable : (prefixWord ++ tailWord_7842274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7842274).length < 2 ^ (prefixWord ++ tailWord_7842274).sum := by decide
  have hdescent : baseEnd_7842274 < baseStart_7842274 := by decide
  rcases family_descends (prefixWord ++ tailWord_7842274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
